import os, re, sys, tempfile, json
from src.prompt.prompt import PromptSwitcher
from transformers import AutoModelForCausalLM, AutoTokenizer
from openai import OpenAI
from src.utils.rustc import Rustc
from src.utils.error import TranslationError


class SliceTranslator:
    def __init__(self):
        self.prompter = PromptSwitcher()
        pass

    def is_slice_function(self, slice_type):
        return slice_type == "Function" or slice_type == "Undefined Function"

    def is_slice_type(self, slice_type):
        return slice_type == "Type"

    def is_slice_global_var(self, slice_type):
        return slice_type == "Global Variable"

    def is_macro_definition(self, slice_type):
        return slice_type == "Macro"

    def get_prompt(self, slice_tuple, context=None):
        """
        slice_tuple: (c_code, slice_type)
        context: rust context for the translation
        """
        if self.is_slice_function(slice_tuple[1]):
            prompt = self.prompter.function_prompt(slice_tuple[0], context=context)
        elif self.is_slice_type(slice_tuple[1]):
            prompt = self.prompter.datatype_prompt(slice_tuple[0], context=context)
        elif self.is_slice_global_var(slice_tuple[1]):
            prompt = self.prompter.variable_prompt(slice_tuple[0], context=context)
        elif self.is_macro_definition(slice_tuple[1]):
            prompt = self.prompter.macro_prompt(slice_tuple[0], context=context)
        else:
            raise ValueError(
                f"Unknown slice type: {slice_tuple[1]}\nSlice content:\n{slice_tuple[0]}"
            )
        return prompt

    def extract_code_block(self, llm_output):
        pattern = re.compile(r"```(?:rust)?\n((?:.|\n)*?)\n?```", re.DOTALL)
        try:
            match = pattern.search(llm_output)
        except Exception:
            raise ValueError(
                "The selected LLM failed to produce a valid output containing the Rust code. This may be due to the model's limited capability in generating structured responses.\nPlease try using a more capable LLM or review your parameter settings."
            )
        if not match:
            return llm_output

        code_block = match.group(1).strip()
        return code_block if code_block else "\n"

    def translate_slice(self, slice_tuple, file_context, context=None, **kwargs):
        """
        Returns: (rust_code: str, is_first_time_success: bool)
        """
        prompt = self.get_prompt(slice_tuple, context=context)
        api_key = kwargs.get("api_key")
        model_name = kwargs.get("model_name", "gpt-4")
        temperature = kwargs.get("temperature", 0.2)
        max_tokens = kwargs.get("max_tokens", 2048)
        top_p = kwargs.get("top_p", 0.7)
        base_url = kwargs.get("base_url", None)
        repair_round_threshold = kwargs.get("repair_round_threshold", 3)

        system_prompt = "You are an expert in code translation, responsible for translating C programs into Rust programs."

        if base_url:
            client = OpenAI(base_url=base_url, api_key=api_key)
        else:
            client = OpenAI(api_key=api_key)

        completion = client.chat.completions.create(
            model=model_name,
            messages=[
                {"role": "system", "content": system_prompt},
                {"role": "user", "content": prompt},
            ],
            temperature=temperature,
            top_p=top_p,
            max_tokens=max_tokens,
            stream=True,
        )

        response = ""
        for chunk in completion:
            delta = chunk.choices[0].delta
            if delta.content:
                response += delta.content

        response = self.extract_code_block(response)

        code_to_compile = file_context + "\n\n" + response
        with tempfile.NamedTemporaryFile(
            mode="w+", suffix=".rs", delete=True
        ) as temp_rust_file:
            temp_rust_file.write(code_to_compile)
            temp_rust_file_path = temp_rust_file.name
            result, msg = Rustc().execute(temp_rust_file_path)
        if result == True:
            return response, True

        for i in range(0, repair_round_threshold):
            repair_prompt = repair_prompt(slice_tuple[0], response, msg)
            completion = client.chat.completions.create(
                model=model_name,
                messages=[
                    {"role": "user", "content": repair_prompt},
                ],
                temperature=temperature,
                top_p=top_p,
                max_tokens=max_tokens,
                stream=True,
            )

            repaired_response = ""
            for chunk in completion:
                delta = chunk.choices[0].delta
                if delta.content:
                    repaired_response += delta.content

            repaired_response = self.extract_code_block(repaired_response)

            code_to_compile = file_context + "\n\n" + repaired_response
            with tempfile.NamedTemporaryFile(
                mode="w+", suffix=".rs", delete=True
            ) as temp_rust_file:
                temp_rust_file.write(code_to_compile)
                temp_rust_file_path = temp_rust_file.name
                result, msg = Rustc().execute(temp_rust_file_path)
            if result == True:
                return repaired_response, False
            else:
                response = repaired_response
                continue

        raise TranslationError(
            f"Failed to translate slice after {repair_round_threshold} repair attempts.\nLast error message from Rust compiler:\n{msg}"
        )
