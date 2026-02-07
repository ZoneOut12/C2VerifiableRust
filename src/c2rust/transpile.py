from transformers import AutoModelForCausalLM, AutoTokenizer
from openai import OpenAI
import os, re, sys, tempfile, json
from src.prompt.prompt import transpile_prompt, repair_prompt, transpile_prompt_v2
from src.spec.extract import SpecExtractor
from src.utils.formatter import ClangFormatter
from src.utils.rustc import Rustc
from src.utils.logger import DummyLogger
from src.c2rust.skeleton import SkeletonGenerator


class Transpiler:
    def __init__(self, model, logger):
        """
        Initializes the Transpiler class with the given configuration and log file.
        model: The model name or path to the LLM.
        logger: A logger instance specific to the given log file.
        """
        self.logger = logger
        self.model = None
        self.model_name = None
        self.tokenizer = None
        if model.strip():
            self.model_name = model
            self.model = AutoModelForCausalLM.from_pretrained(
                self.model_name,
                torch_dtype="auto",
                device_map="auto",
                trust_remote_code=True,
            )
            self.tokenizer = AutoTokenizer.from_pretrained(self.model_name)

    def openai_transpile(self, file_path: str, prompt: str, **kwargs):
        api_key = kwargs.get("api_key")
        model_name = kwargs.get("model_name", "gpt-4")
        temperature = kwargs.get("temperature", 0.2)
        max_tokens = kwargs.get("max_tokens", 2048)
        top_p = kwargs.get("top_p", 0.7)
        base_url = kwargs.get("base_url", None)

        source_code = ""
        with open(file_path, "r", encoding="utf-8") as file:
            source_code = file.read()

        self.logger.info(f"Prompt:\n{prompt}")

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
            if chunk.choices:
                delta = chunk.choices[0].delta
                if delta.content:
                    response += delta.content

        self.logger.info(f"LLM API transpiled result:\n{response}")
        return response

    def openai_repair(self, prompt: str, **kwargs):
        api_key = kwargs.get("api_key")
        model_name = kwargs.get("model_name", "gpt-4")
        temperature = kwargs.get("temperature", 0.2)
        max_tokens = kwargs.get("max_tokens", 2048)
        top_p = kwargs.get("top_p", 0.7)
        base_url = kwargs.get("base_url", None)

        self.logger.info(f"Prompt:\n{prompt}")

        system_prompt = "You are a compiler assistant helping to translate C code into valid and idiomatic Rust code."

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

        self.logger.info(f"LLM API repaired result:\n{response}")
        return response

    def hf_transpile(self, file_path: str, prompt: str, num_samples: int = 1, **kwargs):
        """
        Translate source code into target language code using a pre-trained Hugging Face model,
        and generates multiple different outputs by controlling the temperature parameter.
        """
        temperature = kwargs.get("temperature", 0.2)
        max_tokens = kwargs.get("max_tokens", 2048)
        top_p = kwargs.get("top_p", 0.7)

        model_name = self.model_name

        self.logger.info(f"Prompt:\n{prompt}")

        system_prompt = "You are an expert in code translation, responsible for translating C programs into Rust programs."
        messages = [
            {"role": "system", "content": system_prompt},
            {"role": "user", "content": prompt},
        ]
        text = self.tokenizer.apply_chat_template(
            messages, tokenize=False, add_generation_prompt=True
        )
        model_inputs = self.tokenizer([text], return_tensors="pt").to(self.model.device)

        model_inputs.pop("token_type_ids", None)

        responses = []

        generated_ids = self.model.generate(
            **model_inputs,
            max_new_tokens=max_tokens,
            do_sample=True,
            num_return_sequences=num_samples,
            top_p=top_p,
            temperature=temperature,
        )

        generated_ids = [
            output_ids[len(input_ids) :]
            for input_ids, output_ids in zip(model_inputs.input_ids, generated_ids)
        ]

        for i, output in enumerate(generated_ids):
            response = self.tokenizer.decode(output, skip_special_tokens=True)
            responses.append(response)
            self.logger.info(
                f"{model_name} transpiled result {i+1}/{num_samples}:\n{response}"
            )

        return responses

    def extract_code_block(self, code: str):
        pattern = re.compile(r"```(?:rust)?\n((?:.|\n)*?)\n?```", re.DOTALL)
        try:
            match = pattern.search(code)
        except Exception:
            raise ValueError(
                "The selected LLM failed to produce a valid Rust code block. This may be due to the model's limited capability in generating structured responses.\nPlease try using a more capable LLM or review your parameter settings."
            )
        if not match:
            return code

        code_block = match.group(1).strip()
        return code_block if code_block else "\n"

    def postprocess(self, response: str, output_file: str):
        # output_file = self.config.transpiled_output
        processed_code = self.extract_code_block(response)
        self.logger.info(f"Postprocessed code:\n{processed_code}\n")
        with open(output_file, "w", encoding="utf-8") as file:
            file.write(processed_code)
        return processed_code

    def hf_repair(self, prompt: str, num_samples: int = 1, **kwargs):
        temperature = kwargs.get("temperature", 0.2)
        max_tokens = kwargs.get("max_tokens", 2048)
        top_p = kwargs.get("top_p", 0.7)

        model_name = self.model_name

        self.logger.info(f"Prompt:\n{prompt}")

        system_prompt = "You are a compiler assistant helping to translate C code into valid and idiomatic Rust code."
        messages = [
            {"role": "system", "content": system_prompt},
            {"role": "user", "content": prompt},
        ]
        text = self.tokenizer.apply_chat_template(
            messages, tokenize=False, add_generation_prompt=True
        )
        model_inputs = self.tokenizer([text], return_tensors="pt").to(self.model.device)

        model_inputs.pop("token_type_ids", None)

        responses = []

        generated_ids = self.model.generate(
            **model_inputs,
            max_new_tokens=max_tokens,
            do_sample=True,
            num_return_sequences=num_samples,
            temperature=temperature,
            top_p=top_p,
        )

        generated_ids = [
            output_ids[len(input_ids) :]
            for input_ids, output_ids in zip(model_inputs.input_ids, generated_ids)
        ]

        for i, output in enumerate(generated_ids):
            response = self.tokenizer.decode(output, skip_special_tokens=True)
            responses.append(response)
            self.logger.info(
                f'"{model_name}" repaired Rust code {i+1}/{num_samples}:\n{response}'
            )

        return responses


class BatchTranspiler(Transpiler):
    def __init__(self, model, logger, lang_lib):
        super().__init__(model, logger)
        self.lang_lib = lang_lib

    def openai_batch_transpile(
        self, txt_file_path, target_root_dir, repair_round_threshold, api_key
    ):
        with open(txt_file_path, "r", encoding="utf-8") as f:
            lines = f.readlines()

        transpiled_fail_to_compile_list = []
        repaired_fail_to_compile_list = []
        for line in lines:
            c_file_path = line.strip()
            if not c_file_path or not c_file_path.endswith(".c"):
                continue

            self.logger.info(f"Processing {c_file_path}.\n")

            try:
                data_index = c_file_path.rfind("/data/")
            except ValueError:
                self.logger.error(
                    f"Skipped: '/data/' not found in path '{c_file_path}'"
                )
                continue

            relative_path = c_file_path[data_index + len("/data/") :]
            dir_part, c_filename = os.path.split(relative_path)
            rs_filename = os.path.splitext(c_filename)[0].replace(".", "_") + ".rs"
            # create 'target_dir' if it does not exist.
            target_dir = os.path.join(target_root_dir, dir_part)
            os.makedirs(target_dir, exist_ok=True)
            target_file_path = os.path.join(target_dir, rs_filename)

            try:
                extrator = SpecExtractor(logger=self.logger, lang_lib=self.lang_lib)
                acsl_info, code_with_assert = extrator.llm_extract_and_replace(
                    c_file_path
                )
            except Exception as e:
                self.logger.error(f"{e}\n")
                continue

            code_with_assert = code_with_assert.strip()

            with tempfile.NamedTemporaryFile(
                mode="w+", delete=False, suffix=".c"
            ) as tmp:
                tmp_path = tmp.name
                tmp.write(code_with_assert)
                tmp.flush()

            ClangFormatter().format_file(tmp_path)
            self.logger.info(
                f"Source C code, whose `assert` ACSL annotations have been replaced with `// verus_assert(id)`, is as follow:\n```c\n{code_with_assert}\n```\n"
            )
            llm_res = self.openai_transpile(
                file_path=tmp_path,
                api_key=api_key,
                prompt=transpile_prompt(code_with_assert),
            )
            transpiled_res = self.postprocess(llm_res, output_file=target_file_path)

            # transpiled_total_num += 1
            is_first_compile = True
            # repair round threshold
            for i in range(repair_round_threshold):
                success, errors = Rustc().execute(file_path=target_file_path)
                if not success:
                    if is_first_compile:
                        # transpiled_fail_to_compile_num += 1
                        transpiled_fail_to_compile_list.append(c_file_path)
                        is_first_compile = False

                    self.logger.warning(
                        f"Repair Round: {i+1}/{repair_round_threshold}\n"
                    )

                    llm_res = self.openai_repair(
                        api_key=api_key,
                        prompt=repair_prompt(
                            c_file=tmp_path,
                            rust_file=target_file_path,
                            error_msg=errors,
                        ),
                    )

                    repaired_res = self.postprocess(
                        llm_res, output_file=target_file_path
                    )
                else:
                    break

            success, errors = Rustc().execute(file_path=target_file_path)
            if not success:
                self.logger.error(
                    f'After **{repair_round_threshold}** repair rounds of LLM, Rustc still failed on "{c_file_path}"!\n'
                )
                repaired_fail_to_compile_list.append(c_file_path)
            else:
                self.logger.info(f'Rustc successfully compiled "{c_file_path}"!\n')

            os.remove(tmp_path)

        jsonfile = os.path.join(target_root_dir, "rustc_fail_files.json")
        data = {
            "transpile_fail": transpiled_fail_to_compile_list,
            "repair_fail": repaired_fail_to_compile_list,
        }
        with open(jsonfile, "w", encoding="utf-8") as f:
            json.dump(data, f, ensure_ascii=False, indent=4)


class SkeletonCompletor:
    def __init__(self, logger):
        self.logger = logger

    def completion(self, c_source_file, **kwargs):
        script_dir = os.path.dirname(os.path.abspath(__file__))
        lang_lib = os.path.abspath(
            os.path.join(script_dir, "../spec/build/my-languages.so")
        )
        generator = SkeletonGenerator(lang_lib=lang_lib)
        generator.main(c_source_file, **kwargs)


if __name__ == "__main__":
    pass
