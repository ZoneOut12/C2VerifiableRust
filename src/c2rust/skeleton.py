from tree_sitter import Language, Parser
from openai import OpenAI
import os, sys, re
from antlr4 import InputStream, CommonTokenStream
from src.spec.ACSLParserVisitor import ACSLParserVisitor
from src.spec.ACSLLexer import ACSLLexer
from src.spec.ACSLParser import ACSLParser
from src.spec.extract import ACSLType, ACSLJudger, SpecExtractor
from src.prompt.prompt import transpile_prompt
from src.utils.logger import DummyLogger
from src.spec.refactor import Refactor
from src.spec.merge import Merger
from src.spec.transform import SpecTransformer
from src.utils.formatter import VerusFmt
from src.utils.verus import Verus


class SkeletonGenerator:
    def __init__(self, lang_lib):
        self.lang_lib = lang_lib
        self.parser = self.build_parser(lang_lib)
        pass

    def build_parser(self, lang_lib):
        LANGUAGE_LIB = lang_lib
        LANGUAGE = Language(LANGUAGE_LIB, "c")
        parser = Parser()
        parser.set_language(LANGUAGE)
        return parser

    def translate_code_without_functions_via_llm(self, c_code, **kwargs):
        api_key = kwargs.get("api_key")
        base_url = kwargs.get("base_url", None)
        model_name = kwargs.get("model_name", "gpt-4")
        temperature = kwargs.get("temperature", 0.2)
        max_tokens = kwargs.get("max_tokens", 2048)
        top_p = kwargs.get("top_p", 0.7)

        if base_url:
            client = OpenAI(base_url=base_url, api_key=api_key)
        else:
            client = OpenAI(api_key=api_key)

        system_prompt = "You are an expert in code translation, responsible for translating C programs into Rust programs."
        prompt = transpile_prompt(code=c_code.strip())

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

        return self.extract_code_block(response)

    def translate_sig_via_llm(self, c_code, **kwargs):
        api_key = kwargs.get("api_key")
        base_url = kwargs.get("base_url", None)
        model_name = kwargs.get("model_name", "gpt-4")
        temperature = kwargs.get("temperature", 0.2)
        max_tokens = kwargs.get("max_tokens", 2048)
        top_p = kwargs.get("top_p", 0.7)

        if base_url:
            client = OpenAI(base_url=base_url, api_key=api_key)
        else:
            client = OpenAI(api_key=api_key)

        script_dir = os.path.dirname(os.path.abspath(__file__))
        parent_dir = os.path.dirname(script_dir)
        prompt_path = os.path.join(parent_dir, "prompt", "sig_prompt.txt")

        with open(prompt_path, "r", encoding="utf-8") as f:
            prompt_template = f.read()
        prompt = prompt_template.replace("{code}", c_code.strip())

        completion = client.chat.completions.create(
            model=model_name,
            messages=[
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

        return self.extract_code_block(response)

    def extract_code_block(self, llm_output):
        pattern = re.compile(r"```(?:rust)?\n((?:.|\n)*?)\n?```", re.DOTALL)
        try:
            match = pattern.search(llm_output)
        except Exception:
            raise ValueError(
                "The selected LLM failed to produce a valid output containing the Rust function signature. This may be due to the model's limited capability in generating structured responses.\nPlease try using a more capable LLM or review your parameter settings."
            )
        if not match:
            return llm_output

        code_block = match.group(1).strip()
        return code_block if code_block else "\n"

    def remove_functions_and_comments(self, c_code):
        root = self.parser.parse(bytes(c_code, "utf8")).root_node
        res = []

        for node in root.children:
            if (
                node.type == "comment"
                or node.type == "function_definition"
                or node.type == "declaration"
            ):
                pass
            else:
                res.append(node.text.decode("utf-8"))

        return "\n".join(res)

    def extract_acsl_and_functions(self, code):
        judger = ACSLJudger()
        is_skip = False

        bytes_code = bytes(code, "utf-8")
        c_input_segs = []

        def traverse(node):
            nonlocal is_skip
            if node.type == "comment":
                acsl_code = node.text.decode("utf-8")
                input_stream = InputStream(acsl_code)
                lexer = ACSLLexer(input_stream)
                token_stream = CommonTokenStream(lexer)
                acsl_parser = ACSLParser(token_stream)
                tree = acsl_parser.acsl()
                if judger.visitAcsl(tree).type == ACSLType.CONTRACT:
                    next_sibling = node.next_named_sibling
                    is_skip = True
                    if next_sibling.type == "function_definition":
                        body = next_sibling.child_by_field_name("body")
                        sig_text = (
                            bytes_code[next_sibling.start_byte : body.start_byte]
                            .decode()
                            .strip()
                        )
                        c_input = acsl_code.strip() + "\n" + sig_text + ";"
                        c_input_segs.append(c_input)
                    elif next_sibling.type == "declaration":
                        for child in next_sibling.children:
                            if child.type == "function_declarator":
                                c_input = (
                                    acsl_code.strip()
                                    + "\n"
                                    + next_sibling.text.decode().strip()
                                )
                                c_input_segs.append(c_input)
            elif node.type == "function_definition" and not is_skip:
                body = node.child_by_field_name("body")
                sig_text = (
                    bytes_code[node.start_byte : body.start_byte].decode().strip()
                )
                c_input = sig_text + ";"
                c_input_segs.append(c_input)
            elif node.type == "declaration" and not is_skip:
                for child in node.children:
                    if child.type == "function_declarator":
                        c_input = node.text.decode().strip()
                        c_input_segs.append(c_input)
            for child in node.children:
                traverse(child)

        traverse(self.parser.parse(bytes(code, "utf8")).root_node)
        return c_input_segs

    def generate_rust_skeleton(self, c_source_file, rust_file, **kwargs):
        with open(c_source_file, "r", encoding="utf-8") as file:
            code = file.read()

        non_acsl_block_comment_pattern = re.compile(r"/\*[^@].*?\*/", re.DOTALL)
        non_acsl_line_comment_pattern = re.compile(r"//(?!@).*")
        code = non_acsl_block_comment_pattern.sub("", code)
        code = non_acsl_line_comment_pattern.sub("", code)

        c_input_segs = self.extract_acsl_and_functions(code)

        remaining_c_input = self.remove_functions_and_comments(code)

        skeleton = []
        output = self.translate_code_without_functions_via_llm(
            remaining_c_input, **kwargs
        )
        print(output)
        skeleton.append(output)

        for sig in c_input_segs:
            rust_sig = self.translate_sig_via_llm(sig, **kwargs)
            print(rust_sig)
            skeleton.append(rust_sig + r"{unimplemented!()}")

        rust_skeleton = "\n".join(skeleton)
        with open(rust_file, "w", encoding="utf-8") as file:
            file.write(rust_skeleton)
        self.add_contracts_to_rust_skeleton(c_source_file, rust_file)
        return rust_skeleton

    def add_contracts_to_rust_skeleton(self, c_source_file, rust_dest_file):
        logger = DummyLogger()
        extrator = SpecExtractor(logger=logger, lang_lib=self.lang_lib)

        acsl_info, _ = extrator.llm_extract_and_replace(c_source_file)

        transformer = SpecTransformer(
            file_path=c_source_file,
            lang_lib=self.lang_lib,
            logger=logger,
            transpiled_rust=rust_dest_file,
            type_guidance="true",
        )
        script_dir = os.path.dirname(os.path.abspath(__file__))
        temp_dir = os.path.abspath(os.path.join(script_dir, "./tmp/"))

        verus_info = transformer.transform(acsl_info, temp_dir=temp_dir)
        if transformer.return_code == -1:
            raise ValueError("Spec transformation failed.")

        refactor = Refactor(logger=logger, lang_lib=self.lang_lib)
        refactor.llm_main(file_path=rust_dest_file)

        merger = Merger(logger=logger, lang_lib=self.lang_lib)

        file_to_verify = os.path.join(temp_dir, "verus_input.rs")
        res = merger.merge(
            rust_file=os.path.join(
                os.path.join(os.path.abspath(os.path.join(script_dir, "./tmp/"))),
                "refactored_llm_output.rs",
            ),
            verus_info=verus_info,
            output_file=file_to_verify,
            is_llm=True,
        )

        VerusFmt(logger).run(file_to_verify)
        verus_path = os.path.expanduser("~/verus-x86-linux/verus")
        VerusTool = Verus(verus_path=verus_path, logger=logger)
        return_code, mes = VerusTool.run_with_no_verify(file_to_verify)
        if return_code != 0:
            raise ValueError("Verus failed.")

    def main(self, c_file, **kwargs):
        script_dir = os.path.dirname(os.path.abspath(__file__))
        rust_file = os.path.abspath(os.path.join(script_dir, "./tmp/llm_output.rs"))
        res = self.generate_rust_skeleton(c_file, rust_file, **kwargs)
        return res


if __name__ == "__main__":
    script_dir = os.path.dirname(os.path.abspath(__file__))
    lang_lib = os.path.abspath(
        os.path.join(script_dir, "../spec/build/my-languages.so")
    )
    generator = SkeletonGenerator(lang_lib=lang_lib)
    project_root_dir = os.path.abspath(
        os.path.join(os.path.dirname(__file__), "..", "..")
    )
    c_file = os.path.join(
        project_root_dir, "data/tutorial_wp/ex-1-forall-exists-answer.c"
    )
    raise ValueError("No arguments")
    args = {
        "model_name": "",
        "base_url": "",
        "api_key": "",
        "repair_round_threshold": 3,
    }
    generator.main(c_file, **args)
