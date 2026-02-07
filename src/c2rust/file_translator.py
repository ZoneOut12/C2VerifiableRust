from src.c2rust.slice_translator import SliceTranslator
from src.c2rust.depgraph import DependencyGraphBuilder
from src.spec.extract import SpecExtractor
from src.utils.logger import DummyLogger
from src.utils.rustc import Rustc
import os, re, sys, tempfile, json
from tree_sitter import Language, Parser


class RustSignatureExtractor:
    def __init__(self, lang_lib):
        self.lang_lib = lang_lib
        self.parser = self.build_parser(lang_lib)
        pass

    def build_parser(self, lang_lib):
        LANGUAGE_LIB = lang_lib
        LANGUAGE = Language(LANGUAGE_LIB, "rust")
        parser = Parser()
        parser.set_language(LANGUAGE)
        return parser

    def extract_rust_signature(self, code: str):
        tree = self.parser.parse(bytes(code, "utf8"))
        root = tree.root_node

        for node in root.children:
            if node.type == "function_item":
                block_node = node.child_by_field_name("body")
                start = node.start_byte
                end = block_node.start_byte if block_node else node.end_byte

                signature = code[start:end].strip()

                if block_node:
                    signature += " {\n    // implementation hidden\n}"
                else:
                    if not signature.endswith(";"):
                        signature = signature.rstrip() + ";"

                return signature


class FileTranslator:
    def __init__(self, libclang_path):
        script_dir = os.path.dirname(os.path.abspath(__file__))
        lang_lib = os.path.abspath(
            os.path.join(script_dir, "../spec/build/my-languages.so")
        )
        self.lang_lib = lang_lib
        self.rust_signature_extractor = RustSignatureExtractor(lang_lib)
        self.dep_graph_builder = DependencyGraphBuilder(libclang_path)

    def incremental_translate(self, preprocessed_c_file_path, **kwargs):
        res = self.dep_graph_builder.build(preprocessed_c_file_path)
        c_slices = res["c_slices"]
        slice_deps = res["slice_deps"]
        # functions in rust_slices will be extracted to be functions without actual body
        rust_slices = res["rust_slices"]
        rust_snippets = res["rust_slices"].copy()
        # Already translated rust context
        file_context = ""
        is_repaired = False
        for items in c_slices.items():
            slice_name, slice_tuple = items
            translator = SliceTranslator()
            context = None
            if len(slice_deps[slice_name]) > 0:
                context = ""
                for dep in slice_deps[slice_name]:
                    if rust_slices[dep] is None:
                        raise ValueError(
                            f'Dependency "{dep}" has not been translated yet'
                        )
                    context += rust_slices[dep] + "\n\n"
            rust_code, is_first_time_success = translator.translate_slice(
                slice_tuple, file_context, context=context, **kwargs
            )
            if is_first_time_success == False:
                is_repaired = True
            rust_snippets[slice_name] = rust_code

            file_context += rust_code + "\n\n"
            if slice_tuple[1] == "Function" or slice_tuple[1] == "Undefined Function":
                rust_signature = self.rust_signature_extractor.extract_rust_signature(
                    rust_code
                )
                if slice_name not in rust_slices:
                    raise ValueError(f'Slice "{slice_name}" not found in rust slices')
                rust_slices[slice_name] = rust_signature
            else:
                if slice_name not in rust_slices:
                    raise ValueError(f'Slice "{slice_name}" not found in rust slices')
                rust_slices[slice_name] = rust_code
        return file_context, is_repaired

    def refactor_rust_code(self, rust_code: str) -> str:
        """
        Global variable definitions using `static mut` are changed to `const` if possible.
        """
        pattern = re.compile(
            r"(?m)^\s*static\s+mut\s+([A-Za-z_][A-Za-z0-9_]*)(\s*:\s*[^=]+=\s*[^;]+;)"
        )
        matches = list(pattern.finditer(rust_code))
        if not matches:
            return rust_code

        working_code = rust_code

        for match in matches:
            var_name = match.group(1)
            suffix = match.group(2)
            original_decl = match.group(0)
            new_decl = f"const {var_name}{suffix}"

            modified_code = working_code.replace(original_decl, new_decl, 1)

            with tempfile.TemporaryDirectory() as tmpdir:
                temp_rust_file = os.path.join(tmpdir, "test.rs")
                with open(temp_rust_file, "w", encoding="utf-8") as f:
                    f.write(modified_code)

                result, msg = Rustc().execute(temp_rust_file)

            if result:
                working_code = modified_code

        return working_code

    def translate(self, c_file_path, **kwargs):
        _, code_with_placeholders = SpecExtractor(
            logger=DummyLogger(), lang_lib=self.lang_lib
        ).llm_extract_and_replace(c_file_path)
        with tempfile.NamedTemporaryFile(
            mode="w+", delete=False, suffix=".c"
        ) as tmp_file:
            tmp_file.write(code_with_placeholders)
            tmp_file_path = tmp_file.name

        translated_rust_code, is_repaired = self.incremental_translate(
            tmp_file_path, **kwargs
        )
        os.remove(tmp_file_path)
        # translated_rust_code = self.refactor_rust_code(translated_rust_code)
        return translated_rust_code, is_repaired


if __name__ == "__main__":
    libclang_path = "/usr/lib/llvm-14/lib/libclang.so"
    project_root_dir = os.path.abspath(
        os.path.join(os.path.dirname(__file__), "..", "..")
    )
    file_path = os.path.join(project_root_dir, "data/tutorial_wp/ex-4-change-answer.c")
    raise ValueError("No arguments")
    args = {
        "model_name": "",
        "base_url": "",
        "api_key": "",
        "repair_round_threshold": 3,
    }
    translator = FileTranslator(libclang_path)
    res = translator.translate(file_path, **args)
    print(res)
