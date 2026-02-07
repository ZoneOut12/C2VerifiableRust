import os, argparse, json, shutil, tempfile, toml
from types import SimpleNamespace
from src.utils.logger import Logger
from src.spec.extract import SpecExtractor, MyException
from src.spec.transform import SpecTransformer, TransformError
from src.spec.refactor import Refactor
from src.spec.merge import Merger
from src.utils.formatter import VerusFmt, ClangFormatter
from src.acsl.counter import TransformErrorCounter
from src.spec.specdetector import SpecDetector
from src.c2rust.transpile import Transpiler
from src.c2rust.file_translator import FileTranslator
from src.utils.verus import VEval, Verus
from src.utils.rustc import Rustc
from src.utils.error import TranslationError


class ModularWorkflow:
    @staticmethod
    def merge_dicts_add(d1, d2):
        merged = d1.copy()
        for key, value in d2.items():
            merged[key] = merged.get(key, 0) + value
        return merged

    @staticmethod
    def transform_error_dict(error):
        if error == TransformError.At:
            return {"At": 1}
        elif error == TransformError.InductiveDef:
            return {"InductiveDef": 1}
        elif error == TransformError.AxiomaticDecl:
            return {"AxiomaticDecl": 1}
        elif error == TransformError.ReadsClause:
            return {"ReadsClause": 1}
        elif error == TransformError.TerminatesClause:
            return {"TerminatesClause": 1}
        elif error == TransformError.GhostCode:
            return {"GhostCode": 1}
        elif error == TransformError.Labels:
            return {"Labels": 1}
        else:
            return {"Others": 1}

    @staticmethod
    def copy_file(src, dst):
        """
        Copy the content of file from src to dst.
        src: str, path to the source file
        dst: str, path to the destination file
        """
        with open(src, "rb") as fsrc:
            with open(dst, "wb") as fdst:
                fdst.write(fsrc.read())

    @staticmethod
    def create_dir(dir_path):
        """
        Create a directory if it does not exist, and delete all files in it if it does exist.
        dir_path: str, path to the directory
        """
        if not os.path.exists(dir_path):
            os.makedirs(dir_path)
        else:
            # delete all files in the directory
            for filename in os.listdir(dir_path):
                file_path = os.path.join(dir_path, filename)
                try:
                    if os.path.isfile(file_path) or os.path.islink(file_path):
                        os.unlink(file_path)
                    elif os.path.isdir(file_path):
                        shutil.rmtree(file_path)
                except Exception as e:
                    raise ValueError(f"Failed to delete {file_path}.\nReason: {e}\n")

    @staticmethod
    def read_dataset_paths(file_path):
        paths = []
        with open(file_path, "r", encoding="utf-8") as f:
            for line in f:
                path = line.strip()
                if path:
                    paths.append(path)
        return paths

    @staticmethod
    def API_LLM_main_with_translation(**kwargs):
        script_dir = os.path.dirname(os.path.abspath(__file__))
        lang_lib = os.path.abspath(
            os.path.join(script_dir, "../spec/build/my-languages.so")
        )
        proj_dir = os.path.abspath(os.path.join(script_dir, "..", ".."))
        temp_dir = os.path.join(proj_dir, ".temp")
        if not os.path.exists(temp_dir):
            os.makedirs(temp_dir)

        # extract arguments
        args = SimpleNamespace(**kwargs)
        logger = Logger(log_file=args.log_file).setup_logger(overwrite=True)
        dataset_txt_path = args.dataset_txt
        verus_path = os.path.expanduser(args.verus)
        result_dir = args.result_dir

        libclang_path = args.libclang_path
        api_key = args.api_key
        model_name = args.model_name
        base_url = args.base_url if args.base_url else None
        repair_round_threshold = int(args.repair_round_threshold)
        translator = FileTranslator(libclang_path=libclang_path)

        verus_success_dir = os.path.join(result_dir, "verus_success")
        verus_fail_dir = os.path.join(result_dir, "verus_fail")
        if not os.path.exists(result_dir):
            os.makedirs(result_dir)

        # creat brand-new directories for `verus_success` and `verus_fail``
        ModularWorkflow.create_dir(verus_success_dir)
        ModularWorkflow.create_dir(verus_fail_dir)

        transform_error_files = {}
        verus_success_files = []
        verus_fail_files = []
        total_func_num = 0
        verified_func_num = 0

        rustc_fail_list = []
        transpiled_fail_to_compile_num = 0
        transpiled_total_num = 0
        is_first_compile = True

        missing_spec_files = {}
        non_migratable_files = []

        transform_error_counter = TransformErrorCounter()
        veval = VEval(verus_path=verus_path, logger=logger)
        dataset_paths = ModularWorkflow.read_dataset_paths(dataset_txt_path)
        debug_info = {"filename": None}

        for path in dataset_paths:
            file_path = path
            debug_info["filename"] = file_path

            logger.info(f"Processing: {file_path}\n")

            input_file_copy = os.path.join(temp_dir, "input.c")
            shutil.copyfile(file_path, input_file_copy)

            extrator = SpecExtractor(logger=logger, lang_lib=lang_lib)

            # check if the file is supported by SpecTransformer.
            spec_detector = SpecDetector()
            if not spec_detector.check_file_supported(file_path, lang_lib):
                non_migratable_files.append(file_path)
                continue

            try:
                acsl_info, code_with_assert = extrator.llm_extract_and_replace(
                    input_file_copy
                )
            except MyException as e:
                transform_error = TransformError.GhostCode
                logger.error(
                    f'"{file_path}" failed in SpecTransformer!\nTransformError type: {transform_error}\n'
                )
                tmp_dict = ModularWorkflow.transform_error_dict(transform_error)
                transform_error_counter = ModularWorkflow.merge_dicts_add(
                    transform_error_counter, tmp_dict
                )
                if str(transform_error) not in transform_error_files:
                    transform_error_files[str(transform_error)] = [file_path]
                else:
                    transform_error_files[str(transform_error)].append(file_path)
                continue

            # run C2Rust to transpile
            preprocessed_file = os.path.join(temp_dir, "preprocessed.c")
            code_with_assert = code_with_assert.strip()
            with open(preprocessed_file, "w") as f:
                f.write(code_with_assert)

            ClangFormatter().format_file(preprocessed_file)
            logger.info(
                f'Source C code, whose `assert` ACSL annotations have been replaced with `// verus_assert(id)`, has been written to "{preprocessed_file}":\n```c\n{code_with_assert}\n```\n'
            )
            params = {
                "api_key": api_key,
                "model_name": model_name,
                "base_url": base_url,
                "temperature": float(args.temperature),
                "max_tokens": int(args.max_tokens),
                "top_p": float(args.top_p),
            }
            llm_res, is_repaired = translator.translate(preprocessed_file, **params)
            rust_file = os.path.join(temp_dir, "translation.rs")
            with open(rust_file, "w") as f:
                f.write(llm_res)

            transpiled_total_num += 1
            is_first_compile = not is_repaired

            with tempfile.NamedTemporaryFile(mode="w+", delete=False) as temp_rust_file:
                temp_rust_file_path = temp_rust_file.name
            shutil.copyfile(rust_file, temp_rust_file_path)

            transformer = SpecTransformer(
                file_path=file_path,
                lang_lib=lang_lib,
                logger=logger,
                transpiled_rust=rust_file,
                type_guidance=(args.type_guidance.lower().strip() == "true"),
            )
            verus_info = transformer.transform(acsl_info, temp_dir=temp_dir)
            if transformer.return_code == -1:
                transform_error = transformer.error_type
                logger.error(
                    f'"{file_path}" failed in SpecTransformer!\nTransformError type: {transform_error}\n'
                )
                tmp_dict = ModularWorkflow.transform_error_dict(transform_error)
                transform_error_counter = ModularWorkflow.merge_dicts_add(
                    transform_error_counter, tmp_dict
                )
                # transform_error_counter.update(transform_error)
                if str(transform_error) not in transform_error_files:
                    transform_error_files[str(transform_error)] = [file_path]
                else:
                    transform_error_files[str(transform_error)].append(file_path)
                continue

            refactor = Refactor(logger=logger, lang_lib=lang_lib)
            refactor.llm_main(file_path=rust_file)

            merger = Merger(logger=logger, lang_lib=lang_lib)
            file_to_verify = os.path.join(temp_dir, "verus_input.rs")
            res = merger.merge(
                rust_file=os.path.join(
                    os.path.dirname(rust_file), "refactored_translation.rs"
                ),
                verus_info=verus_info,
                output_file=file_to_verify,
                is_llm=True,
            )

            missed_specs = merger.get_unmerged_specs()
            if len(missed_specs) > 0:
                missing_spec_files[debug_info["filename"]] = [
                    len(missed_specs),
                    "/",
                    len(verus_info["annotation"]),
                ]
                logger.error("Following specifications are not merged successfully:\n")
                for i in range(len(missed_specs)):
                    logger.error(f"{i+1}/{len(missed_specs)}:\n{missed_specs[i]}\n")

            VerusFmt(logger).run(file_to_verify)
            with open(file_to_verify) as f:
                logger.info(
                    "Final-version code to be verified:\n```rust\n"
                    + f.read()
                    + "\n```\n"
                )
            verus_success = veval.eval(rust_file=file_to_verify, **debug_info)
            if verus_success:
                verus_success_files.append(file_path)
                # Copy the file to the verus_success directory
                # Modify the file name from a '.c' extension to a '.rs' extension
                base, _ = os.path.splitext(file_path)
                new_file_path = base + ".rs"
                success_file_path = os.path.join(
                    verus_success_dir, os.path.basename(new_file_path)
                )
                ModularWorkflow.copy_file(file_to_verify, success_file_path)
            else:
                verus_fail_files.append(file_path)
                # Copy the file to the verus_fail directory
                # Modify the file name from a '.c' extension to a '.rs' extension
                base, _ = os.path.splitext(file_path)
                new_file_path = base + ".rs"
                fail_file_path = os.path.join(
                    verus_fail_dir, os.path.basename(new_file_path)
                )
                ModularWorkflow.copy_file(file_to_verify, fail_file_path)
            veval.get_error_message()

            cur_verified_func_num, cur_total_func_num = Verus(
                verus_path=verus_path, logger=None
            ).count_success_rate_of_function_level_per_file(
                temp_rust_file_path, file_to_verify, lang_lib
            )
            total_func_num += cur_total_func_num
            verified_func_num += cur_verified_func_num
            os.remove(temp_rust_file_path)

        # Print the statistics about non-migratable specifications
        logger.terminal(
            f"Number of files that have non-migratable specifications: {len(non_migratable_files)}\n"
        )
        logger.terminal(
            f"Number of files that failed to compile after translation: {len(rustc_fail_list)}\n"
        )

        # Save the error statistics to a JSON file
        with open(
            os.path.join(result_dir, "compile_error_files.json"), "w", encoding="utf-8"
        ) as f:
            json.dump(veval.compile_error_list, f, indent=4, ensure_ascii=False)

        with open(
            os.path.join(result_dir, "verify_error_files.json"), "w", encoding="utf-8"
        ) as f:
            json.dump(veval.verify_error_list, f, indent=4, ensure_ascii=False)

        veval.get_error_statistics(
            verus_output=os.path.join(result_dir, "verus_error_msg.json"),
            rustc_output=os.path.join(result_dir, "rustc_error_msg.json"),
        )

        result_data = {
            "transform_error_files": transform_error_files,
            "translation_failed_files": rustc_fail_list,
            "verus_success_files": verus_success_files,
            "verus_fail_files": verus_fail_files,
        }

        logger.terminal(
            f"\033[1mFunction-level Pass Rate: {verified_func_num}/{total_func_num}\033[0m\n"
        )

        with open(
            os.path.join(result_dir, "verus_result.json"), "w", encoding="utf-8"
        ) as f:
            json.dump(result_data, f, indent=4, ensure_ascii=False)

        with open(
            os.path.join(result_dir, "missing_spec_files.json"), "w", encoding="utf-8"
        ) as f:
            json.dump(missing_spec_files, f, indent=4, ensure_ascii=False)

        logger.terminal(f'Results are stored in "{result_dir}".\n')
        shutil.rmtree(temp_dir)


if __name__ == "__main__":
    raise ValueError("Not executable yet!")
    parent_dir = os.path.abspath(
        os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")
    )
    config = toml.load(os.path.join(parent_dir, "config.toml"))
    paths = config["path"]
    for key, value in paths.items():
        expanded = os.path.expanduser(value)
        paths[key] = os.path.abspath(expanded)
    model = config["model"]
    spec = config["spec"]
    args = {**paths, **model, **spec}
    print(args)
    ModularWorkflow.API_LLM_main_with_translation(**args)