import os, argparse, json, shutil, tempfile, sys, traceback, io, toml
from types import SimpleNamespace
from src.utils.logger import Logger
from src.spec.extract import SpecExtractor, MyException, GhostCodePreprocessor
from src.spec.transform import SpecTransformer, TransformError
from src.spec.refactor import Refactor
from src.spec.merge import Merger
from src.utils.formatter import VerusFmt, ClangFormatter, C2Rust
from src.acsl.counter import TransformErrorCounter
from src.spec.specdetector import SpecDetector
from src.c2rust.transpile import Transpiler
from src.utils.verus import VEval, Verus
from src.utils.rustc import Rustc
from src.prompt.prompt import transpile_prompt, repair_prompt


class Pipeline:
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
                    print(f"Failed to delete {file_path}.\nReason: {e}\n")

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
        args = SimpleNamespace(**kwargs)

        script_dir = os.path.dirname(os.path.abspath(__file__))
        lang_lib = os.path.abspath(
            os.path.join(script_dir, "../spec/build/my-languages.so")
        )
        logger = Logger(log_file=args.log_file).setup_logger(overwrite=True)

        dataset_txt_path = args.dataset_txt
        verus_path = args.verus

        result_dir = args.result_dir
        verus_success_dir = os.path.join(result_dir, "verus_success")
        verus_fail_dir = os.path.join(result_dir, "verus_fail")
        if not os.path.exists(result_dir):
            os.makedirs(result_dir)
        if not os.path.exists(args.output):
            os.makedirs(args.output)
        Pipeline.create_dir(verus_success_dir)
        Pipeline.create_dir(verus_fail_dir)

        transform_error_files = []
        # transform_error_counter = TransformErrorCounter()

        verus_success_files = []
        verus_fail_files = []
        total_func_num = 0
        verified_func_num = 0

        transpiler = Transpiler(model="", logger=logger)

        repair_round_threshold = int(args.repair_round_threshold)
        rustc_fail_list = []
        transpiled_fail_to_compile_num = 0
        transpiled_total_num = 0
        is_first_compile = True

        missing_spec_files = {}
        non_migratable_files = []

        veval = VEval(verus_path=verus_path, logger=logger)
        dataset_paths = Pipeline.read_dataset_paths(dataset_txt_path)
        debug_info = {"filename": None}

        for path in dataset_paths:
            file_path = path
            debug_info["filename"] = file_path

            temp_dir = args.output
            logger.info(f"Processing: {file_path}\n")

            processed_file = os.path.join(temp_dir, "input.c")
            shutil.copyfile(file_path, processed_file)

            extractor = SpecExtractor(logger=logger, lang_lib=lang_lib)

            # check if the file is supported by SpecTransformer.
            spec_detector = SpecDetector()
            with tempfile.NamedTemporaryFile(mode="w+", delete=False) as deghost_file:
                deghosted_code = extractor.remove_comments(file_path)
                deghosted_code = extractor.get_acsl_annotation_without_ats(
                    deghosted_code
                )
                deghosted_code = GhostCodePreprocessor.preprocess(
                    lang_lib, deghosted_code
                )
                deghost_file.write(deghosted_code)
                deghost_file_path = deghost_file.name

            if not spec_detector.check_file_supported(deghost_file_path, lang_lib):
                non_migratable_files.append(file_path)
                logger.error(f"{file_path} contains non-migratable specifications!\n")
                transform_error_files.append(file_path)
                os.remove(deghost_file_path)
                continue

            os.remove(deghost_file_path)

            acsl_info, code_with_assert = extractor.llm_extract_and_replace(
                processed_file
            )

            # run llm to transpile C to Rust
            temp_file = os.path.join(temp_dir, "source.c")
            code_with_assert = code_with_assert.strip()
            with open(temp_file, "w") as f:
                f.write(code_with_assert)

            ClangFormatter().format_file(temp_file)
            logger.info(
                f'Source C code, whose `assert` ACSL annotations have been replaced with `// verus_assert(id)`, has been written to "{temp_file}":\n```c\n{code_with_assert}\n```\n'
            )
            params = {
                "api_key": args.api_key,
                "model_name": args.model_name,
                "base_url": args.base_url if args.base_url else None,
                "temperature": float(args.temperature),
                "max_tokens": int(args.max_tokens),
                "top_p": float(args.top_p),
            }
            llm_res = transpiler.openai_transpile(
                file_path=temp_file, prompt=transpile_prompt(code_with_assert), **params
            )
            rust_file = os.path.join(temp_dir, "src/source.rs")
            transpiler.postprocess(llm_res, output_file=rust_file)

            transpiled_total_num += 1
            is_first_compile = True

            # repair round threshold
            for i in range(repair_round_threshold):
                success, errors = Rustc().execute(file_path=rust_file)
                if not success:
                    if is_first_compile:
                        transpiled_fail_to_compile_num += 1
                        is_first_compile = False

                    logger.warning(f"Repair Round: {i+1}/{repair_round_threshold}\n")
                    # repair rust based on `rustc`

                    llm_res = transpiler.openai_repair(
                        prompt=repair_prompt(
                            c_file=temp_file, rust_file=rust_file, error_msg=errors
                        ),
                        **params,
                    )

                    transpiler.postprocess(llm_res, output_file=rust_file)
                else:
                    break

            success, errors = Rustc().execute(file_path=rust_file)
            if not success:
                logger.error(
                    f'After **{repair_round_threshold}** repair rounds of LLM, Rustc still failed on translated "{file_path}"!\n'
                )
                rustc_fail_list.append(file_path)
                continue
            else:
                logger.info(f'Rustc successfully compiled translated "{file_path}"!\n')

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
            verus_info = transformer.transform(acsl_info, temp_dir=args.output)

            # necessary postprocessing such as add the `verus!` macro`
            refactor = Refactor(logger=logger, lang_lib=lang_lib)
            refactor.llm_main(file_path=rust_file)

            broadcast_use_lemmas = transformer.visitor.broadcast_inductive_lemmas
            merger = Merger(logger=logger, lang_lib=lang_lib)
            file_to_verify = os.path.join(temp_dir, "verus_input.rs")
            res = merger.merge(
                rust_file=os.path.join(
                    os.path.dirname(rust_file), "refactored_source.rs"
                ),
                verus_info=verus_info,
                broadcast_use_lemmas=broadcast_use_lemmas,
                output_file=file_to_verify,
                is_llm=True,
            )

            # check whether translation misalignment led to specification embeddding failures
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
                Pipeline.copy_file(file_to_verify, success_file_path)
            else:
                verus_fail_files.append(file_path)
                # Copy the file to the verus_fail directory
                # Modify the file name from a '.c' extension to a '.rs' extension
                base, _ = os.path.splitext(file_path)
                new_file_path = base + ".rs"
                fail_file_path = os.path.join(
                    verus_fail_dir, os.path.basename(new_file_path)
                )
                Pipeline.copy_file(file_to_verify, fail_file_path)
            veval.get_error_message()

            cur_verified_func_num, cur_total_func_num = Verus(
                verus_path=verus_path, logger=None
            ).count_success_rate_of_function_level_per_file(
                temp_rust_file_path, file_to_verify, lang_lib
            )
            total_func_num += cur_total_func_num
            verified_func_num += cur_verified_func_num
            os.remove(temp_rust_file_path)

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

    @staticmethod
    def LLM_main_without_translation(**kwargs):
        args = SimpleNamespace(**kwargs)

        script_dir = os.path.dirname(os.path.abspath(__file__))
        lang_lib = os.path.abspath(
            os.path.join(script_dir, "../spec/build/my-languages.so")
        )
        logger = Logger(log_file=args.log_file).setup_logger(overwrite=True)

        dataset_txt_path = args.dataset_txt
        verus_path = args.verus

        result_dir = args.result_dir
        verus_success_dir = os.path.join(result_dir, "verus_success")
        verus_fail_dir = os.path.join(result_dir, "verus_fail")
        if not os.path.exists(result_dir):
            os.makedirs(result_dir)
        if not os.path.exists(args.output):
            os.makedirs(args.output)
        Pipeline.create_dir(verus_success_dir)
        Pipeline.create_dir(verus_fail_dir)

        transform_error_files = []
        # transform_error_counter = TransformErrorCounter()
        verus_success_files = []
        verus_fail_files = []
        total_func_num = 0
        verified_func_num = 0

        cache_dir = args.tranpiled_rust_dir
        missing_spec_files = {}
        non_migratable_files = []

        veval = VEval(verus_path=verus_path, logger=logger)
        dataset_paths = Pipeline.read_dataset_paths(dataset_txt_path)
        debug_info = {"filename": None}
        for path in dataset_paths:
            file_path = path
            debug_info["filename"] = file_path

            temp_dir = args.output
            logger.info(f"Processing: {file_path}\n")

            processed_file = os.path.join(temp_dir, "input.c")
            shutil.copyfile(file_path, processed_file)

            extractor = SpecExtractor(logger=logger, lang_lib=lang_lib)

            # check if the file is supported by SpecTransformer.
            spec_detector = SpecDetector()
            with tempfile.NamedTemporaryFile(mode="w+", delete=False) as deghost_file:
                deghosted_code = extractor.remove_comments(file_path)
                deghosted_code = extractor.get_acsl_annotation_without_ats(
                    deghosted_code
                )
                deghosted_code = GhostCodePreprocessor.preprocess(
                    lang_lib, deghosted_code
                )
                deghost_file.write(deghosted_code)
                deghost_file_path = deghost_file.name

            if not spec_detector.check_file_supported(deghost_file_path, lang_lib):
                non_migratable_files.append(file_path)
                logger.error(f"{file_path} contains non-migratable specifications!\n")
                transform_error_files.append(file_path)
                os.remove(deghost_file_path)
                continue

            os.remove(deghost_file_path)

            acsl_info, code_with_assert = extractor.llm_extract_and_replace(
                processed_file
            )

            temp_file = os.path.join(temp_dir, "source.c")
            code_with_assert = code_with_assert.strip()
            with open(temp_file, "w") as f:
                f.write(code_with_assert)

            ClangFormatter().format_file(temp_file)
            logger.info(
                f'Source C code, whose `assert` ACSL annotations have been replaced with `// verus_assert(id)`, has been written to "{temp_file}":\n```c\n{code_with_assert}\n```\n'
            )

            # obtain cached Rust code which originated from the translation of C code.
            rust_file = os.path.join(temp_dir, "src/source.rs")

            data_index = debug_info["filename"].rfind("/data/")
            relative_path = debug_info["filename"][data_index + len("/data/") :]
            dir_part, c_filename = os.path.split(relative_path)
            rs_filename = os.path.splitext(c_filename)[0].replace(".", "_") + ".rs"
            # create 'target_dir' if it does not exist.
            cached_rust_file = os.path.join(cache_dir, dir_part, rs_filename)
            with open(cached_rust_file, "r") as src, open(rust_file, "w") as dst:
                dst.write(src.read())

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
            verus_info = transformer.transform(acsl_info, temp_dir=args.output)

            refactor = Refactor(logger=logger, lang_lib=lang_lib)
            refactor.llm_main(file_path=rust_file)

            broadcast_use_lemmas = transformer.visitor.broadcast_inductive_lemmas
            merger = Merger(logger=logger, lang_lib=lang_lib)
            file_to_verify = os.path.join(temp_dir, "verus_input.rs")
            res = merger.merge(
                rust_file=os.path.join(
                    os.path.dirname(rust_file), "refactored_source.rs"
                ),
                verus_info=verus_info,
                broadcast_use_lemmas=broadcast_use_lemmas,
                output_file=file_to_verify,
                is_llm=True,  # llm
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
                base, _ = os.path.splitext(file_path)
                new_file_path = base + ".rs"
                success_file_path = os.path.join(
                    verus_success_dir, os.path.basename(new_file_path)
                )
                Pipeline.copy_file(file_to_verify, success_file_path)
            else:
                verus_fail_files.append(file_path)
                base, _ = os.path.splitext(file_path)
                new_file_path = base + ".rs"
                fail_file_path = os.path.join(
                    verus_fail_dir, os.path.basename(new_file_path)
                )
                Pipeline.copy_file(file_to_verify, fail_file_path)
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


    @staticmethod
    def c2rust_main_with_translation(**kwargs):
        args = SimpleNamespace(**kwargs)

        script_dir = os.path.dirname(os.path.abspath(__file__))
        lang_lib = os.path.abspath(
            os.path.join(script_dir, "../spec/build/my-languages.so")
        )
        logger = Logger(log_file=args.log_file).setup_logger(overwrite=True)

        dataset_txt_path = args.dataset_txt
        verus_path = args.verus

        result_dir = args.result_dir
        verus_success_dir = os.path.join(result_dir, "verus_success")
        verus_fail_dir = os.path.join(result_dir, "verus_fail")
        if not os.path.exists(result_dir):
            os.makedirs(result_dir)
        if not os.path.exists(args.output):
            os.makedirs(args.output)
        Pipeline.create_dir(verus_success_dir)
        Pipeline.create_dir(verus_fail_dir)

        transform_error_files = []
        # transform_error_counter = TransformErrorCounter()

        verus_success_files = []
        verus_fail_files = []
        total_func_num = 0
        verified_func_num = 0

        transpiler = Transpiler(model="", logger=logger)

        repair_round_threshold = int(args.repair_round_threshold)
        rustc_fail_list = []
        transpiled_fail_to_compile_num = 0
        transpiled_total_num = 0
        is_first_compile = True

        missing_spec_files = {}
        non_migratable_files = []

        veval = VEval(verus_path=verus_path, logger=logger)
        dataset_paths = Pipeline.read_dataset_paths(dataset_txt_path)
        debug_info = {"filename": None}

        for path in dataset_paths:
            file_path = path
            debug_info["filename"] = file_path

            temp_dir = args.output
            logger.info(f"Processing: {file_path}\n")

            processed_file = os.path.join(temp_dir, "input.c")
            shutil.copyfile(file_path, processed_file)

            extractor = SpecExtractor(logger=logger, lang_lib=lang_lib)

            # check if the file is supported by SpecTransformer.
            spec_detector = SpecDetector()
            with tempfile.NamedTemporaryFile(mode="w+", delete=False) as deghost_file:
                deghosted_code = extractor.remove_comments(file_path)
                deghosted_code = extractor.get_acsl_annotation_without_ats(
                    deghosted_code
                )
                deghosted_code = GhostCodePreprocessor.preprocess(
                    lang_lib, deghosted_code
                )
                deghost_file.write(deghosted_code)
                deghost_file_path = deghost_file.name

            if not spec_detector.check_file_supported(deghost_file_path, lang_lib):
                non_migratable_files.append(file_path)
                logger.error(f"{file_path} contains non-migratable specifications!\n")
                transform_error_files.append(file_path)
                os.remove(deghost_file_path)
                continue

            os.remove(deghost_file_path)

            acsl_info, code_with_assert = extractor.llm_extract_and_replace(
                processed_file
            )

            # run llm to transpile C to Rust
            temp_file = os.path.join(temp_dir, "source.c")
            code_with_assert = code_with_assert.strip()
            with open(temp_file, "w") as f:
                f.write(code_with_assert)

            ClangFormatter().format_file(temp_file)
            logger.info(
                f'Source C code, whose `assert` ACSL annotations have been replaced with `verus_assert(id);`, has been written to "{temp_file}":\n```c\n{code_with_assert}\n```\n'
            )
            
            # run `c2rust` to transpile C to Rust
            C2Rust(logger).transpile(
                input_file=temp_file, output_dir=temp_dir, **debug_info
            )
            
            rust_file = os.path.join(temp_dir, "src/source.rs")
            
            with open(rust_file) as f:
                logger.info("C2Rust-transpiled code:\n```rust\n" + f.read() + "\n```\n")

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
            verus_info = transformer.transform(acsl_info, temp_dir=args.output)

            # necessary postprocessing such as add the `verus!` macro`
            refactor = Refactor(logger=logger, lang_lib=lang_lib)
            refactor.c2rust_main(file_path=rust_file)

            broadcast_use_lemmas = transformer.visitor.broadcast_inductive_lemmas
            merger = Merger(logger=logger, lang_lib=lang_lib)
            file_to_verify = os.path.join(temp_dir, "verus_input.rs")
            res = merger.merge(
                rust_file=os.path.join(
                    os.path.dirname(rust_file), "refactored_source.rs"
                ),
                verus_info=verus_info,
                broadcast_use_lemmas=broadcast_use_lemmas,
                output_file=file_to_verify,
                is_llm=False,
            )

            # check whether translation misalignment led to specification embeddding failures
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
                Pipeline.copy_file(file_to_verify, success_file_path)
            else:
                verus_fail_files.append(file_path)
                # Copy the file to the verus_fail directory
                # Modify the file name from a '.c' extension to a '.rs' extension
                base, _ = os.path.splitext(file_path)
                new_file_path = base + ".rs"
                fail_file_path = os.path.join(
                    verus_fail_dir, os.path.basename(new_file_path)
                )
                Pipeline.copy_file(file_to_verify, fail_file_path)
            veval.get_error_message()

            cur_verified_func_num, cur_total_func_num = Verus(
                verus_path=verus_path, logger=None
            ).count_success_rate_of_function_level_per_file(
                temp_rust_file_path, file_to_verify, lang_lib
            )
            total_func_num += cur_total_func_num
            verified_func_num += cur_verified_func_num
            os.remove(temp_rust_file_path)

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


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Run the migration framework.")
    parser.add_argument(
        "-l", "--local", action="store_true", help="Run with pre-translated Rust code."
    )
    parser.add_argument(
        "-c", "--c2rust", action="store_true", help="Run with c2rust transpilation."
    )

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

    # temp_dir_path
    parent_dir = os.path.abspath(os.path.join(os.getcwd(), ".."))
    temp_dir = tempfile.mkdtemp(dir=parent_dir)
    input_c = os.path.join(temp_dir, "input.c")
    result_rs = os.path.join(temp_dir, "verus_input.rs")
    source_c = os.path.join(temp_dir, "source.c")
    src_dir = os.path.join(temp_dir, "src")
    os.makedirs(src_dir, exist_ok=True)
    refactored_rs = os.path.join(src_dir, "refactored_source.rs")
    source_rs = os.path.join(src_dir, "source.rs")

    for path in [input_c, result_rs, source_c, refactored_rs, source_rs]:
        with open(path, "w", encoding="utf-8") as f:
            f.write(f"\n")

    temp_dir_path = os.path.abspath(temp_dir)
    # transpiled_rust_dir
    script_path = os.path.abspath(__file__)
    DEFAULT_TRANSLATED_DIR = os.path.abspath(
        os.path.join(script_path, "../../../transpiled_rust")
    )
    args = {
        **paths,
        **model,
        **spec,
        "output": temp_dir_path,
        "tranpiled_rust_dir": DEFAULT_TRANSLATED_DIR,
    }

    cli_args = parser.parse_args()

    # redirect io
    temp_io_file = tempfile.NamedTemporaryFile(mode="w", delete=False)
    temp_io_file_path = temp_io_file.name
    old_stdout = sys.stdout
    sys.stdout = temp_io_file

    try:
        if cli_args.local:
            Pipeline.LLM_main_without_translation(**args)
        elif cli_args.c2rust:
            Pipeline.c2rust_main_with_translation(**args)
        else:
            Pipeline.API_LLM_main_with_translation(**args)
        os.remove(temp_io_file_path)
    except Exception as e:
        sys.stdout = old_stdout
        os.remove(temp_io_file_path)
        sys.stdout.write(traceback.format_exc())
