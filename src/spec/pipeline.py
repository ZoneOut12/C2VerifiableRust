import os, argparse, json, shutil, tempfile, sys, traceback, io
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
from src.utils.verus import VEval, Verus
from src.utils.rustc import Rustc
from src.prompt.prompt import transpile_prompt, repair_prompt


class Pipeline:
    def merge_dicts_add(d1, d2):
        merged = d1.copy()
        for key, value in d2.items():
            merged[key] = merged.get(key, 0) + value
        return merged

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

    def copy_file(src, dst):
        """
        Copy the content of file from src to dst.
        src: str, path to the source file
        dst: str, path to the destination file
        """
        with open(src, "rb") as fsrc:
            with open(dst, "wb") as fdst:
                fdst.write(fsrc.read())

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

    def read_dataset_paths(file_path):
        paths = []
        with open(file_path, "r", encoding="utf-8") as f:
            for line in f:
                path = line.strip()
                if path:
                    paths.append(path)
        return paths

    def API_LLM_main_with_translation(**kwargs):
        args = SimpleNamespace(**kwargs)

        lang_lib = args.lang_lib
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

        transform_error_files = {}
        verus_success_files = []
        verus_fail_files = []
        total_func_num = 0
        verified_func_num = 0

        # local_llm = args.local_llm_path
        api_key = args.api_key
        transpiler = Transpiler(model="", logger=logger)

        repair_round_threshold = int(args.repair_round_threshold)
        rustc_fail_list = []
        transpiled_fail_to_compile_num = 0
        transpiled_total_num = 0
        is_first_compile = True

        missing_spec_files = {}
        non_migratable_files = []

        transform_error_counter = TransformErrorCounter()
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

            extrator = SpecExtractor(logger=logger, lang_lib=lang_lib)

            # check if the file is supported by SpecTransformer.
            spec_detector = SpecDetector()
            if not spec_detector.check_file_supported(file_path, lang_lib):
                non_migratable_files.append(file_path)
                continue

            try:
                acsl_info, code_with_assert = extrator.llm_extract_and_replace(
                    processed_file
                )
            except MyException as e:
                transform_error = TransformError.GhostCode
                logger.error(
                    f'"{file_path}" failed in SpecTransformer!\nTransformError type: {transform_error}\n'
                )
                tmp_dict = Pipeline.transform_error_dict(transform_error)
                transform_error_counter = Pipeline.merge_dicts_add(
                    transform_error_counter, tmp_dict
                )
                # transform_error_counter.update(transform_error)
                if str(transform_error) not in transform_error_files:
                    transform_error_files[str(transform_error)] = [file_path]
                else:
                    transform_error_files[str(transform_error)].append(file_path)
                continue

            # run C2Rust to transpile
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
                "model_name": args.api_model,
                "base_url": args.base_url if args.base_url else None,
                "temperature": float(args.temperature),
                "max_tokens": int(args.max_tokens),
                "top_p": float(args.top_p),
            }
            llm_res = transpiler.openai_transpile(
                file_path=temp_file, prompt=transpile_prompt(code_with_assert), **params
            )
            rust_file = os.path.join(temp_dir, "src/source.rs")
            transpiled_res = transpiler.postprocess(llm_res, output_file=rust_file)

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

                    repaired_res = transpiler.postprocess(
                        llm_res, output_file=rust_file
                    )
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
            if transformer.return_code == -1:
                transform_error = transformer.error_type
                logger.error(
                    f'"{file_path}" failed in SpecTransformer!\nTransformError type: {transform_error}\n'
                )
                tmp_dict = Pipeline.transform_error_dict(transform_error)
                transform_error_counter = Pipeline.merge_dicts_add(
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
                    os.path.dirname(rust_file), "refactored_source.rs"
                ),
                verus_info=verus_info,
                output_file=file_to_verify,
                is_llm=True,
            )

            missed_specs = merger.get_unmerged_specs()
            if len(missed_specs) > 0:
                missing_spec_files[debug_info["filename"]] = [
                    len(missed_specs),
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

        # Print the statistics about non-migratable specifications
        # non_migratable_count = transform_error_counter.get_counts()
        # non_migratable_count.pop("UnsupportedType", None)
        # non_migratable_count.pop("ParamIsPointerType", None)
        # logger.error(
        #     f"Collected statistics on the first non-migratable specification type encountered in each file containing unsupported specifications:\n{non_migratable_count}\n"
        # )
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

    def Local_LLM_main_with_translation(**kwargs):
        args = SimpleNamespace(**kwargs)

        lang_lib = args.lang_lib
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

        transform_error_files = {}
        verus_success_files = []
        verus_fail_files = []
        total_func_num = 0
        verified_func_num = 0

        local_llm = args.local_llm_path
        transpiler = Transpiler(model=local_llm, logger=logger)

        repair_round_threshold = int(args.repair_round_threshold)
        rustc_fail_list = []
        transpiled_fail_to_compile_num = 0
        transpiled_total_num = 0
        is_first_compile = True

        missing_spec_files = {}
        non_migratable_files = []

        transform_error_counter = TransformErrorCounter()
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

            extrator = SpecExtractor(logger=logger, lang_lib=lang_lib)

            # check if the file is supported by SpecTransformer.
            spec_detector = SpecDetector()
            if not spec_detector.check_file_supported(file_path, lang_lib):
                non_migratable_files.append(file_path)
                continue

            try:
                acsl_info, code_with_assert = extrator.llm_extract_and_replace(
                    processed_file
                )
            except MyException as e:
                transform_error = TransformError.GhostCode
                logger.error(
                    f'"{file_path}" failed in SpecTransformer!\nTransformError type: {transform_error}\n'
                )
                tmp_dict = Pipeline.transform_error_dict(transform_error)
                transform_error_counter = Pipeline.merge_dicts_add(
                    transform_error_counter, tmp_dict
                )
                # transform_error_counter.update(transform_error)
                if str(transform_error) not in transform_error_files:
                    transform_error_files[str(transform_error)] = [file_path]
                else:
                    transform_error_files[str(transform_error)].append(file_path)
                continue

            # run C2Rust to transpile
            temp_file = os.path.join(temp_dir, "source.c")
            code_with_assert = code_with_assert.strip()
            with open(temp_file, "w") as f:
                f.write(code_with_assert)

            ClangFormatter().format_file(temp_file)
            logger.info(
                f'Source C code, whose `assert` ACSL annotations have been replaced with `// verus_assert(id)`, has been written to "{temp_file}":\n```c\n{code_with_assert}\n```\n'
            )
            params = {
                "temperature": float(args.temperature),
                "max_tokens": int(args.max_tokens),
                "top_p": float(args.top_p),
            }
            llm_res = transpiler.hf_transpile(
                file_path=temp_file, prompt=transpile_prompt(code_with_assert), **params
            )[0]
            rust_file = os.path.join(temp_dir, "src/source.rs")
            transpiled_res = transpiler.postprocess(llm_res, output_file=rust_file)

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

                    llm_res = transpiler.hf_repair(
                        prompt=repair_prompt(
                            c_file=temp_file, rust_file=rust_file, error_msg=errors
                        ),
                        **params,
                    )[0]

                    repaired_res = transpiler.postprocess(
                        llm_res, output_file=rust_file
                    )
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
            if transformer.return_code == -1:
                transform_error = transformer.error_type
                logger.error(
                    f'"{file_path}" failed in SpecTransformer!\nTransformError type: {transform_error}\n'
                )
                tmp_dict = Pipeline.transform_error_dict(transform_error)
                transform_error_counter = Pipeline.merge_dicts_add(
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
                    os.path.dirname(rust_file), "refactored_source.rs"
                ),
                verus_info=verus_info,
                output_file=file_to_verify,
                is_llm=True,
            )

            missed_specs = merger.get_unmerged_specs()
            if len(missed_specs) > 0:
                missing_spec_files[debug_info["filename"]] = [
                    len(missed_specs),
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

        # Print the statistics about non-migratable specifications
        # non_migratable_count = transform_error_counter.get_counts()
        # non_migratable_count.pop("UnsupportedType", None)
        # non_migratable_count.pop("ParamIsPointerType", None)
        # logger.error(
        #     f"Collected statistics on the first non-migratable specification type encountered in each file containing unsupported specifications:\n{non_migratable_count}\n"
        # )
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

    def LLM_main_without_translation(**kwargs):
        args = SimpleNamespace(**kwargs)

        lang_lib = args.lang_lib
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

        transform_error_files = {}
        verus_success_files = []
        verus_fail_files = []
        total_func_num = 0
        verified_func_num = 0

        cache_dir = args.tranpiled_rust_dir
        missing_spec_files = {}
        non_migratable_files = []

        transform_error_counter = TransformErrorCounter()
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

            extrator = SpecExtractor(logger=logger, lang_lib=lang_lib)

            # check if the file is supported by SpecTransformer.
            spec_detector = SpecDetector()
            if not spec_detector.check_file_supported(file_path, lang_lib):
                non_migratable_files.append(file_path)
                continue

            try:
                acsl_info, code_with_assert = extrator.llm_extract_and_replace(
                    processed_file
                )
            except MyException as e:
                transform_error = TransformError.GhostCode
                logger.error(
                    f'"{file_path}" failed in SpecTransformer!\nTransformError type: {transform_error}\n'
                )
                tmp_dict = Pipeline.transform_error_dict(transform_error)
                transform_error_counter = Pipeline.merge_dicts_add(
                    transform_error_counter, tmp_dict
                )
                if str(transform_error) not in transform_error_files:
                    transform_error_files[str(transform_error)] = [file_path]
                else:
                    transform_error_files[str(transform_error)].append(file_path)
                continue

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
            if transformer.return_code == -1:
                transform_error = transformer.error_type
                logger.error(
                    f'"{file_path}" failed in SpecTransformer!\nTransformError type: {transform_error}\n'
                )
                tmp_dict = Pipeline.transform_error_dict(transform_error)
                transform_error_counter = Pipeline.merge_dicts_add(
                    transform_error_counter, tmp_dict
                )
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
                    os.path.dirname(rust_file), "refactored_source.rs"
                ),
                verus_info=verus_info,
                output_file=file_to_verify,
                is_llm=True,  # llm
            )

            missed_specs = merger.get_unmerged_specs()
            if len(missed_specs) > 0:
                missing_spec_files[debug_info["filename"]] = [
                    len(missed_specs),
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
        # non_migratable_count = transform_error_counter.get_counts()
        # non_migratable_count.pop("UnsupportedType", None)
        # non_migratable_count.pop("ParamIsPointerType", None)
        # logger.error(
        #     f"Collected statistics on the first non-migratable specification type encountered in each file containing unsupported specifications:\n{non_migratable_count}\n"
        # )
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


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Verified C2Rust Translation Tool!")
    parser.add_argument(
        "dataset_txt",
        help="Txt file which contains all the C file paths to be translated",
    )
    parser.add_argument(
        "output",
        help="Directory which stores generated intermediate files during processing",
    )
    parser.add_argument("verus", help="Verus path to be set")
    parser.add_argument("lang_lib", help="Tree-sitter language library path to be set")
    parser.add_argument("log_file", help="Log file path to be set")
    parser.add_argument(
        "result_dir",
        help="Directory which stores the final Rust codes",
    )
    parser.add_argument(
        "repair_round_threshold",
        help="Repair round threshold to be set",
    )
    parser.add_argument(
        "mode",
        help="C-to-Rust translation mode: 'cached' (use pre-translated files), 'local' (use local LLM), or 'api' (call LLM via API)",
    )
    parser.add_argument(
        "local_llm_path",
        help="Model path to be set",
    )
    parser.add_argument(
        "api_key",
        help="API Key to access LLM via OpenAI",
    )
    parser.add_argument(
        "api_model",
        help="Model name for the OpenAI API",
    )
    parser.add_argument(
        "base_url",
        type=str,
        help="Optional base URL for the LLM API (e.g., for non-Open AI endpoints)",
    )
    parser.add_argument(
        "temperature",
        type=float,
        default=0.2,
        help="Sampling temperature for the language model (default: 0.2)",
    )

    parser.add_argument(
        "max_tokens",
        type=int,
        default=2048,
        help="Maximum number of tokens to generate (default: 2048)",
    )

    parser.add_argument(
        "top_p",
        type=float,
        default=0.7,
        help="Top-p sampling parameter for nucleus sampling (default: 0.7)",
    )

    parser.add_argument(
        "tranpiled_rust_dir",
        help="Directory where the transpiled Rust files are cached (for 'cached' mode only)",
    )

    parser.add_argument(
        "type_guidance",
        type=str,
        help="Enable or disable type guidance (true or false), default is true",
    )

    args = parser.parse_args()
    mode = args.mode if hasattr(args, "mode") else "cached"
    all_args = vars(args)
    filtered_args = {k: v for k, v in all_args.items() if k != "mode"}
    temp_io_file = tempfile.NamedTemporaryFile(mode="w", delete=False)
    temp_io_file_path = temp_io_file.name
    old_stdout = sys.stdout
    sys.stdout = temp_io_file
    try:
        if mode == "cached":
            Pipeline.LLM_main_without_translation(**filtered_args)
        elif mode == "local":
            Pipeline.Local_LLM_main_with_translation(**filtered_args)
        elif mode == "api":
            Pipeline.API_LLM_main_with_translation(**filtered_args)
        os.remove(temp_io_file_path)
    except Exception as e:
        sys.stdout = old_stdout
        os.remove(temp_io_file_path)
        sys.stdout.write(traceback.format_exc())
        sys.exit(99)
