import os, json, re, sys, shutil, traceback, tempfile, subprocess
from pathlib import Path
from tree_sitter import Language, Parser


class VEval:
    verus_errors_dict = {}
    rustc_errors_dict = {}
    total_number = 0
    success_number = 0

    def __init__(self, verus_path, logger):
        self.logger = logger
        # rustc reports multiple errors in multiple JSON objects to stderr.
        self.rustc_result = []

        # List "verus_errors" contains both compilation bugs and verification bugs, while List "rustc_errors" only contains compilation bugs.
        self.verus_errors = []
        self.rustc_errors = []
        self.verus_path = verus_path

        # self.compilation_error = False
        self.rustc_out = ""
        self.verus_out = ""
        self.compile_error_list = []
        self.verify_error_list = []

    # Run verus on the code and parse the output.
    def eval(
        self, rust_file, max_errs=8, json_mode=True, func_name=None, **args
    ) -> bool:
        with open(rust_file, "r") as f:
            self.code = f.read()
        with tempfile.NamedTemporaryFile(mode="w", delete=False) as f:
            f.write(self.code)
            code_path = f.name

        # run "verus" with "-V no-solver-version-check -V cvc5" options.
        err_format_args = ["--output-json", "--error-format=json"] if json_mode else []
        cmd_check = (
            [self.verus_path, "-V", "no-solver-version-check", "-V", "cvc5"]
            + err_format_args
            + [code_path]
        )
        result_check = subprocess.run(cmd_check, capture_output=True, text=True)

        if result_check.returncode != 0:
            # run "verus" with default SMT solver z3.
            multiple_errors = f"--multiple-errors {max_errs}" if max_errs > 0 else ""
            err_format = "--output-json --error-format=json" if json_mode else ""

            cmd = (f"{self.verus_path} {multiple_errors} {err_format}").split(" ")
            cmd += [code_path]
            if func_name:
                cmd += ["--verify-function", func_name, "--verify-root"]
            # self.logger.info(f"Running command: {cmd}")
            m = subprocess.run(cmd, capture_output=True, text=True)
            verus_out = m.stdout
            rustc_out = m.stderr
        else:
            verus_out = result_check.stdout
            rustc_out = result_check.stderr

        os.unlink(code_path)

        # self.logger.info("Verus stdout(Json format):\n" + verus_out)
        # self.logger.info("Verus stderr(Json format):\n" + rustc_out)

        verifier = Verus(verus_path=self.verus_path, logger=self.logger)
        return_code, _ = verifier.verify(rust_file=rust_file, **args)

        if return_code == 0:
            self.success_number += 1
        else:
            c_source_file = args["filename"].split("/")[-1]
            base, _ = os.path.splitext(c_source_file)
            new_file_path = base + ".rs"

            # Judge which error type(rustc, or verus) the verifier has met.
            ret_code, compile_err_msgs = verifier.run_with_no_verify(
                rust_file=rust_file, max_errs=8, **args
            )
            if ret_code == -1:
                self.compile_error_list.append(new_file_path)
                # update `self.rustc_errors`
                for compile_err_msg in compile_err_msgs.split("\n")[:-1]:
                    try:
                        e = json.loads(compile_err_msg)
                    except json.JSONDecodeError as e:
                        continue
                    if not isinstance(e, dict):
                        self.logger.error(f"Unexpected rust err output: {e}")
                        continue
                    if "level" in e and e["level"] == "error":
                        if "message" in e and "aborting due to" not in e["message"]:
                            self.rustc_errors.append(e)
            else:
                self.verify_error_list.append(new_file_path)

        self.total_number += 1

        self.verus_out = verus_out
        self.rustc_out = rustc_out

        if not json_mode:
            return

        for rust_err in rustc_out.split("\n")[:-1]:
            try:
                e = json.loads(rust_err)
            except json.JSONDecodeError as e:
                continue
            if not isinstance(e, dict):
                self.logger.error(f"Unexpected rust err output: {e}")
                continue
            self.rustc_result.append(e)
            if "level" in e and e["level"] == "error":
                if "message" in e and "aborting due to" not in e["message"]:
                    self.verus_errors.append(e)

        if return_code == 0:
            return True
        else:
            return False

    def get_verus_error_message(self, repeat=False):
        """
        Param "repeat=False" means the same error message in the same file can only be counted once.
        """
        error_set = set()
        for error in self.verus_errors:
            if "message" in error:
                error_ms = error["message"]
                msg = re.sub(r"`[^`]*`", "`TODO`", error_ms)
                if not repeat:
                    if msg not in error_set:
                        if msg not in self.verus_errors_dict:
                            self.verus_errors_dict[msg] = 0
                        self.verus_errors_dict[msg] += 1
                        error_set.add(msg)
                else:
                    if msg not in self.verus_errors_dict:
                        self.verus_errors_dict[msg] = 0
                    self.verus_errors_dict[msg] += 1
            else:
                Exception("No 'message' in Verus error!")
        self.verus_errors = []

    def get_rustc_error_message(self, repeat=False):
        error_set = set()
        for error in self.rustc_errors:
            if "message" in error:
                error_ms = error["message"]
                msg = re.sub(r"`[^`]*`", "`TODO`", error_ms)
                if not repeat:
                    if msg not in error_set:
                        if msg not in self.rustc_errors_dict:
                            self.rustc_errors_dict[msg] = 0
                        self.rustc_errors_dict[msg] += 1
                        error_set.add(msg)
                else:
                    if msg not in self.rustc_errors_dict:
                        self.rustc_errors_dict[msg] = 0
                    self.rustc_errors_dict[msg] += 1
            else:
                Exception("No 'message' in Rustc error!")
        self.rustc_errors = []
        self.rustc_result = []

    def get_error_message(self, repeat=False):
        # Count error types and record them into dictionary.
        self.get_verus_error_message(repeat=repeat)
        self.get_rustc_error_message(repeat=repeat)

    def get_error_statistics(self, verus_output, rustc_output):
        # Write statistics of error messages types into 'verus_output' jsonfile and 'rustc_output' jsonfile respectively.
        sorted_errors = dict(
            sorted(
                self.verus_errors_dict.items(), key=lambda item: item[1], reverse=True
            )
        )

        self.logger.terminal(
            f"\033[1mFile-level Pass Rate: {self.success_number}/{self.total_number}\033[0m\n"
        )

        sorted_errors = dict(
            sorted(
                self.rustc_errors_dict.items(), key=lambda item: item[1], reverse=True
            )
        )


class Verus:
    def __init__(self, verus_path, logger, encoding="utf-8"):
        self.encoding = encoding
        self.command = verus_path
        self.logger = logger
        self.verus_path = os.path.realpath(verus_path)
        self.vstd_path = os.path.realpath(os.path.join(self.verus_path, "./vstd/"))

    def execute(self, rust_file):
        """
        execute the command in terminal
        """
        # rust_file = self.config.output_file
        try:
            # First, run "verus" with "-V no-solver-version-check -V cvc5" options
            check_cmd = f"{self.command} -V no-solver-version-check -V cvc5 {rust_file}"

            result_check = subprocess.run(
                check_cmd,
                shell=True,
                capture_output=True,
                text=True,
                encoding=self.encoding,
            )

            if result_check.returncode != 0:
                # run "verus" with default SMT-solver z3
                result = subprocess.run(
                    self.command + " " + rust_file,
                    shell=True,
                    capture_output=True,
                    text=True,
                    encoding=self.encoding,
                )
                return result.stdout, result.stderr, result.returncode
            else:
                return result_check.stdout, result_check.stderr, result_check.returncode
        except Exception as e:
            self.logger.error(f"Verus failed to run:\n{str(e)}\n")
            return "", str(e), -1

    def verify(self, rust_file, **args):
        """
        Verify the Rust file using Verus"
        """
        stdout, stderr, returncode = self.execute(rust_file)
        if returncode == 0:
            if self.logger:
                self.logger.info(
                    f'Verus verifies successfully.\n[C Source: "{args["filename"]}"]\nVerus output:\n{stdout}\n'
                )
            return 0, stdout
        else:
            if self.logger:
                self.logger.error(
                    f'Verus error when verifying {rust_file}.\n[C Source: "{args["filename"]}"]\nVerus output:\n[stderr]\n{stderr}\n[stdout]\n{stdout}\n'
                )
            return -1, stderr

    def is_compilation_error(self, rust_file):
        """
        Check if the Rust file is a compilation error
        Method:
            1. Run Verus on the Rust file
            2. Check if the Verus output contains "verification results:: %d verified, %d errors"
        """
        stdout, stderr, returncode = self.execute(rust_file)
        pattern = r"verification results:: (\d+) verified, (\d+) errors"
        match = re.search(pattern, stdout)
        if match:
            verified = int(match.group(1))
            errors = int(match.group(2))
            return False
        else:
            return True

    def run_with_no_verify(self, rust_file, max_errs=8, **args):
        """
        Run Verus with --no-verify to check whether rust_file could pass syntax and type checks.
        Output format is set to Json.
        """
        try:
            multiple_errors = f"--multiple-errors {max_errs}" if max_errs > 0 else ""
            cmd = f"{self.command} --no-verify {multiple_errors} --output-json --error-format=json {rust_file}"
            result = subprocess.run(
                cmd,
                shell=True,
                capture_output=True,
                text=True,
                encoding=self.encoding,
            )
            if result.returncode == 0:
                return 0, result.stdout
            else:
                return -1, result.stderr
        except Exception as e:
            self.logger.error(f"Verus --no-verify failed to run:\n{str(e)}\n")
            return -1, str(e)

    def collect_error_messages_in_verus_fail(self, root_dir, repeat=False, max_errs=8):
        """
        Verify all the ".rs" files in root_dir(.../verus_fail), and collect error messages.
        """
        rs_files = list(Path(root_dir).rglob("*.rs"))
        compile_bugs_dict = {}
        verify_bugs_dict = {}
        for rust_file in rs_files:
            try:
                with tempfile.NamedTemporaryFile(
                    delete=False, mode="w+", encoding="utf-8"
                ) as tmp_file:
                    shutil.copyfileobj(open(rust_file, "r", encoding="utf-8"), tmp_file)
                    temp_path = tmp_file.name
                compile_bugs_set = set()
                verify_bugs_set = set()
                multiple_errors = (
                    f"--multiple-errors {max_errs}" if max_errs > 0 else ""
                )
                cmd = f"{self.command} --no-verify {multiple_errors} --output-json --error-format=json {temp_path}"
                result = subprocess.run(
                    cmd,
                    shell=True,
                    capture_output=True,
                    text=True,
                    encoding=self.encoding,
                )
                if result.returncode == 0:
                    cmd = f"{self.command} {multiple_errors} --output-json --error-format=json {temp_path}"
                    result = subprocess.run(
                        cmd,
                        shell=True,
                        capture_output=True,
                        text=True,
                        encoding=self.encoding,
                    )
                    if result.returncode == 0:
                        continue
                    else:
                        for verus_err in result.stderr.split("\n")[:-1]:
                            try:
                                e = json.loads(verus_err)
                            except json.JSONDecodeError as e:
                                continue
                            if not isinstance(e, dict):
                                print(f"Unexpected rust err output: {e}")
                                sys.exit(1)
                                continue
                            if "level" in e and e["level"] == "error":
                                if (
                                    "message" in e
                                    and "aborting due to" not in e["message"]
                                ):
                                    error_ms = e["message"]
                                    msg = re.sub(r"`[^`]*`", "`TODO`", error_ms)
                                    if not repeat:
                                        if msg not in verify_bugs_set:
                                            if msg not in verify_bugs_dict:
                                                verify_bugs_dict[msg] = 0
                                            verify_bugs_dict[msg] += 1
                                            verify_bugs_set.add(msg)
                                    else:
                                        if msg not in verify_bugs_dict:
                                            verify_bugs_dict[msg] = 0
                                        verify_bugs_dict[msg] += 1
                else:
                    for verus_err in result.stderr.split("\n")[:-1]:
                        try:
                            e = json.loads(verus_err)
                        except json.JSONDecodeError as e:
                            continue
                        if not isinstance(e, dict):
                            print(f"Unexpected rust err output: {e}")
                            sys.exit(1)
                            continue
                        if "level" in e and e["level"] == "error":
                            if "message" in e and "aborting due to" not in e["message"]:
                                error_ms = e["message"]
                                msg = re.sub(r"`[^`]*`", "`TODO`", error_ms)
                                if not repeat:
                                    if msg not in compile_bugs_set:
                                        if r"""mismatched types""" in msg:
                                            print(rust_file)
                                        if msg not in compile_bugs_dict:
                                            compile_bugs_dict[msg] = 0
                                        compile_bugs_dict[msg] += 1
                                        compile_bugs_set.add(msg)
                                else:
                                    if msg not in compile_bugs_dict:
                                        compile_bugs_dict[msg] = 0
                                    compile_bugs_dict[msg] += 1
                os.remove(temp_path)
            except Exception as e:
                print(traceback.format_exc())
                print(f"Verus failed to run: {e}")
                sys.exit(1)
        sorted_compile_bugs_dict = dict(
            sorted(compile_bugs_dict.items(), key=lambda item: item[1], reverse=True)
        )
        sorted_verify_bugs_dict = dict(
            sorted(verify_bugs_dict.items(), key=lambda item: item[1], reverse=True)
        )
        print(json.dumps(sorted_compile_bugs_dict, indent=2))
        print(json.dumps(sorted_verify_bugs_dict, indent=2))

    def verify_file_in_function_level(self, rust_file, func_name):
        specify_func_cmd = f" --verify-function {func_name} --verify-root"
        try:
            # First, run "verus" with "-V no-solver-version-check -V cvc5" options
            check_cmd = f"{self.command} -V no-solver-version-check -V cvc5 {rust_file}"

            result_check = subprocess.run(
                check_cmd + specify_func_cmd,
                shell=True,
                capture_output=True,
                text=True,
                encoding=self.encoding,
            )

            if result_check.returncode != 0:
                # run "verus" with default SMT-solver z3
                result = subprocess.run(
                    self.command + " " + rust_file + specify_func_cmd,
                    shell=True,
                    capture_output=True,
                    text=True,
                    encoding=self.encoding,
                )
                return result.stdout, result.stderr, result.returncode
            else:
                return result_check.stdout, result_check.stderr, result_check.returncode
        except Exception as e:
            self.logger.error(f"Verus failed to run:\n{str(e)}\n")
            return "", str(e), -1

    def find_files_by_name(self, directory, file_name):
        for root, _, files in os.walk(directory):
            for file in files:
                if file == file_name:
                    absolute_path = os.path.abspath(os.path.join(root, file))
                    return absolute_path

        raise FileNotFoundError(f"File {file_name} not found in directory {directory}")

    def get_all_files_in_directory(self, directory):
        file_paths_and_names = []

        for root, _, files in os.walk(directory):
            for file in files:
                absolute_path = os.path.abspath(os.path.join(root, file))
                file_name = file
                file_paths_and_names.append((absolute_path, file_name))

        return file_paths_and_names

    def count_success_rate_of_file_level(self, directory):
        file_paths_and_names = self.get_all_files_in_directory(directory)
        total_verified_file_num = 0
        total_file_name = 0
        for file_path, file_name in file_paths_and_names:
            total_file_name += 1
            with open(file_path, "r") as original_file:
                content = original_file.read()

            with tempfile.NamedTemporaryFile(
                delete=False, mode="w", newline="", encoding="utf-8"
            ) as temp_file:
                temp_file.write(content)
                temp_file_path = temp_file.name

            returncode, _ = self.verify(rust_file=temp_file_path)
            if returncode == 0:
                print(f"{file_name}")
                total_verified_file_num += 1
            os.remove(temp_file_path)
        print(
            f"Total verified file number: {total_verified_file_num}/{total_file_name}"
        )
        print(f"Total file number: {total_file_name}")

    def count_success_rate_of_function_level_per_file(
        self, translated_rust_file, verus_file, lang_lib
    ):
        """Return total_verified_func_num and total_func_name"""
        total_verified_func_num = 0
        total_func_name = 0
        with open(translated_rust_file, "r") as f:
            source_code = f.read().encode("utf8")
        RUST_LANGUAGE = Language(lang_lib, "rust")
        parser = Parser()
        parser.set_language(RUST_LANGUAGE)
        tree = parser.parse(source_code)
        root_node = tree.root_node
        function_names = []

        def extract_functions(node):
            if node.type == "function_item":
                for child in node.children:
                    if child.type == "identifier":
                        function_names.append(child.text.decode("utf-8"))

            for child in node.children:
                extract_functions(child)

        extract_functions(root_node)

        with open(verus_file, "r") as original_file:
            content = original_file.read()

        with tempfile.NamedTemporaryFile(
            delete=False, mode="w", newline="", encoding="utf-8"
        ) as temp_file:
            temp_file.write(content)
            temp_file_path = temp_file.name

        for func_name in function_names:
            total_func_name += 1
            _, _, returncode = self.verify_file_in_function_level(
                rust_file=temp_file_path, func_name=func_name
            )
            if returncode == 0:
                total_verified_func_num += 1

        os.remove(temp_file_path)
        return total_verified_func_num, total_func_name

    def count_success_rate_of_function_level(
        self,
        directory,
        lang_lib,
        translated_dir,
    ):
        file_paths_and_names = self.get_all_files_in_directory(directory)
        total_verified_func_num = 0
        total_func_name = 0
        total_file_name = 0
        for file_path, file_name in file_paths_and_names:
            total_file_name += 1
            base_name, ext = os.path.splitext(file_name)
            # replace '.' with '_' in file name
            base_name = base_name.replace(".", "_")
            new_file_name = base_name + ext
            translated_rust_file = self.find_files_by_name(
                directory=translated_dir, file_name=new_file_name
            )

            with open(translated_rust_file, "r") as f:
                source_code = f.read().encode("utf8")
            RUST_LANGUAGE = Language(lang_lib, "rust")
            parser = Parser()
            parser.set_language(RUST_LANGUAGE)
            tree = parser.parse(source_code)
            root_node = tree.root_node
            function_names = []

            def extract_functions(node):
                if node.type == "function_item":
                    for child in node.children:
                        if child.type == "identifier":
                            function_names.append(child.text.decode("utf-8"))

                for child in node.children:
                    extract_functions(child)

            extract_functions(root_node)

            with open(file_path, "r") as original_file:
                content = original_file.read()

            with tempfile.NamedTemporaryFile(
                delete=False, mode="w", newline="", encoding="utf-8"
            ) as temp_file:
                temp_file.write(content)
                temp_file_path = temp_file.name

            for func_name in function_names:
                total_func_name += 1
                _, _, returncode = self.verify_file_in_function_level(
                    rust_file=temp_file_path, func_name=func_name
                )
                if returncode == 0:
                    total_verified_func_num += 1
                # else:
                #     print(f"Failed to verify function {func_name} in file {file_path}")
            os.remove(temp_file_path)
        print(f"Total file number: {total_file_name}")
        print(
            f"Total verified function number: {total_verified_func_num}/{total_func_name}"
        )
        return total_verified_func_num / total_func_name

    def obtain_rust_files_with_message_output(self, directory, message):
        count = 0
        normalized_message = re.sub(r"\s+", "", message)

        for filename in os.listdir(directory):
            file_path = os.path.join(directory, filename)
            if filename.endswith(".rs") and os.path.isfile(file_path):
                with tempfile.NamedTemporaryFile(delete=False) as temp_file:
                    with open(file_path, "r") as f:
                        temp_file.write(f.read().encode("utf-8"))

                    temp_file_path = temp_file.name
                try:
                    max_errs = 8
                    multiple_errors = (
                        f"--multiple-errors {max_errs}" if max_errs > 0 else ""
                    )
                    result = subprocess.run(
                        self.command + f" {multiple_errors} " + temp_file_path,
                        shell=True,
                        capture_output=True,
                        text=True,
                    )

                    normalized_stderr = re.sub(r"\s+", "", result.stderr)

                    if normalized_message in normalized_stderr:
                        # if message in result.stderr:
                        print(f"Error in file: {filename}")
                        count += 1

                except subprocess.CalledProcessError as e:
                    print(f"Error running Verus on {filename}: {e}")

        print(f"Total files with error message '{message}': {count}")


if __name__ == "__main__":
    project_root_dir = os.path.abspath(
        os.path.join(os.path.dirname(__file__), "..", "..")
    )
    fixed_dir = os.path.join(project_root_dir, "./result_improve/fix_verus_fail")
    verus_fail_dir = os.path.join(project_root_dir, "./result/verus_fail")
    lang_lib = os.path.join(project_root_dir, "./src/spec/build/my-languages.so")
    translated_dir = os.path.join(project_root_dir, "transpiled_rust")
    Verus(
        verus_path="~/verus-x86-linux/verus", logger=None
    ).count_success_rate_of_function_level(verus_fail_dir, lang_lib, translated_dir)
    pass
