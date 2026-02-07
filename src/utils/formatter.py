import subprocess, sys


class AttrDict(dict):
    def __getattr__(self, name):
        return self[name]


class ClangFormatter:
    def __init__(self):
        pass

    def format_file(self, file_path: str, in_place: bool = True) -> str:
        """
        Format a single C file
        :param file_path: The path to the C file to be formatted
        :param in_place: Whether to modify the original file (if False, only return the formatted result)
        :return: The formatted code as a string (if in_place is False)
        """
        cmd = ["clang-format"]
        if in_place:
            cmd.append("-i")
        cmd.append(file_path)

        result = subprocess.run(cmd, capture_output=True, text=True)
        if result.returncode != 0:
            raise RuntimeError(f"clang-format failed: {result.stderr}")
        return result.stdout if not in_place else ""


class VerusFmt:
    def __init__(self, logger):
        self.logger = logger
        pass

    def run(self, input_file):
        """
        run 'verus-fmt' command to format Rust code
        """
        try:
            cmd = ["verusfmt", input_file]
            result = subprocess.run(
                cmd, capture_output=True, text=True, check=True, encoding="utf-8"
            )
            if result.stderr:
                self.logger.error(f"VerusFmt error:\n{result.stderr}\n")
                # sys.exit(1)
            self.logger.info(f"VerusFmt runs successfully. {result.stdout}\n")
        except subprocess.CalledProcessError as e:
            self.logger.error(f"VerusFmt failed to run:\n{e.stderr}\n")


class C2Rust:
    def __init__(self, logger):
        self.logger = logger
        pass

    def transpile(self, input_file, output_dir=None, **args):
        try:
            if not output_dir:
                cmd = ["c2rust", "transpile", "--overwrite-existing", input_file]
                result = subprocess.run(
                    cmd, capture_output=True, text=True, check=True, encoding="utf-8"
                )
                if result.stderr and result.returncode != 0:
                    self.logger.error(f"C2Rust error:\n{result.stderr}\n")
                    sys.exit(1)
                self.logger.info(f"C2Rust runs successfully: {result.stdout}\n")
            else:
                cmd = [
                    "c2rust",
                    "transpile",
                    "--overwrite-existing",
                    "-o",
                    output_dir,
                    input_file,
                ]
                result = subprocess.run(
                    cmd, capture_output=True, text=True, check=True, encoding="utf-8"
                )
                if result.stderr and result.returncode != 0:
                    self.logger.error(
                        f'C2Rust error when transpiling "{args["filename"]}":\n{result.stderr}\n'
                    )
                    sys.exit(1)
                self.logger.info(f"C2Rust runs successfully: {result.stdout}\n")
        except subprocess.CalledProcessError as e:
            self.logger.error(
                f'C2Rust failed to run when transpiling "{args["filename"]}":\n{e.stderr}\n'
            )
            sys.exit(1)


if __name__ == "__main__":
    pass
