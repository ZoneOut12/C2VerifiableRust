import subprocess, json, re


class Rustc:
    def __init__(self):
        pass

    def execute(self, file_path: str) -> tuple[bool, list[str]]:
        """
        Compile the Rust file using rustc with JSON output.
        Returns:
            - (True, []) if compiles successfully or only has E0601 (`main` not found)
            - (False, [list of rendered error messages]) otherwise
        """
        result = subprocess.run(
            ["rustc", "--emit=metadata", "--error-format=json", file_path],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
        )

        if result.returncode == 0:
            return True, []

        non_main_errors = []
        main_error_present = False
        for line in result.stderr.strip().splitlines():
            try:
                diagnostic = json.loads(line)
                if (
                    diagnostic.get("level") == "error"
                    and diagnostic.get("$message_type") == "diagnostic"
                ):
                    code_info = diagnostic.get("code")
                    code = code_info.get("code") if code_info else None
                    if code != "E0601":  # Not 'missing main' error
                        rendered = diagnostic.get("rendered", "").strip()
                        if main_error_present:
                            match = re.search(
                                r"aborting due to (\d+) previous error", rendered
                            )
                            if match:
                                number = int(match.group(1))
                                if number > 1:
                                    # subtract number by 1 inside `render`` string
                                    rendered = re.sub(
                                        r"aborting due to (\d+) previous error",
                                        lambda m: f"aborting due to {int(m.group(1)) - 1} previous error"
                                        + ("s" if int(m.group(1)) - 1 != 1 else ""),
                                        rendered,
                                    )
                                else:
                                    rendered = None
                        if rendered:
                            non_main_errors.append(rendered)
                    else:
                        main_error_present = True
            except json.JSONDecodeError:
                continue  # skip invalid JSON lines

        if len(non_main_errors) == 0:
            return True, []
        else:
            error_msg = "\n".join(non_main_errors)
            return False, error_msg


if __name__ == "__main__":
    pass
