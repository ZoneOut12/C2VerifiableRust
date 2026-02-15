"""
C-to-Rust transpilation WITH ACSL annotations as context.

Usage:
    python -m src.c2rust.transpile_with_spec
"""

from openai import OpenAI
import os
import re
import json
import argparse
import tempfile
import tomllib
from src.spec.extract import SpecExtractor
from src.utils.formatter import ClangFormatter
from src.utils.rustc import Rustc
from src.utils.logger import Logger


# ACSL keywords/syntax that should NEVER appear in Rust output
ACSL_LEAK_PATTERNS = [
    r"\\forall\b",
    r"\\exists\b",
    r"\\result\b",
    r"\\valid\b",
    r"\\valid_read\b",
    r"\\separated\b",
    r"\\old\b",
    r"\\nothing\b",
    r"\\at\b",
    r"\bassigns\b",
    r"\bloop\s+invariant\b",
    r"\bloop\s+variant\b",
    r"\bloop\s+assigns\b",
    r"\brequires\b",
    r"\bensures\b",
    r"/\*@",
    r"//@",
]


def transpile_prompt_with_spec(original_code: str, code_with_placeholder: str) -> str:
    """
    Carefully separated prompt.
    Provides ACSL for context, but translates the placeholder version.
    """
    prompt = f"""You are an expert C-to-Rust translator with deep knowledge of formal verification.

## Task Overview

You are given a C program with ACSL (ANSI/ISO C Specification Language) formal specifications. Your task is to translate it to safe, idiomatic Rust code. **Use the ACSL specifications to guide your translation decisions.**

## Input 1: Original C Code with ACSL Specifications

```c
{original_code}
```

## Input 2: C Code to Translate (with placeholder comments)

The ACSL annotations have been replaced with `// verus_assert(id);` placeholders. You must preserve these placeholders in your Rust output.

```c
{code_with_placeholder}
```

---

## How to Use ACSL Specifications

ACSL specifications provide crucial information for making correct translation decisions:

### 1. Mutability from `assigns` clause

The `assigns` clause specifies which memory locations a function may modify. Variables or memory regions listed in `assigns` **must** be translated with `mut` in Rust:

- `assigns \\nothing;` -> All pointer parameters should be `&T` or `&[T]` (immutable)
- `assigns *ptr;` -> The pointer is modified, use `&mut T`
- `assigns arr[0..n-1];` -> The array is modified, use `&mut [T]`

**Example:**
```c
/*@ assigns arr[0..n-1]; */
void fill(int *arr, int n, int val);
```
-> `fn fill(arr: &mut [i32], n: i32, val: i32)`

### 2. Mutability from `\\valid()` vs `\\valid_read()`

- `requires \\valid(ptr + (0..n-1));` -> The pointer has **write** access, translate as `&mut [T]`
- `requires \\valid_read(ptr + (0..n-1));` -> The pointer has **read-only** access, translate as `&[T]`

In ACSL, `\\valid()` implies both read and write validity, while `\\valid_read()` implies read-only validity. This distinction directly maps to Rust's `&mut` vs `&` references.

**Example:**
```c
/*@
    requires \\valid(dst + (0..n-1));
    requires \\valid_read(src + (0..n-1));
    assigns dst[0..n-1];
*/
void copy(int *dst, const int *src, int n);
```
-> `fn copy(dst: &mut [i32], src: &[i32], n: i32)`

### 3. Pointer separation from `\\separated()`

- `requires \\separated(a + (0..n-1), b + (0..n-1));` -> The two arrays do not overlap in memory. In Rust, this is naturally enforced by the borrow checker when using separate `&mut` and `&` references.

### 4. Preconditions (from `requires` clauses)

- `requires n >= 0;` -> Parameter constraint (helps understand valid input range)
- `requires \\forall k1, k2; 0 <= k1 < k2 < n ==> arr[k1] <= arr[k2];` -> Array is sorted

### 5. Return Value (from `ensures` clauses)

- `ensures \\result >= 0;` -> Return type is non-negative integer
- `ensures \\result == x || \\result == y;` -> Result is one of the inputs

### 6. Loop Invariants (from `loop invariant`)

- Loop invariants help understand the loop's purpose and bounds
- Preserve the loop structure exactly as in C (use `while` loops)

---

## Translation Rules

### Pointer/Array Translation

| C Type | ACSL Hint | Rust Type |
|--------|-----------|-----------|
| `int *arr` | `\\valid(arr + ...)` or `assigns arr[...]` | `&mut [i32]` |
| `int *arr` | `\\valid_read(arr + ...)` or `assigns \\nothing` | `&[i32]` |
| `int *ptr` | `\\valid(ptr)` or `assigns *ptr` | `&mut i32` |
| `int *ptr` | `\\valid_read(ptr)` or read-only | `&i32` |
| `const int *arr` | - | `&[i32]` |

### Loop Translation

Convert ALL `for` loops to `while` loops:
```c
for (int i = 0; i < n; i++) {{{{ ... }}}}
```
->
```rust
let mut i: i32 = 0;
while i < n {{{{
    ...
    i += 1;
}}}}
```

### Placeholder Preservation

The `// verus_assert(id);` comments mark where Verus specifications will be inserted later. **You MUST preserve these comments exactly** at the corresponding locations in the Rust code.

---

## Output Requirements

1. **Preserve structure**: The Rust code should mirror the C code line-by-line
2. **Preserve placeholders**: Keep all `// verus_assert(id);` comments
3. **Use specifications**: Apply ACSL information to make correct mutability decisions
4. **No unsafe**: Avoid `unsafe` blocks unless absolutely necessary
5. **No std imports**: Do not use `use std::...`
6. **Explicit types**: All variables must have explicit type annotations
7. **Format**: Wrap output in ```rust ... ``` code block

---

## Now translate the C code (Input 2) to Rust:

"""
    return prompt


def repair_prompt_with_spec(original_code: str, c_code: str, rust_code: str, error_msg: str) -> str:
    """Repair prompt that also provides ACSL annotations as context."""
    prompt = f"""You are an expert Rust developer fixing compilation errors in automatically translated code.

## Context

This Rust code was translated from a C program with ACSL formal specifications. The ACSL specifications provide important hints about the intended behavior.

### Original C Code with ACSL Specifications:
```c
{original_code}
```

### C Code That Was Translated (with placeholders):
```c
{c_code}
```

### Current Rust Code (has compilation errors):
```rust
{rust_code}
```

### Compilation Errors:
```
{error_msg}
```

---

## Your Task

Fix the compilation errors while:

1. **Preserving the code structure** - Keep the same control flow and logic
2. **Preserving all `// verus_assert(id);` comments** - These are critical placeholders
3. **Using ACSL hints for mutability** - `assigns` and `\\valid()` indicate `&mut`; `\\valid_read()` indicates `&`
4. **Keeping identifiers unchanged** - Do not rename variables or functions
5. **Making minimal changes** - Only fix what's necessary to compile

## Common Fixes

| Error Type | Likely Fix |
|------------|------------|
| "cannot borrow as mutable" | Check `assigns` / `\\valid()` clause - if modified, use `&mut [T]` |
| "mismatched types" | Ensure slice indexing uses `as usize` |
| "cannot find value" | Verify variable declarations and scope |
| "borrow of moved value" | Adjust ownership or use references |

## Output

Provide the corrected Rust code wrapped in ```rust ... ``` code block.
Do not include explanations, only the fixed code.

"""
    return prompt


# =============================================================================
# Output Validator: Detect problems in transpiled Rust code
# =============================================================================

class OutputValidator:
    """
    Validates transpiled Rust code to detect problems.

    Checks for:
    - Placeholder loss (verus_assert markers missing)
    - ACSL syntax leaking into Rust output
    - Structure deviation (extra assert!, debug_assert!, bounds checks)
    """

    @staticmethod
    def count_placeholders(code: str) -> int:
        """Count `// verus_assert(N)` markers in code."""
        return len(re.findall(r"//\s*verus_assert\(\d+\)\s*;?", code))

    @staticmethod
    def detect_acsl_leak(rust_code: str) -> list:
        """
        Detect ACSL syntax that leaked into Rust output.
        Returns list of (pattern, line_number, line_content) tuples.
        """
        leaks = []
        for i, line in enumerate(rust_code.split("\n"), 1):
            # Skip lines that are verus_assert placeholders
            if re.search(r"//\s*verus_assert\(\d+\)", line):
                continue
            for pattern_str in ACSL_LEAK_PATTERNS:
                pattern = re.compile(pattern_str)
                if pattern.search(line):
                    leaks.append((pattern_str, i, line.strip()))
                    break  # one leak per line is enough
        return leaks

    @staticmethod
    def detect_structure_deviation(rust_code: str) -> dict:
        """
        Detect structural additions not present in the original C code.
        """
        issues = {
            "assert_count": len(re.findall(r"\bassert!\s*\(", rust_code)),
            "debug_assert_count": len(re.findall(r"\bdebug_assert!\s*\(", rust_code)),
            "panic_count": len(re.findall(r"\bpanic!\s*\(", rust_code)),
            "option_wrapping": len(re.findall(r"\bOption\s*<", rust_code)),
            "bounds_checks": len(re.findall(
                r"if\s+.*\.len\(\)\s*[<>=]|\.get\s*\(|\.checked_", rust_code
            )),
            "i64_usage": len(re.findall(r"\bi64\b", rust_code)),
            "usize_params": len(re.findall(r"\b\w+:\s*usize\b", rust_code)),
        }
        return issues

    @staticmethod
    def validate(
        c_placeholder_code: str,
        rust_code: str,
        logger,
        c_file_path: str,
    ) -> dict:
        """
        Run all validation checks and return a report dict.
        """
        expected_placeholders = OutputValidator.count_placeholders(c_placeholder_code)
        actual_placeholders = OutputValidator.count_placeholders(rust_code)

        acsl_leaks = OutputValidator.detect_acsl_leak(rust_code)
        structure_issues = OutputValidator.detect_structure_deviation(rust_code)

        report = {
            "file": c_file_path,
            "expected_placeholders": expected_placeholders,
            "actual_placeholders": actual_placeholders,
            "placeholder_loss": expected_placeholders - actual_placeholders,
            "acsl_leak_count": len(acsl_leaks),
            "acsl_leaks": [(p, ln, content) for p, ln, content in acsl_leaks[:10]],
            "structure_deviation": structure_issues,
        }

        # Log warnings
        if report["placeholder_loss"] > 0:
            logger.warning(
                f"[Placeholder Loss] {c_file_path}: "
                f"expected {expected_placeholders} placeholders, "
                f"got {actual_placeholders} "
                f"(lost {report['placeholder_loss']})"
            )

        if acsl_leaks:
            leak_summary = "; ".join(
                f"L{ln}: {content[:60]}" for _, ln, content in acsl_leaks[:5]
            )
            logger.warning(
                f"[ACSL Leak] {c_file_path}: "
                f"{len(acsl_leaks)} ACSL syntax leaks detected: {leak_summary}"
            )

        total_extra = (
            structure_issues["assert_count"]
            + structure_issues["debug_assert_count"]
            + structure_issues["panic_count"]
        )
        if total_extra > 0:
            logger.warning(
                f"[Structure Deviation] {c_file_path}: "
                f"{structure_issues['assert_count']} assert!, "
                f"{structure_issues['debug_assert_count']} debug_assert!, "
                f"{structure_issues['panic_count']} panic!"
            )

        return report


# =============================================================================
# Transpiler class
# =============================================================================

class TranspilerWithSpec:
    """Transpiler that provides ACSL annotations as context during translation."""

    def __init__(self, config: dict, logger, lang_lib: str):
        self.config = config
        self.logger = logger
        self.lang_lib = lang_lib

    def extract_code_block(self, code: str) -> str:
        """Extract Rust code from markdown code block."""
        pattern = re.compile(r"```(?:rust)?\n((?:.|\n)*?)\n?```", re.DOTALL)
        match = pattern.search(code)
        if not match:
            return code
        code_block = match.group(1).strip()
        return code_block if code_block else "\n"

    def openai_transpile(self, original_code: str, code_with_placeholder: str) -> str:
        """Call LLM to translate C code with ACSL as context."""
        api_key = self.config["model"]["api_key"]
        model_name = self.config["model"]["model_name"]
        temperature = self.config["model"].get("temperature", 0.2)
        max_tokens = self.config["model"].get("max_tokens", 2048)
        top_p = self.config["model"].get("top_p", 0.7)
        base_url = self.config["model"].get("base_url")

        prompt = transpile_prompt_with_spec(original_code, code_with_placeholder)
        self.logger.info(f"Transpile prompt:\n{prompt}")

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

        self.logger.info(f"LLM transpiled result:\n{response}")
        return response

    def openai_repair(self, original_code: str, c_code: str, rust_code: str, error_msg: str) -> str:
        """Call LLM to repair compilation errors."""
        api_key = self.config["model"]["api_key"]
        model_name = self.config["model"]["model_name"]
        temperature = self.config["model"].get("temperature", 0.2)
        max_tokens = self.config["model"].get("max_tokens", 2048)
        top_p = self.config["model"].get("top_p", 0.7)
        base_url = self.config["model"].get("base_url")

        prompt = repair_prompt_with_spec(original_code, c_code, rust_code, error_msg)
        self.logger.info(f"Repair prompt:\n{prompt[:1000]}...")

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
            if chunk.choices:
                delta = chunk.choices[0].delta
                if delta.content:
                    response += delta.content

        self.logger.info(f"LLM repaired result:\n{response}")
        return response

    def batch_transpile(self, txt_file_path: str, target_root_dir: str):
        """
        Batch transpile C files WITH ACSL annotations as context.

        Args:
            txt_file_path: Path to the txt file containing C file paths.
            target_root_dir: Root directory for output Rust files.
        """
        repair_round_threshold = self.config["model"].get("repair_round_threshold", 3)

        with open(txt_file_path, "r", encoding="utf-8") as f:
            lines = f.readlines()

        os.makedirs(target_root_dir, exist_ok=True)

        transpiled_fail_to_compile_list = []
        repaired_fail_to_compile_list = []
        compile_success_list = []
        validation_reports = []

        for line in lines:
            c_file_path = line.strip()
            if not c_file_path or not c_file_path.endswith(".c"):
                continue

            self.logger.info(f"Processing {c_file_path}.\n")

            try:
                data_index = c_file_path.rfind("/data/")
            except ValueError:
                self.logger.error(f"Skipped: '/data/' not found in path '{c_file_path}'")
                continue

            relative_path = c_file_path[data_index + len("/data/"):]
            dir_part, c_filename = os.path.split(relative_path)
            rs_filename = os.path.splitext(c_filename)[0].replace(".", "_") + ".rs"

            target_dir = os.path.join(target_root_dir, dir_part)
            os.makedirs(target_dir, exist_ok=True)
            target_file_path = os.path.join(target_dir, rs_filename)

            # Read original C code (with ACSL)
            try:
                with open(c_file_path, "r", encoding="utf-8") as f:
                    original_code = f.read()
            except Exception as e:
                self.logger.error(f"Failed to read {c_file_path}: {e}")
                continue

            # Use SpecExtractor to get code with `// verus_assert(id)` placeholders
            try:
                extractor = SpecExtractor(logger=self.logger, lang_lib=self.lang_lib)
                acsl_info, code_with_placeholder = extractor.llm_extract_and_replace(c_file_path)
            except Exception as e:
                self.logger.error(f"SpecExtractor failed on {c_file_path}: {e}\n")
                continue

            code_with_placeholder = code_with_placeholder.strip()

            # Format the placeholder code
            with tempfile.NamedTemporaryFile(mode="w+", delete=False, suffix=".c") as tmp:
                tmp_path = tmp.name
                tmp.write(code_with_placeholder)
                tmp.flush()

            ClangFormatter().format_file(tmp_path)

            with open(tmp_path, "r", encoding="utf-8") as f:
                code_with_placeholder = f.read()

            self.logger.info(f"Original C code (with ACSL):\n```c\n{original_code}\n```\n")
            self.logger.info(f"C code with placeholders:\n```c\n{code_with_placeholder}\n```\n")

            # Transpile with ACSL as context
            llm_res = self.openai_transpile(original_code, code_with_placeholder)
            transpiled_res = self.extract_code_block(llm_res)

            with open(target_file_path, "w", encoding="utf-8") as f:
                f.write(transpiled_res)

            self.logger.info(f"Transpiled Rust code:\n{transpiled_res}\n")

            # ---- Validate output ----
            report = OutputValidator.validate(
                c_placeholder_code=code_with_placeholder,
                rust_code=transpiled_res,
                logger=self.logger,
                c_file_path=c_file_path,
            )
            validation_reports.append(report)

            # Compilation and repair loop
            is_first_compile = True
            for i in range(repair_round_threshold):
                success, errors = Rustc().execute(file_path=target_file_path)
                if not success:
                    if is_first_compile:
                        transpiled_fail_to_compile_list.append(c_file_path)
                        is_first_compile = False

                    self.logger.warning(f"Repair Round: {i+1}/{repair_round_threshold}\n")

                    # Read current Rust code
                    with open(target_file_path, "r", encoding="utf-8") as f:
                        rust_code = f.read()

                    llm_res = self.openai_repair(original_code, code_with_placeholder, rust_code, errors)
                    repaired_res = self.extract_code_block(llm_res)

                    with open(target_file_path, "w", encoding="utf-8") as f:
                        f.write(repaired_res)
                else:
                    break

            # Final check
            success, errors = Rustc().execute(file_path=target_file_path)
            if not success:
                self.logger.error(
                    f'After {repair_round_threshold} repair rounds, Rustc still failed on "{c_file_path}"!\n'
                )
                repaired_fail_to_compile_list.append(c_file_path)
            else:
                self.logger.info(f'Rustc successfully compiled "{c_file_path}"!\n')
                compile_success_list.append(c_file_path)

                # ---- Re-validate after repair (placeholder may be lost during repair) ----
                with open(target_file_path, "r", encoding="utf-8") as f:
                    final_rust_code = f.read()
                final_report = OutputValidator.validate(
                    c_placeholder_code=code_with_placeholder,
                    rust_code=final_rust_code,
                    logger=self.logger,
                    c_file_path=c_file_path + " (after repair)",
                )
                report["after_repair"] = final_report

            # Clean up temp file
            os.remove(tmp_path)

        # Save results
        jsonfile = os.path.join(target_root_dir, "rustc_result.json")
        data = {
            "transpile_fail": transpiled_fail_to_compile_list,
            "repair_fail": repaired_fail_to_compile_list,
            "compile_success": compile_success_list,
            "total": len([l for l in lines if l.strip().endswith(".c")]),
        }
        with open(jsonfile, "w", encoding="utf-8") as f:
            json.dump(data, f, ensure_ascii=False, indent=4)

        # Save validation report
        validation_file = os.path.join(target_root_dir, "validation_report.json")
        summary = self._summarize_validation(validation_reports)
        with open(validation_file, "w", encoding="utf-8") as f:
            json.dump(
                {"summary": summary, "per_file": validation_reports},
                f, ensure_ascii=False, indent=4, default=str,
            )

        self.logger.info(f"Results saved to {jsonfile}")
        self.logger.info(f"Validation report saved to {validation_file}")
        self.logger.info(
            f"Total: {data['total']}, "
            f"Success: {len(compile_success_list)}, "
            f"Transpile Fail: {len(transpiled_fail_to_compile_list)}, "
            f"Repair Fail: {len(repaired_fail_to_compile_list)}"
        )
        self.logger.info(f"Validation Summary:\n{json.dumps(summary, indent=2)}")

    @staticmethod
    def _summarize_validation(reports: list) -> dict:
        """Aggregate validation metrics across all files."""
        if not reports:
            return {}
        total = len(reports)
        total_placeholder_loss = sum(r["placeholder_loss"] for r in reports)
        files_with_placeholder_loss = sum(1 for r in reports if r["placeholder_loss"] > 0)
        total_acsl_leaks = sum(r["acsl_leak_count"] for r in reports)
        files_with_acsl_leak = sum(1 for r in reports if r["acsl_leak_count"] > 0)
        total_asserts = sum(r["structure_deviation"]["assert_count"] for r in reports)
        total_debug_asserts = sum(r["structure_deviation"]["debug_assert_count"] for r in reports)

        return {
            "total_files": total,
            "placeholder_loss": {
                "total_lost": total_placeholder_loss,
                "files_affected": files_with_placeholder_loss,
                "rate": f"{files_with_placeholder_loss}/{total}",
            },
            "acsl_syntax_leak": {
                "total_leaks": total_acsl_leaks,
                "files_affected": files_with_acsl_leak,
                "rate": f"{files_with_acsl_leak}/{total}",
            },
            "structure_deviation": {
                "total_assert": total_asserts,
                "total_debug_assert": total_debug_asserts,
            },
        }


def main():
    """Main entry point for batch transpilation with ACSL as context."""
    # Load config
    config_path = os.path.join(
        os.path.dirname(os.path.abspath(__file__)), "..", "config.toml"
    )
    with open(config_path, "rb") as f:
        config = tomllib.load(f)

    # Setup logger
    log_dir = os.path.dirname(config["path"]["log_file"])
    os.makedirs(log_dir, exist_ok=True)
    log_file = config["path"]["log_file"].replace(".log", "_with_spec.log")
    logger = Logger(log_file).setup_logger(overwrite=True)

    # Setup lang_lib path
    script_dir = os.path.dirname(os.path.abspath(__file__))
    lang_lib = os.path.abspath(os.path.join(script_dir, "../spec/build/my-languages.so"))

    # Setup paths
    dataset_txt = config["path"]["dataset_txt"]
    target_root_dir = "./transpiled_rust_with_spec"

    # Run transpilation
    transpiler = TranspilerWithSpec(config, logger, lang_lib)
    transpiler.batch_transpile(dataset_txt, target_root_dir)


if __name__ == "__main__":
    main()
