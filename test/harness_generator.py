"""
LLM-based test harness generator with Frama-C validation.

This module:
1. Uses LLM to generate test cases AND test harness code
2. Validates preconditions using Frama-C WP
3. Validates outputs by running C program
4. Regenerates invalid test cases

Directory structure:
    test/harness/
        autospec_bench/
        frama_c_problems/
        lms_verify/
        tutorial_wp/

Usage:
    python -m test.harness_generator --file ./data/frama_c_problems/binary_search.c
    python -m test.harness_generator --benchmark ./data/dataset_path/supported_benchmark.txt
"""

import os
import re
import json
import subprocess
import tempfile
import shutil
from typing import Dict, List, Any, Optional, Tuple
from dataclasses import dataclass, field
from enum import Enum
from openai import OpenAI
import tomllib


class ValidationStatus(Enum):
    VALID = "valid"              # Precondition satisfied, output correct
    PRECOND_FAIL = "precond_fail"  # Precondition violated (expected for invalid tests)
    OUTPUT_MISMATCH = "output_mismatch"  # Precondition OK but output wrong
    COMPILE_ERROR = "compile_error"
    RUNTIME_ERROR = "runtime_error"
    TIMEOUT = "timeout"


@dataclass
class HarnessTestCase:
    """A single test case in a harness."""
    test_id: int
    inputs: Dict[str, Any]
    expected_output: Any
    test_type: str  # "valid", "invalid", "boundary"
    description: str
    validation_status: Optional[ValidationStatus] = None
    actual_output: Optional[Any] = None


@dataclass
class TestHarness:
    """Test harness for a C file."""
    source_file: str
    function_name: str
    function_signature: str
    preconditions: List[str]
    test_cases: List[HarnessTestCase] = field(default_factory=list)
    harness_code: str = ""


class HarnessGenerator:
    """Generate and validate test harnesses."""

    def __init__(self, config: dict):
        self.config = config
        self.api_key = config["model"]["api_key"]
        self.model_name = config["model"]["model_name"]
        self.base_url = config["model"].get("base_url")
        self.temperature = config["model"].get("temperature", 0.3)
        self.max_tokens = 8192

        if self.base_url:
            self.client = OpenAI(base_url=self.base_url, api_key=self.api_key)
        else:
            self.client = OpenAI(api_key=self.api_key)

        # Base directory for harness files
        self.harness_base_dir = os.path.join(
            os.path.dirname(os.path.abspath(__file__)),
            "harness"
        )

    def _call_llm(self, system_prompt: str, user_prompt: str) -> str:
        """Call LLM and return response."""
        try:
            print(f"    Calling LLM ({self.model_name})...")
            completion = self.client.chat.completions.create(
                model=self.model_name,
                messages=[
                    {"role": "system", "content": system_prompt},
                    {"role": "user", "content": user_prompt},
                ],
                temperature=self.temperature,
                max_tokens=self.max_tokens,
            )

            if not completion.choices:
                return "{}"

            content = completion.choices[0].message.content
            return content if content else "{}"

        except Exception as e:
            print(f"    LLM API call failed: {e}")
            return "{}"

    def _get_subdir_for_file(self, c_file: str) -> str:
        """Determine which subdirectory a file belongs to."""
        path_lower = c_file.lower()
        if 'autospec_bench' in path_lower:
            return 'autospec_bench'
        elif 'frama_c_problems' in path_lower:
            return 'frama_c_problems'
        elif 'lms_verify' in path_lower:
            return 'lms_verify'
        elif 'tutorial_wp' in path_lower:
            return 'tutorial_wp'
        else:
            return 'other'

    def _get_harness_path(self, c_file: str) -> str:
        """Get the harness file path for a C file."""
        subdir = self._get_subdir_for_file(c_file)
        basename = os.path.basename(c_file).replace('.c', '_harness.c')
        return os.path.join(self.harness_base_dir, subdir, basename)

    def generate_harness(
        self,
        c_file: str,
        num_valid: int = 5,
        num_invalid: int = 3,
        num_boundary: int = 3
    ) -> Optional[TestHarness]:
        """Generate test harness for a C file."""

        with open(c_file, 'r') as f:
            c_code = f.read()

        system_prompt = """You are an expert in C programming, formal verification, and software testing.
You understand ACSL (ANSI/ISO C Specification Language) annotations used with Frama-C.

Your task is to generate test cases AND a test harness for C functions.
The harness will be used with Frama-C to verify preconditions."""

        user_prompt = f"""Analyze the following C code with ACSL annotations and generate:
1. A JSON description of test cases
2. A C test harness file

**C Code with ACSL:**
```c
{c_code}
```

**Requirements:**

Generate test cases in these categories:
- **Valid** ({num_valid} cases): Inputs that SATISFY ALL preconditions
- **Invalid** ({num_invalid} cases): Inputs that VIOLATE at least one precondition
- **Boundary** ({num_boundary} cases): Edge cases that still satisfy preconditions

**Output Format:**

Return a JSON object with this structure:
```json
{{
  "function_name": "<main function name>",
  "function_signature": "<function signature>",
  "preconditions": ["<requires clause 1>", ...],
  "test_cases": [
    {{
      "test_id": 1,
      "type": "valid|invalid|boundary",
      "inputs": {{"param1": value1, "param2": [1,2,3], ...}},
      "expected_output": <value or null for invalid>,
      "description": "<brief description>"
    }},
    ...
  ],
  "harness_code": "<C code as escaped string>"
}}
```

**Harness Code Requirements:**

1. Do NOT use `main` as function name - use `test_harness_<function_name>`
2. Include the original C code at the top (copy it, don't use #include)
3. Each test case should be a separate function: `test_case_N()`
4. For valid/boundary tests, print the result so we can verify output
5. For arrays, declare them as local variables with proper initialization

**Example Harness Structure:**
```c
// ========== Original Code (with ACSL) ==========
/*@ requires n >= 0;
    requires \\valid(arr + (0..n-1));
    assigns \\nothing;
*/
int sum(int *arr, int n) {{
    int s = 0;
    for (int i = 0; i < n; i++) s += arr[i];
    return s;
}}

// ========== Test Cases ==========
#include <stdio.h>

// Test case 1: Valid - normal array
void test_case_1() {{
    int arr[] = {{1, 2, 3, 4, 5}};
    int result = sum(arr, 5);
    printf("test_case_1: %d\\n", result);  // Expected: 15
}}

// Test case 2: Valid - single element
void test_case_2() {{
    int arr[] = {{42}};
    int result = sum(arr, 1);
    printf("test_case_2: %d\\n", result);  // Expected: 42
}}

// Test case 3: Boundary - empty array
void test_case_3() {{
    int arr[] = {{0}};  // Dummy, won't be accessed
    int result = sum(arr, 0);
    printf("test_case_3: %d\\n", result);  // Expected: 0
}}

// Test case 4: Invalid - negative n (violates n >= 0)
void test_case_4() {{
    int arr[] = {{1, 2, 3}};
    int result = sum(arr, -1);  // Frama-C should flag this
    // No output check needed for invalid case
}}

// Harness entry point (not main!)
void test_harness_sum() {{
    test_case_1();
    test_case_2();
    test_case_3();
    // test_case_4 intentionally not called - it's for precondition testing
}}
```

**Important:**
1. For sorted array requirements (`\\forall k1 < k2: arr[k1] <= arr[k2]`), ensure valid arrays are sorted
2. For pointer validity (`\\valid(arr + (0..n-1))`), ensure array has exactly n elements
3. For invalid tests, make sure ONLY ONE precondition is violated (for clear diagnosis)
4. Use realistic values, not extreme integers
5. Escape the harness code properly in JSON (use \\n for newlines)

Now generate the test harness for the provided C code:"""

        response = self._call_llm(system_prompt, user_prompt)

        # Parse response
        try:
            # Extract JSON
            json_match = re.search(r'```(?:json)?\s*([\s\S]*?)\s*```', response)
            if json_match:
                json_str = json_match.group(1)
            else:
                json_str = response.strip()

            data = json.loads(json_str)

            # Build TestHarness object
            harness = TestHarness(
                source_file=c_file,
                function_name=data.get('function_name', 'unknown'),
                function_signature=data.get('function_signature', ''),
                preconditions=data.get('preconditions', []),
                harness_code=data.get('harness_code', '')
            )

            # Parse test cases
            for tc_data in data.get('test_cases', []):
                tc = HarnessTestCase(
                    test_id=tc_data.get('test_id', 0),
                    inputs=tc_data.get('inputs', {}),
                    expected_output=tc_data.get('expected_output'),
                    test_type=tc_data.get('type', 'valid'),
                    description=tc_data.get('description', '')
                )
                harness.test_cases.append(tc)

            return harness

        except json.JSONDecodeError as e:
            print(f"    Failed to parse LLM response: {e}")
            return None

    def save_harness(self, harness: TestHarness) -> str:
        """Save harness code to file."""
        harness_path = self._get_harness_path(harness.source_file)
        os.makedirs(os.path.dirname(harness_path), exist_ok=True)

        with open(harness_path, 'w') as f:
            f.write(harness.harness_code)

        return harness_path

    def validate_precondition_with_frama_c(
        self,
        harness_path: str,
        test_case_func: str
    ) -> Tuple[bool, str]:
        """
        Use Frama-C WP to check if a test case satisfies preconditions.

        Returns (satisfied, details)
        """
        try:
            # Run Frama-C with WP to check @requires properties
            # We check if the function call in test_case_func satisfies the callee's requires
            result = subprocess.run(
                [
                    "frama-c", "-wp",
                    "-wp-prop", "@requires",
                    "-wp-timeout", "10",
                    "-wp-out", "/dev/null",
                    harness_path
                ],
                capture_output=True,
                timeout=30,
                text=True
            )

            output = result.stdout + result.stderr

            # Check for proof status
            # Frama-C outputs something like:
            # [wp] Proved goals: X / Y
            # If all requires are proved, preconditions are satisfied

            if "Proved goals" in output:
                # Parse proved/total
                match = re.search(r'Proved goals:\s*(\d+)\s*/\s*(\d+)', output)
                if match:
                    proved, total = int(match.group(1)), int(match.group(2))
                    if proved == total:
                        return True, f"All {total} preconditions satisfied"
                    else:
                        return False, f"Only {proved}/{total} preconditions proved"

            # Check for specific failures
            if "Unknown" in output or "Timeout" in output:
                return False, "Frama-C could not determine precondition status"

            # Default: assume satisfied if no errors
            return True, "No precondition violations detected"

        except subprocess.TimeoutExpired:
            return False, "Frama-C timeout"
        except FileNotFoundError:
            return False, "Frama-C not found"
        except Exception as e:
            return False, f"Error: {e}"

    def validate_single_test_case(
        self,
        harness_path: str,
        test_case: HarnessTestCase,
        function_name: str
    ) -> ValidationStatus:
        """Validate a single test case."""

        test_func = f"test_case_{test_case.test_id}"

        # Step 1: Check precondition with Frama-C
        # Create a temporary harness that only includes this test case
        precond_ok, details = self._check_precondition_for_test(
            harness_path, test_case, function_name
        )

        if not precond_ok:
            test_case.validation_status = ValidationStatus.PRECOND_FAIL
            if test_case.test_type == "invalid":
                # Expected behavior for invalid tests
                return ValidationStatus.PRECOND_FAIL
            else:
                # Unexpected - valid/boundary test fails precondition
                print(f"      {test_func}: Precondition FAILED (unexpected)")
                return ValidationStatus.PRECOND_FAIL

        # Step 2: For valid/boundary tests, verify output
        if test_case.test_type in ["valid", "boundary"]:
            actual, status = self._run_test_and_get_output(harness_path, test_case)

            if status != ValidationStatus.VALID:
                test_case.validation_status = status
                return status

            test_case.actual_output = actual

            # Compare outputs
            if actual is not None and test_case.expected_output is not None:
                if str(actual).strip() == str(test_case.expected_output).strip():
                    test_case.validation_status = ValidationStatus.VALID
                    return ValidationStatus.VALID
                else:
                    print(f"      {test_func}: Output mismatch (expected {test_case.expected_output}, got {actual})")
                    test_case.validation_status = ValidationStatus.OUTPUT_MISMATCH
                    return ValidationStatus.OUTPUT_MISMATCH

        test_case.validation_status = ValidationStatus.VALID
        return ValidationStatus.VALID

    def _check_precondition_for_test(
        self,
        harness_path: str,
        test_case: HarnessTestCase,
        function_name: str
    ) -> Tuple[bool, str]:
        """Check precondition for a specific test case using Frama-C."""

        # Read harness
        with open(harness_path, 'r') as f:
            harness_code = f.read()

        # Create a minimal file with just the function and this test case
        test_func_name = f"test_case_{test_case.test_id}"

        # Extract the original function (with ACSL) and the test case function
        # This is a simplified approach - in practice you might need better parsing

        with tempfile.NamedTemporaryFile(mode='w', suffix='.c', delete=False) as tmp:
            tmp.write(harness_code)
            tmp_path = tmp.name

        try:
            result = subprocess.run(
                [
                    "frama-c", "-wp",
                    "-wp-prop", "@requires",
                    "-wp-timeout", "10",
                    "-wp-function", test_func_name,
                    tmp_path
                ],
                capture_output=True,
                timeout=30,
                text=True
            )

            output = result.stdout + result.stderr

            # Look for proof results
            if "Proved goals" in output:
                match = re.search(r'Proved goals:\s*(\d+)\s*/\s*(\d+)', output)
                if match:
                    proved, total = int(match.group(1)), int(match.group(2))
                    if total == 0:
                        return True, "No preconditions to check"
                    return proved == total, f"{proved}/{total} proved"

            # Check for specific failure indicators
            if "Unknown" in output:
                return False, "Unknown proof status"

            return True, "No failures detected"

        except subprocess.TimeoutExpired:
            return True, "Timeout (assuming OK)"
        except Exception as e:
            return True, f"Error: {e} (assuming OK)"
        finally:
            os.unlink(tmp_path)

    def _run_test_and_get_output(
        self,
        harness_path: str,
        test_case: HarnessTestCase
    ) -> Tuple[Optional[str], ValidationStatus]:
        """Compile and run test case, return output."""

        test_func = f"test_case_{test_case.test_id}"

        # Create a main that calls just this test
        with open(harness_path, 'r') as f:
            harness_code = f.read()

        # Add a main function that calls the specific test
        runner_code = harness_code + f"""

int main() {{
    {test_func}();
    return 0;
}}
"""

        with tempfile.TemporaryDirectory() as tmpdir:
            src_path = os.path.join(tmpdir, "test.c")
            exe_path = os.path.join(tmpdir, "test")

            with open(src_path, 'w') as f:
                f.write(runner_code)

            # Compile
            result = subprocess.run(
                ["gcc", "-o", exe_path, src_path, "-w", "-lm"],
                capture_output=True,
                timeout=10
            )

            if result.returncode != 0:
                return None, ValidationStatus.COMPILE_ERROR

            # Run
            try:
                result = subprocess.run(
                    [exe_path],
                    capture_output=True,
                    timeout=5,
                    text=True
                )

                if result.returncode != 0:
                    return None, ValidationStatus.RUNTIME_ERROR

                # Parse output - expect format "test_case_N: <value>"
                output = result.stdout.strip()
                match = re.search(rf'{test_func}:\s*(-?\d+)', output)
                if match:
                    return match.group(1), ValidationStatus.VALID

                return output, ValidationStatus.VALID

            except subprocess.TimeoutExpired:
                return None, ValidationStatus.TIMEOUT

    def validate_and_fix_harness(
        self,
        harness: TestHarness,
        max_retries: int = 2
    ) -> TestHarness:
        """Validate all test cases and regenerate invalid ones."""

        harness_path = self.save_harness(harness)
        print(f"    Saved harness to {harness_path}")

        # Track which test cases need regeneration
        invalid_tests = []
        valid_count = 0

        for tc in harness.test_cases:
            print(f"    Validating test_case_{tc.test_id} ({tc.test_type})...")
            status = self.validate_single_test_case(
                harness_path, tc, harness.function_name
            )

            if tc.test_type == "invalid":
                # Invalid tests should fail precondition
                if status == ValidationStatus.PRECOND_FAIL:
                    valid_count += 1
                    print(f"      OK (precondition correctly violated)")
                else:
                    invalid_tests.append(tc)
                    print(f"      FAIL (should violate precondition but didn't)")
            else:
                # Valid/boundary tests should pass
                if status == ValidationStatus.VALID:
                    valid_count += 1
                    print(f"      OK")
                elif status == ValidationStatus.OUTPUT_MISMATCH:
                    # Fix output from actual
                    if tc.actual_output is not None:
                        print(f"      Fixing output: {tc.expected_output} -> {tc.actual_output}")
                        tc.expected_output = tc.actual_output
                        tc.validation_status = ValidationStatus.VALID
                        valid_count += 1
                else:
                    invalid_tests.append(tc)

        print(f"    Validation: {valid_count}/{len(harness.test_cases)} valid")

        # Regenerate invalid tests if needed
        if invalid_tests and max_retries > 0:
            print(f"    Regenerating {len(invalid_tests)} invalid test cases...")
            harness = self._regenerate_tests(harness, invalid_tests, max_retries - 1)

        return harness

    def _regenerate_tests(
        self,
        harness: TestHarness,
        invalid_tests: List[HarnessTestCase],
        retries_left: int
    ) -> TestHarness:
        """Ask LLM to regenerate specific test cases."""

        # Build prompt describing what went wrong
        issues = []
        for tc in invalid_tests:
            issues.append(f"- test_case_{tc.test_id} ({tc.test_type}): {tc.validation_status}")

        system_prompt = """You are fixing test cases that failed validation.
Generate replacement test cases that satisfy the requirements."""

        user_prompt = f"""The following test cases for function `{harness.function_name}` failed validation:

{chr(10).join(issues)}

**Function signature:** {harness.function_signature}
**Preconditions:** {harness.preconditions}

**Issues:**
- For "valid" tests: must satisfy ALL preconditions
- For "invalid" tests: must violate at least one precondition
- For arrays with sorted requirement: must actually be sorted
- For length constraints: array length must match n parameter

Please provide replacement test cases in JSON format:
```json
{{
  "replacement_tests": [
    {{
      "original_id": <id>,
      "inputs": {{...}},
      "expected_output": <value>,
      "description": "<what this tests>"
    }},
    ...
  ],
  "harness_additions": "<additional test_case_N functions as C code>"
}}
```"""

        response = self._call_llm(system_prompt, user_prompt)

        try:
            json_match = re.search(r'```(?:json)?\s*([\s\S]*?)\s*```', response)
            if json_match:
                data = json.loads(json_match.group(1))

                # Apply replacements
                for repl in data.get('replacement_tests', []):
                    orig_id = repl.get('original_id')
                    for tc in harness.test_cases:
                        if tc.test_id == orig_id:
                            tc.inputs = repl.get('inputs', tc.inputs)
                            tc.expected_output = repl.get('expected_output')
                            tc.description = repl.get('description', tc.description)
                            tc.validation_status = None  # Reset for re-validation

                # Update harness code if provided
                additions = data.get('harness_additions', '')
                if additions:
                    harness.harness_code += "\n" + additions

        except Exception as e:
            print(f"    Failed to parse regeneration response: {e}")

        return harness

    def generate_and_validate(
        self,
        c_file: str,
        num_valid: int = 5,
        num_invalid: int = 3,
        num_boundary: int = 3,
        max_retries: int = 2
    ) -> Optional[TestHarness]:
        """Generate harness and validate all test cases."""

        print(f"  Generating harness for {c_file}...")

        harness = self.generate_harness(c_file, num_valid, num_invalid, num_boundary)

        if harness is None:
            print(f"    Failed to generate harness")
            return None

        print(f"    Generated {len(harness.test_cases)} test cases")

        # Validate and fix
        harness = self.validate_and_fix_harness(harness, max_retries)

        # Save final harness
        harness_path = self.save_harness(harness)

        # Save test case metadata
        metadata_path = harness_path.replace('.c', '_meta.json')
        metadata = {
            'source_file': harness.source_file,
            'function_name': harness.function_name,
            'function_signature': harness.function_signature,
            'preconditions': harness.preconditions,
            'test_cases': [
                {
                    'test_id': tc.test_id,
                    'type': tc.test_type,
                    'inputs': tc.inputs,
                    'expected_output': tc.expected_output,
                    'description': tc.description,
                    'validation_status': tc.validation_status.value if tc.validation_status else None,
                    'actual_output': tc.actual_output
                }
                for tc in harness.test_cases
            ]
        }

        with open(metadata_path, 'w') as f:
            json.dump(metadata, f, indent=2, ensure_ascii=False)

        print(f"    Metadata saved to {metadata_path}")

        return harness

    def process_benchmark(
        self,
        benchmark_txt: str,
        num_valid: int = 5,
        num_invalid: int = 3,
        num_boundary: int = 3
    ) -> Dict[str, Any]:
        """Process all files in benchmark."""

        with open(benchmark_txt, 'r') as f:
            c_files = [line.strip() for line in f if line.strip().endswith('.c')]

        results = {
            'summary': {
                'total': len(c_files),
                'success': 0,
                'failed': 0
            },
            'files': {}
        }

        for i, c_file in enumerate(c_files):
            if not os.path.exists(c_file):
                print(f"[{i+1}/{len(c_files)}] Skipping {c_file}: not found")
                results['files'][c_file] = {'status': 'not_found'}
                continue

            print(f"[{i+1}/{len(c_files)}] Processing {c_file}...")

            try:
                harness = self.generate_and_validate(
                    c_file, num_valid, num_invalid, num_boundary
                )

                if harness:
                    valid_tests = sum(
                        1 for tc in harness.test_cases
                        if tc.validation_status == ValidationStatus.VALID or
                           (tc.test_type == "invalid" and tc.validation_status == ValidationStatus.PRECOND_FAIL)
                    )

                    results['files'][c_file] = {
                        'status': 'success',
                        'harness_path': self._get_harness_path(c_file),
                        'total_tests': len(harness.test_cases),
                        'valid_tests': valid_tests
                    }
                    results['summary']['success'] += 1
                else:
                    results['files'][c_file] = {'status': 'generation_failed'}
                    results['summary']['failed'] += 1

            except Exception as e:
                print(f"    Error: {e}")
                results['files'][c_file] = {'status': 'error', 'error': str(e)}
                results['summary']['failed'] += 1

        return results


def main():
    """Main entry point."""
    import argparse

    parser = argparse.ArgumentParser(description='Test harness generator with Frama-C validation')
    parser.add_argument('--file', help='Single C file to process')
    parser.add_argument(
        '--benchmark',
        default='./data/dataset_path/supported_benchmark.txt',
        help='Benchmark file list'
    )
    parser.add_argument(
        '--output',
        default='./test/harness/generation_report.json',
        help='Output report file'
    )
    parser.add_argument('--num-valid', type=int, default=5)
    parser.add_argument('--num-invalid', type=int, default=3)
    parser.add_argument('--num-boundary', type=int, default=3)

    args = parser.parse_args()

    # Load config
    config_path = os.path.join(
        os.path.dirname(os.path.abspath(__file__)),
        "..", "src", "config.toml"
    )
    with open(config_path, "rb") as f:
        config = tomllib.load(f)

    generator = HarnessGenerator(config)

    if args.file:
        harness = generator.generate_and_validate(
            args.file,
            num_valid=args.num_valid,
            num_invalid=args.num_invalid,
            num_boundary=args.num_boundary
        )
        if harness:
            print(f"\nHarness saved to: {generator._get_harness_path(args.file)}")
    else:
        results = generator.process_benchmark(
            args.benchmark,
            num_valid=args.num_valid,
            num_invalid=args.num_invalid,
            num_boundary=args.num_boundary
        )

        # Save report
        os.makedirs(os.path.dirname(args.output), exist_ok=True)
        with open(args.output, 'w') as f:
            json.dump(results, f, indent=2)

        print(f"\n{'='*50}")
        print(f"Generation Summary")
        print(f"{'='*50}")
        print(f"Total files: {results['summary']['total']}")
        print(f"Success: {results['summary']['success']}")
        print(f"Failed: {results['summary']['failed']}")
        print(f"\nReport saved to {args.output}")


if __name__ == '__main__':
    main()
