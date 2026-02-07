# Test Harness Generator

## Overview

`harness_generator.py` is an LLM-based test harness generator for ACSL-annotated C programs. It automatically generates test cases and C test harness code suitable for Frama-C verification.

## Features

- **Automatic test case generation**: Uses LLM to generate valid, invalid, and boundary test cases based on ACSL preconditions
- **Integrated validation**: Validates preconditions with Frama-C WP and verifies output by executing C code
- **Self-healing**: Automatically regenerates invalid test cases until all tests pass validation
- **Structured output**: Produces both executable C harness code and JSON metadata for each function

## Usage

```bash
# Generate harness for a single file
python -m test.harness_generator --file ./data/frama_c_problems/binary_search.c

# Generate harnesses for all files in a benchmark
python -m test.harness_generator --benchmark ./data/dataset_path/supported_benchmark.txt
```

## Output

For each C file, generates two files:
- `*_harness.c`: Executable C harness with test functions
- `*_harness_meta.json`: Test case metadata and validation results
