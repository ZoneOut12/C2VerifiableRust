"""
Benchmark Statistics Analyzer for C2VerifiableRust.

Analyzes C files to extract:
- Lines of Code (LOC)
- Nested pointers
- Function pointers
- Type definitions (structs, enums, unions)
- libc function calls
- ACSL annotation statistics

Usage:
    python -m src.utils.benchmark_stats --benchmark ./data/dataset_path/total_benchmark.txt
"""

import os
import re
import json
from typing import Dict, List, Any, Set
from dataclasses import dataclass, field
from collections import defaultdict
import argparse


# Common libc functions
LIBC_FUNCTIONS = {
    # stdio.h
    'printf', 'fprintf', 'sprintf', 'snprintf', 'scanf', 'fscanf', 'sscanf',
    'fopen', 'fclose', 'fread', 'fwrite', 'fgets', 'fputs', 'fgetc', 'fputc',
    'getchar', 'putchar', 'puts', 'gets', 'fflush', 'fseek', 'ftell', 'rewind',
    'feof', 'ferror', 'perror', 'remove', 'rename', 'tmpfile', 'tmpnam',
    # stdlib.h
    'malloc', 'calloc', 'realloc', 'free', 'exit', 'abort', 'atexit',
    'atoi', 'atol', 'atof', 'strtol', 'strtoul', 'strtod', 'strtof',
    'rand', 'srand', 'qsort', 'bsearch', 'abs', 'labs', 'div', 'ldiv',
    'getenv', 'system',
    # string.h
    'strlen', 'strcpy', 'strncpy', 'strcat', 'strncat', 'strcmp', 'strncmp',
    'strchr', 'strrchr', 'strstr', 'strtok', 'memcpy', 'memmove', 'memset',
    'memcmp', 'memchr',
    # ctype.h
    'isalpha', 'isdigit', 'isalnum', 'isspace', 'isupper', 'islower',
    'toupper', 'tolower', 'isprint', 'ispunct', 'isxdigit',
    # math.h
    'sin', 'cos', 'tan', 'asin', 'acos', 'atan', 'atan2', 'sinh', 'cosh', 'tanh',
    'exp', 'log', 'log10', 'pow', 'sqrt', 'ceil', 'floor', 'fabs', 'fmod',
    # assert.h
    'assert',
    # time.h
    'time', 'clock', 'difftime', 'mktime', 'strftime', 'localtime', 'gmtime',
    # unistd.h (POSIX)
    'read', 'write', 'close', 'sleep', 'usleep', 'fork', 'exec', 'execv', 'execve',
}


@dataclass
class FileStats:
    """Statistics for a single file."""
    file_path: str
    total_lines: int = 0
    code_lines: int = 0  # Non-empty, non-comment lines
    comment_lines: int = 0
    blank_lines: int = 0
    acsl_lines: int = 0  # ACSL annotation lines

    # Language features
    nested_pointers: int = 0  # e.g., int **p, char ***s
    function_pointers: int = 0  # e.g., int (*fp)(int)
    structs: int = 0
    enums: int = 0
    unions: int = 0
    typedefs: int = 0

    # Function calls
    libc_calls: Dict[str, int] = field(default_factory=dict)

    # ACSL features
    acsl_requires: int = 0
    acsl_ensures: int = 0
    acsl_assigns: int = 0
    acsl_loop_invariant: int = 0
    acsl_assert: int = 0
    acsl_behaviors: int = 0

    # Function count
    function_count: int = 0


@dataclass
class BenchmarkStats:
    """Aggregate statistics for the benchmark."""
    total_files: int = 0
    file_stats: List[FileStats] = field(default_factory=list)

    # Aggregates
    total_loc: int = 0
    total_code_lines: int = 0
    total_acsl_lines: int = 0

    # Feature counts
    files_with_nested_pointers: int = 0
    files_with_function_pointers: int = 0
    files_with_structs: int = 0
    files_with_enums: int = 0
    files_with_unions: int = 0
    files_with_typedefs: int = 0
    files_with_libc: int = 0

    # Totals
    total_nested_pointers: int = 0
    total_function_pointers: int = 0
    total_structs: int = 0
    total_enums: int = 0
    total_unions: int = 0
    total_typedefs: int = 0
    total_functions: int = 0

    # libc usage
    libc_usage: Dict[str, int] = field(default_factory=dict)


class BenchmarkAnalyzer:
    """Analyze benchmark files for language features."""

    def __init__(self):
        self.stats = BenchmarkStats()

    def analyze_file(self, file_path: str) -> FileStats:
        """Analyze a single C file."""
        stats = FileStats(file_path=file_path)

        try:
            with open(file_path, 'r', encoding='utf-8', errors='ignore') as f:
                content = f.read()
                lines = content.split('\n')
        except Exception as e:
            print(f"Error reading {file_path}: {e}")
            return stats

        stats.total_lines = len(lines)

        # Track state for multi-line comments
        in_block_comment = False
        in_acsl_block = False

        for line in lines:
            stripped = line.strip()

            # Blank lines
            if not stripped:
                stats.blank_lines += 1
                continue

            # Check for ACSL annotations
            if '/*@' in line or '//@' in line:
                in_acsl_block = '/*@' in line
                stats.acsl_lines += 1
                self._count_acsl_features(line, stats)
                continue

            if in_acsl_block:
                stats.acsl_lines += 1
                self._count_acsl_features(line, stats)
                if '*/' in line:
                    in_acsl_block = False
                continue

            # Block comments
            if '/*' in stripped and '*/' not in stripped:
                in_block_comment = True
                stats.comment_lines += 1
                continue

            if in_block_comment:
                stats.comment_lines += 1
                if '*/' in stripped:
                    in_block_comment = False
                continue

            # Single line comments
            if stripped.startswith('//'):
                stats.comment_lines += 1
                continue

            # Code line
            stats.code_lines += 1

        # Analyze content for features
        self._analyze_features(content, stats)

        return stats

    def _count_acsl_features(self, line: str, stats: FileStats):
        """Count ACSL annotation features."""
        if 'requires' in line:
            stats.acsl_requires += 1
        if 'ensures' in line:
            stats.acsl_ensures += 1
        if 'assigns' in line:
            stats.acsl_assigns += 1
        if 'loop invariant' in line or 'loop_invariant' in line:
            stats.acsl_loop_invariant += 1
        if 'assert' in line:
            stats.acsl_assert += 1
        if 'behavior' in line:
            stats.acsl_behaviors += 1

    def _analyze_features(self, content: str, stats: FileStats):
        """Analyze code content for language features."""

        # Remove comments and ACSL for feature detection
        # Remove ACSL blocks
        content_no_acsl = re.sub(r'/\*@[\s\S]*?\*/', '', content)
        content_no_acsl = re.sub(r'//@.*', '', content_no_acsl)
        # Remove regular comments
        content_clean = re.sub(r'/\*[\s\S]*?\*/', '', content_no_acsl)
        content_clean = re.sub(r'//.*', '', content_clean)

        # Nested pointers: int **p, char ***s, etc.
        # Match type followed by 2+ stars
        nested_ptr_pattern = r'\b\w+\s*\*{2,}'
        stats.nested_pointers = len(re.findall(nested_ptr_pattern, content_clean))

        # Function pointers: type (*name)(params) or typedef ... (*name)(...)
        func_ptr_pattern = r'\(\s*\*\s*\w*\s*\)\s*\([^)]*\)'
        stats.function_pointers = len(re.findall(func_ptr_pattern, content_clean))

        # Structs: struct name { or struct {
        struct_pattern = r'\bstruct\s+\w*\s*\{'
        stats.structs = len(re.findall(struct_pattern, content_clean))

        # Enums: enum name { or enum {
        enum_pattern = r'\benum\s+\w*\s*\{'
        stats.enums = len(re.findall(enum_pattern, content_clean))

        # Unions: union name { or union {
        union_pattern = r'\bunion\s+\w*\s*\{'
        stats.unions = len(re.findall(union_pattern, content_clean))

        # Typedefs
        typedef_pattern = r'\btypedef\b'
        stats.typedefs = len(re.findall(typedef_pattern, content_clean))

        # Function definitions (simplified)
        # Match: type name(params) { but not if/while/for/switch
        func_pattern = r'\b(?!if|while|for|switch|return)\w+\s+\w+\s*\([^)]*\)\s*\{'
        stats.function_count = len(re.findall(func_pattern, content_clean))

        # libc function calls
        for func in LIBC_FUNCTIONS:
            pattern = rf'\b{func}\s*\('
            count = len(re.findall(pattern, content_clean))
            if count > 0:
                stats.libc_calls[func] = count

    def analyze_benchmark(self, benchmark_file: str) -> BenchmarkStats:
        """Analyze all files in the benchmark."""

        # Read file list
        with open(benchmark_file, 'r') as f:
            files = [line.strip() for line in f if line.strip().endswith('.c')]

        print(f"Analyzing {len(files)} files...")

        for i, file_path in enumerate(files):
            if not os.path.exists(file_path):
                print(f"  [{i+1}/{len(files)}] Skipping {file_path}: not found")
                continue

            if (i + 1) % 20 == 0:
                print(f"  [{i+1}/{len(files)}] Processing...")

            file_stats = self.analyze_file(file_path)
            self.stats.file_stats.append(file_stats)

            # Aggregate
            self.stats.total_files += 1
            self.stats.total_loc += file_stats.total_lines
            self.stats.total_code_lines += file_stats.code_lines
            self.stats.total_acsl_lines += file_stats.acsl_lines

            # Feature counts
            if file_stats.nested_pointers > 0:
                self.stats.files_with_nested_pointers += 1
            if file_stats.function_pointers > 0:
                self.stats.files_with_function_pointers += 1
            if file_stats.structs > 0:
                self.stats.files_with_structs += 1
            if file_stats.enums > 0:
                self.stats.files_with_enums += 1
            if file_stats.unions > 0:
                self.stats.files_with_unions += 1
            if file_stats.typedefs > 0:
                self.stats.files_with_typedefs += 1
            if file_stats.libc_calls:
                self.stats.files_with_libc += 1

            # Totals
            self.stats.total_nested_pointers += file_stats.nested_pointers
            self.stats.total_function_pointers += file_stats.function_pointers
            self.stats.total_structs += file_stats.structs
            self.stats.total_enums += file_stats.enums
            self.stats.total_unions += file_stats.unions
            self.stats.total_typedefs += file_stats.typedefs
            self.stats.total_functions += file_stats.function_count

            # libc usage
            for func, count in file_stats.libc_calls.items():
                self.stats.libc_usage[func] = self.stats.libc_usage.get(func, 0) + count

        return self.stats

    def print_report(self):
        """Print a formatted report."""
        s = self.stats

        print("\n" + "=" * 70)
        print("BENCHMARK STATISTICS REPORT")
        print("=" * 70)

        print("\n## Overview")
        print(f"  Total files analyzed: {s.total_files}")
        print(f"  Total lines of code:  {s.total_loc}")
        print(f"  Code lines (non-blank, non-comment): {s.total_code_lines}")
        print(f"  ACSL annotation lines: {s.total_acsl_lines}")
        print(f"  Total functions: {s.total_functions}")

        print("\n## Language Features")
        print(f"  {'Feature':<25} {'Files':>10} {'Total Count':>15}")
        print(f"  {'-'*25} {'-'*10} {'-'*15}")
        print(f"  {'Nested pointers':<25} {s.files_with_nested_pointers:>10} {s.total_nested_pointers:>15}")
        print(f"  {'Function pointers':<25} {s.files_with_function_pointers:>10} {s.total_function_pointers:>15}")
        print(f"  {'Structs':<25} {s.files_with_structs:>10} {s.total_structs:>15}")
        print(f"  {'Enums':<25} {s.files_with_enums:>10} {s.total_enums:>15}")
        print(f"  {'Unions':<25} {s.files_with_unions:>10} {s.total_unions:>15}")
        print(f"  {'Typedefs':<25} {s.files_with_typedefs:>10} {s.total_typedefs:>15}")
        print(f"  {'libc calls':<25} {s.files_with_libc:>10} {sum(s.libc_usage.values()):>15}")

        print("\n## ACSL Annotations (Aggregate)")
        total_requires = sum(fs.acsl_requires for fs in s.file_stats)
        total_ensures = sum(fs.acsl_ensures for fs in s.file_stats)
        total_assigns = sum(fs.acsl_assigns for fs in s.file_stats)
        total_loop_inv = sum(fs.acsl_loop_invariant for fs in s.file_stats)
        total_assert = sum(fs.acsl_assert for fs in s.file_stats)
        total_behaviors = sum(fs.acsl_behaviors for fs in s.file_stats)

        print(f"  requires:       {total_requires}")
        print(f"  ensures:        {total_ensures}")
        print(f"  assigns:        {total_assigns}")
        print(f"  loop invariant: {total_loop_inv}")
        print(f"  assert:         {total_assert}")
        print(f"  behaviors:      {total_behaviors}")

        if s.libc_usage:
            print("\n## libc Function Usage")
            sorted_libc = sorted(s.libc_usage.items(), key=lambda x: -x[1])
            for func, count in sorted_libc[:15]:
                print(f"  {func:<20} {count:>5}")
            if len(sorted_libc) > 15:
                print(f"  ... and {len(sorted_libc) - 15} more")

        # Per-subdirectory breakdown
        print("\n## Per-Directory Breakdown")
        dir_stats = defaultdict(lambda: {'files': 0, 'loc': 0, 'code': 0, 'acsl': 0})
        for fs in s.file_stats:
            # Extract directory name
            parts = fs.file_path.split('/')
            for i, part in enumerate(parts):
                if part in ['autospec_bench', 'frama_c_problems', 'lms_verify', 'tutorial_wp']:
                    dir_name = part
                    break
            else:
                dir_name = 'other'

            dir_stats[dir_name]['files'] += 1
            dir_stats[dir_name]['loc'] += fs.total_lines
            dir_stats[dir_name]['code'] += fs.code_lines
            dir_stats[dir_name]['acsl'] += fs.acsl_lines

        print(f"  {'Directory':<25} {'Files':>8} {'LOC':>10} {'Code':>10} {'ACSL':>10}")
        print(f"  {'-'*25} {'-'*8} {'-'*10} {'-'*10} {'-'*10}")
        for dir_name, stats in sorted(dir_stats.items()):
            print(f"  {dir_name:<25} {stats['files']:>8} {stats['loc']:>10} {stats['code']:>10} {stats['acsl']:>10}")

    def save_report(self, output_file: str):
        """Save report to JSON file."""
        s = self.stats

        report = {
            'summary': {
                'total_files': s.total_files,
                'total_loc': s.total_loc,
                'total_code_lines': s.total_code_lines,
                'total_acsl_lines': s.total_acsl_lines,
                'total_functions': s.total_functions,
            },
            'language_features': {
                'nested_pointers': {
                    'files_with_feature': s.files_with_nested_pointers,
                    'total_count': s.total_nested_pointers,
                },
                'function_pointers': {
                    'files_with_feature': s.files_with_function_pointers,
                    'total_count': s.total_function_pointers,
                },
                'structs': {
                    'files_with_feature': s.files_with_structs,
                    'total_count': s.total_structs,
                },
                'enums': {
                    'files_with_feature': s.files_with_enums,
                    'total_count': s.total_enums,
                },
                'unions': {
                    'files_with_feature': s.files_with_unions,
                    'total_count': s.total_unions,
                },
                'typedefs': {
                    'files_with_feature': s.files_with_typedefs,
                    'total_count': s.total_typedefs,
                },
                'libc_calls': {
                    'files_with_feature': s.files_with_libc,
                    'total_count': sum(s.libc_usage.values()),
                    'functions': dict(sorted(s.libc_usage.items(), key=lambda x: -x[1])),
                },
            },
            'acsl_annotations': {
                'requires': sum(fs.acsl_requires for fs in s.file_stats),
                'ensures': sum(fs.acsl_ensures for fs in s.file_stats),
                'assigns': sum(fs.acsl_assigns for fs in s.file_stats),
                'loop_invariant': sum(fs.acsl_loop_invariant for fs in s.file_stats),
                'assert': sum(fs.acsl_assert for fs in s.file_stats),
                'behaviors': sum(fs.acsl_behaviors for fs in s.file_stats),
            },
            'per_file': [
                {
                    'file': fs.file_path,
                    'total_lines': fs.total_lines,
                    'code_lines': fs.code_lines,
                    'acsl_lines': fs.acsl_lines,
                    'nested_pointers': fs.nested_pointers,
                    'function_pointers': fs.function_pointers,
                    'structs': fs.structs,
                    'enums': fs.enums,
                    'unions': fs.unions,
                    'typedefs': fs.typedefs,
                    'libc_calls': fs.libc_calls,
                    'functions': fs.function_count,
                }
                for fs in s.file_stats
            ]
        }

        os.makedirs(os.path.dirname(output_file), exist_ok=True)
        with open(output_file, 'w') as f:
            json.dump(report, f, indent=2)

        print(f"\nDetailed report saved to: {output_file}")


def main():
    parser = argparse.ArgumentParser(description='Benchmark statistics analyzer')
    parser.add_argument(
        '--benchmark',
        default='./data/dataset_path/total_benchmark.txt',
        help='Benchmark file list'
    )
    parser.add_argument(
        '--output',
        default='./result/benchmark_stats.json',
        help='Output JSON report'
    )

    args = parser.parse_args()

    analyzer = BenchmarkAnalyzer()
    analyzer.analyze_benchmark(args.benchmark)
    analyzer.print_report()
    analyzer.save_report(args.output)


if __name__ == '__main__':
    main()
