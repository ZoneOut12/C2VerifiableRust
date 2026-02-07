import os


class PromptSwitcher:
    def __init__(self):
        self.base_dir = os.path.dirname(os.path.abspath(__file__))
        self.context_prompt = r"""The translation should take into account the Rust context provided below (which may define dependent types, constants, global variables, or helper functions).
*Rust Context:*
```rust
{context}
```
"""

    def datatype_prompt(self, c_code, context=None):
        path = os.path.join(self.base_dir, "datatype_prompt.txt")
        with open(path, "r") as f:
            template = f.read()
        if context is not None:
            rust_context = self.context_prompt.format(context=context)
            prompt = template.format(context=rust_context, code=c_code)
        else:
            prompt = template.format(context="", code=c_code)
        return prompt

    def variable_prompt(self, c_code, context=None):
        path = os.path.join(self.base_dir, "variable_prompt.txt")
        with open(path, "r") as f:
            template = f.read()
        if context is not None:
            rust_context = self.context_prompt.format(context=context)
            prompt = template.format(context=rust_context, code=c_code)
        else:
            prompt = template.format(context="", code=c_code)
        return prompt

    def macro_prompt(self, c_code, context=None):
        path = os.path.join(self.base_dir, "macro_prompt.txt")
        with open(path, "r") as f:
            template = f.read()
        if context is not None:
            rust_context = self.context_prompt.format(context=context)
            prompt = template.format(context=rust_context, code=c_code)
        else:
            prompt = template.format(context="", code=c_code)
        return prompt

    def function_prompt(self, c_code, context=None):
        path = os.path.join(self.base_dir, "function_prompt.txt")
        with open(path, "r") as f:
            template = f.read()
        if context is not None:
            rust_context = self.context_prompt.format(context=context)
            prompt = template.format(context=rust_context, code=c_code)
        else:
            prompt = template.format(context="", code=c_code)
        return prompt

    def repair_prompt(self, c_code, rust_code, error_msg):
        path = os.path.join(self.base_dir, "repair_prompt.txt")
        with open(path, "r") as f:
            template = f.read()
        prompt = template.format(
            c_code=c_code, rust_code=rust_code, error_msg=error_msg
        )
        return prompt


def transpile_prompt(code):
    prompt = f"""You are a code translator specializing in converting C code to safe, idiomatic Rust code.

**Objectives**:
- The translated Rust code should be a line-by-line reimplementation that mirrors the original C structure as closely as possible in both syntax and control flow.
- Ensure that the translated Rust code maintains the same **behavior** and **control structure** as the original C code.
- Convert C pointer types (`T*`) into Rust references (`&T` or `&mut T`), depending on mutability.
- Always convert `for` loops in C into semantically equivalent `while` loops in Rust.
- If a type (such as an `enum`) or a module contains multiple named items (such as variants or constants) that are used in the code, the Rust translation should include `use Type::*;` or `use module::*;` to allow unqualified access.
- **Preserve all comments from the original C code**, ideally at the corresponding locations.
- For C code that only declares a function (without a definition), translate it to Rust as a full function definition with the body containing only `unimplemented!();`.

**Constraints**:
- Do not rewrite the structure of the code in ways that obscure the original intent (e.g., avoid using `split_at_mut`, iterators, or high-level abstractions unless the C code already uses equivalent constructs).
- Avoid functional or declarative rewrites — preserve imperative structure.
- **Do not use raw pointers or pointer conversion methods (e.g., `as_ptr()`, `as_mut_ptr()`, or casting references to pointers).**
- Avoid using `unsafe` blocks in Rust unless absolutely necessary.
- Do not change any identifiers (such as variable names, function names, struct names, etc.) from the original C code.
- Do not use standard library or third-party functions (such as `std::cmp::max`) to replace explicit conditionals and operations in the original C code.
- **Do not use any `use std::...` imports under any circumstance.**
- **Do not introduce any new comments** that were not present in the original C code.
- Output only the translated Rust code, without any additional explanations.
- **The final translated Rust code must be wrapped in a fenced code block starting with ` ```rust ` and ending with ` ``` `.**

**Guidelines**:
1. **Pointer Conversion**:
    - Translate C pointers (`T*`) to Rust references: use `&T` for immutable pointers and `&mut T` for mutable pointers.
    - Use `&mut T` **only if** the C code modifies the data pointed to by the pointer.
    - If the data pointed to is only read (not modified), use `&T`.

2. **Array Handling**:
    - Convert C arrays or pointers(e.g., `int*`) to Rust slices (`&[i32]` or `&mut [i32]`) as appropriate.

3. **Specialization for `char*` and `char`**:
    - For `char*` or `char[]`:
        - If **immutable** and points to contiguous character data (i.e. a C string), convert to `&str`.
        - If **mutable**, treat as a writable string buffer; convert to `&mut String`.
    - For single `char` values:
        - Convert to Rust `char`.

4. **Function Parameters and Return Types**:
    - Adjust function signatures to use Rust references instead of pointers.
    - Do not change the function name, argument list and argument names.
    - For functions returning pointers, consider returning `Option<&T>` or `Option<&mut T>` in Rust.

5. **Memory Management**:
    - Avoid manual memory management in Rust; utilize Rust's ownership and borrowing system.
    - Do not use raw pointers or manual allocation/deallocation unless necessary, and avoid `unsafe` blocks.

6. **Loop Translation**:
    - **All `for` loops in C **must** be translated to explicit `while` loops in Rust**, preserving initialization, condition check, and increment statements as separate components.

7. **Global Variable Conversion**:
    - Convert C global variables to Rust equivalents:
        - If the C global is `const` or never modified, use `const` in Rust.
        - If the C global is modified in the program, use `static mut` in Rust.

8. **Variable Declarations**:
    - Every variable in the translated Rust code must include an explicit type annotation, even if it is initialized immediately.
    
9. **Code Style and Idiomatic Rust**:
    - Follow idiomatic Rust style **without** altering the underlying control flow, structure, or logic of the original C code.

**Examples**:
*Example 1:*
Input:
```c
struct Person {{
    int height;
    int age;
}};

enum Color {{
    RED,
    GREEN,
    BLUE
}};

int main() {{
    enum Color c = GREEN;
    if (c == GREEN) {{
        c = BLUE;
    }}
    struct Person p = {{170, 30}};
    p.age += 1;
    return 0;
}}
```
Output:
```rust
struct Person {{
    height: i32,
    age: i32,
}}

#[derive(PartialEq)]
enum Color {{
    RED,
    GREEN,
    BLUE,
}}

use Color::*;

fn main() {{
    let mut c: Color = GREEN;
    if c == GREEN {{
        c = BLUE;
    }}
    let mut p: Person = Person {{
        height: 170,
        age: 30,
    }};
    p.age += 1;
}}
```
*Example 2:*
Input:
```c
void reverse(int* arr, int len){{
    for (int i = 0; i < len / 2; i++) {{
        int tmp = arr[i];
        arr[i] = arr[len - 1 - i];
        arr[len - 1 - i] = tmp;
    }}
}}

int sum_vector(int* vec, int len) {{
    int sum = 0;
    // verus_assert(1);
    for (int i = 0; i < len; i++) {{
        sum += vec[i];
    }}
    return sum;
}}
```
Output:
```rust
fn reverse(arr: &mut [i32], len: i32) {{
    let mut i: i32 = 0;
    while i < len / 2 {{
        let tmp: i32 = arr[i as usize];
        arr[i as usize] = arr[(len - 1 - i) as usize];
        arr[(len - 1 - i) as usize] = tmp;
        i += 1;
    }}
}}

fn sum_vector(vec: &[i32], len: i32) -> i32 {{
    let mut sum: i32 = 0;
    // verus_assert(1);
    let mut i: i32 = 0;
    while i < len {{
        sum += vec[i as usize];
        i += 1;
    }}
    sum
}}
```
*Example 3:*
Input:
```c
#include <stdio.h>
#include <string.h>

int THRESHOLD = 100;

int CheckAndCount(int* ptr) {{
    if (*ptr > THRESHOLD) {{
        return *ptr;
    }} else {{
        return THRESHOLD;
    }}
}}

void foo(const char *input) {{
    int len = strlen(input);
    // verus_assert(1);
}}

void Test() {{
}}
```
Output:
```rust
const THRESHOLD: i32 = 100;

fn CheckAndCount(ptr: &i32) -> i32 {{
    if *ptr > THRESHOLD {{
        *ptr
    }} else {{
        THRESHOLD
    }}
}}

fn foo(input: &str) {{
    let len: i32 = input.len() as i32;
    // verus_assert(1);
}}

fn Test() {{
}}
```

**Now, please translate the following C code into safe, idiomatic Rust code:**
```c
{code}
```

**Output**:
"""
    return prompt


def repair_prompt(c_file, rust_file, error_msg):
    c_code = ""
    with open(c_file, "r") as f:
        c_code = f.read()
    rust_code = ""
    with open(rust_file, "r") as f:
        rust_code = f.read()
    prompt = f"""You are assisting in debugging and correcting Rust code that was automatically translated from a C program.

**Below, you are given:**
1. The original C program to be translated.
2. An initial Rust translation that fails to compile.
3. The compiler error messages produced by `rustc`.

**Your task is to:**
- Fix only the compilation errors, and preserve the structure, control flow, comments, and all identifiers exactly as written in the original (buggy) Rust translation.
- Preserve the original behavior of the C program.
- Do not restructure or simplify the Rust code beyond what is necessary to fix the errors.
- Do not use standard library or third-party functions (such as `std::cmp::max`) to replace explicit conditionals and operations in the original C code.
- Do not introduce new helper functions, new variables, or logic rearrangement unless absolutely required by the fix.
- All identifiers (e.g., function names, variable names, struct fields, constants, etc.) must remain unchanged.
- Preserve all comments in the Rust code, and do not introduce any new comments.
- All `for` loops in the C code must remain as `while` loops in Rust if translated that way.
- **Do not use raw pointers or pointer conversion methods (e.g., `as_ptr()`, `as_mut_ptr()`, or casting references to pointers).**
- Avoid using `unsafe` blocks in Rust unless absolutely necessary.
- Make minimal edits necessary to fix the errors.
- Output only the corrected Rust code, without any additional explanations.
- **The final corrected Rust code must be wrapped in a fenced code block starting with ` ```rust ` and ending with ` ``` `.**
    
**Original C Program:**
```c
{c_code}
```

**Rust Program (with Compilation Errors):**
```rust
{rust_code}
```

**rustc Compiler Errors:**
```bash
{error_msg}
```

**Repaired Rust Program:**
"""
    return prompt


def transpile_prompt_v2(context, code, signature):
    prompt = f"""You are a code translator specializing in converting C code to safe, idiomatic Rust code.

### Task Overview

You are given:
1. An **existing Rust file context**, which provides all necessary definitions.
2. A **C function** that needs to be translated into Rust.
3. A **target Rust function signature**, which defines the exact name, parameters, and return type that your translated function must use.

Your goal is to **translate only the given C function** into valid, safe Rust — assuming that everything in the provided Rust context already exists and does not need to be redefined.
    
### Guidelines:
- The translated Rust code should be a line-by-line reimplementation that mirrors the original C structure as closely as possible in both syntax and control flow.
- Ensure that the translated Rust code maintains the same **behavior** and **control structure** as the original C code.
- Convert C pointer types (`T*`) into Rust references (`&T` or `&mut T`), depending on mutability.
- Always convert `for` loops in C into semantically equivalent `while` loops in Rust.
- If a type (such as an `enum`) or a module contains multiple named items (such as variants or constants) that are used in the code, the Rust translation should include `use Type::*;` or `use module::*;` to allow unqualified access.
- **Preserve all comments from the original C code**, ideally at the corresponding locations.
- **Do not use raw pointers or pointer conversion methods (e.g., `as_ptr()`, `as_mut_ptr()`, or casting references to pointers).**
- Avoid using `unsafe` blocks in Rust unless absolutely necessary.
- Do not change any identifiers (such as variable names, function names, struct names, etc.) from the original C code.
- **Do not introduce any new comments** that were not present in the original C code.
- Output only the translated Rust code, without any additional explanations.
- **The final translated Rust code must be wrapped in a fenced code block starting with ` ```rust ` and ending with ` ``` `.**

### Examples:

*Example 1:*
Input:
```c
struct Person {{
    int height;
    int age;
}};

enum Color {{
    RED,
    GREEN,
    BLUE
}};

int main() {{
    enum Color c = GREEN;
    if (c == GREEN) {{
        c = BLUE;
    }}
    struct Person p = {{170, 30}};
    p.age += 1;
    return 0;
}}
```
Output:
```rust
struct Person {{
    height: i32,
    age: i32,
}}

#[derive(PartialEq)]
enum Color {{
    RED,
    GREEN,
    BLUE,
}}

use Color::*;

fn main() {{
    let mut c: Color = GREEN;
    if c == GREEN {{
        c = BLUE;
    }}
    let mut p: Person = Person {{
        height: 170,
        age: 30,
    }};
    p.age += 1;
}}
```

*Example 2:*
Input:
```c
void reverse(int* arr, int len){{
    for (int i = 0; i < len / 2; i++) {{
        int tmp = arr[i];
        arr[i] = arr[len - 1 - i];
        arr[len - 1 - i] = tmp;
    }}
}}

int sum_vector(int* vec, int len) {{
    int sum = 0;
    // verus_assert(1);
    for (int i = 0; i < len; i++) {{
        sum += vec[i];
    }}
    return sum;
}}
```
Output:
```rust
fn reverse(arr: &mut [i32], len: i32) {{
    let mut i: i32 = 0;
    while i < len / 2 {{
        let tmp: i32 = arr[i as usize];
        arr[i as usize] = arr[(len - 1 - i) as usize];
        arr[(len - 1 - i) as usize] = tmp;
        i += 1;
    }}
}}

fn sum_vector(vec: &[i32], len: i32) -> i32 {{
    let mut sum: i32 = 0;
    // verus_assert(1);
    let mut i: i32 = 0;
    while i < len {{
        sum += vec[i as usize];
        i += 1;
    }}
    sum
}}
```

*Example 3:*
Input:
```c
#include <stdio.h>
#include <string.h>

int THRESHOLD = 100;

int CheckAndCount(int* ptr) {{
    if (*ptr > THRESHOLD) {{
        return *ptr;
    }} else {{
        return THRESHOLD;
    }}
}}

void foo(const char *input) {{
    int len = strlen(input);
    // verus_assert(1);
}}

void Test() {{
}}
```
Output:
```rust
const THRESHOLD: i32 = 100;

fn CheckAndCount(ptr: &i32) -> i32 {{
    if *ptr > THRESHOLD {{
        *ptr
    }} else {{
        THRESHOLD
    }}
}}

fn foo(input: &str) {{
    let len: i32 = input.len() as i32;
    // verus_assert(1);
}}

fn Test() {{
}}
```

### Input:

[Existing Rust Context]:
```rust
{context}
```

[C Function]:
```c
{code}
```

[RUST SIGNATURE]:
```rust
{signature}
```

### Output
"""
    return prompt


if __name__ == "__main__":
    prompt_switcher = PromptSwitcher()
    prompt1 = prompt_switcher.function_prompt(
        c_code="int a;", context="struct S { int x; };"
    )
    print(prompt1)
