## RQ1 Experimental Results

The `RQ1_result` directory contains the core experimental results for Research Question 1 (RQ1), which evaluates the effectiveness of the migration framework. These experiments were conducted on **175** migratable C programs whose paths are recorded in the `data/dataset_path/supported_benchmark.txt`.

We adopted the best migration results from the 'Impact of Translation Engine Choice on Migration Performance' subsection.

- `success_without_fixes`:
    This folder contains **92** files that were successfully migrated using the framework with type guidance but without manual fixes.

- `success_with_fixes`:
    This folder contains **139** files that were successfully migrated using the framework with type guidance and manual fixes.

### Reproducing the Impact of Type-Guided Specification Migration

To compare the **Type-Guided** and **Type-Agnostic** configurations, set the `type_guidance` field in `src/config.toml`:

- `type_guidance = true`: Enable type-guided specification migration (default).
- `type_guidance = false`: Disable type guidance (type-agnostic mode).

Then run the main workflow:
```bash
python -m src.workflow.main
```

### Reproducing the Impact of Translation Engine Choice on Migration Performance

1. **Different LLMs as translation engine**: Specify the desired LLM in `src/config.toml`, then run the main workflow:
   ```bash
   python -m src.workflow.main
   ```

2. **C2Rust as translation engine**: Run the following command from the project root directory:
   ```bash
   python -m src.workflow.main -c
   ```

### Reproducing the Impact of Specification-Guided Code Translation

1. Run the spec-guided translation to obtain Rust code translated with ACSL annotations as context:
   ```bash
   python -m src.c2rust.transpile_with_spec
   ```

2. Rename the output directory so C2VR can use the pre-translated results:
   ```bash
   mv transpiled_rust_with_spec transpiled_rust
   ```

3. Run the main workflow with the `-l` flag to skip translation and use the pre-translated Rust code:
   ```bash
   python -m src.workflow.main -l
   ```
