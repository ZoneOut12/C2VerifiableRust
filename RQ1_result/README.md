## RQ1 Experimental Results

The `RQ1_result` directory contains the core experimental results for Research Question 1 (RQ1), which evaluates the effectiveness of the migration framework. These experiments were conducted on **173** migratable C programs whose paths are recorded in the `data/dataset_path/supported_benchmark.txt`.

We adopted the best migration results from the 'Impact of LLM Choice on Migration Performance' subsection. 

- `migration_success`: 
    This folder contains **128** files that were successfully migrated using the framework, possibly with minimal manual fixes (<= 4 LoC).

- `migration_failure`: 
    This folder contains **45** files where migration failed.

- `success_without_minimal_fix`:
    This folder contains **92** files.