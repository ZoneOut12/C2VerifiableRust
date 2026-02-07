## RQ3 Experimental Results

The `RQ3` folder contains three subfolders:
- `Failed`: This folder contains **81** files that failed migration without any manual fix. 

    Based on these files, failure symptoms were summarized into three categories:  
    - Translation misalignment: relevant files are in `translation_misalignment_files.json`.  
    - Compilation errors: relevant files are in `compile_error_files.json`.
    - Verification errors: relevant files are in `verify_error_files.json`.
    
    Also note that files in `translation_misalignment_files.json` and `compile_error_files.json` may overlap.

- `Light_fixed`: This folder contains **36** files that underwent light manual fix (≤ 4 lines of code changed) and successfully passed verification.  
    The average number of modified LoC per file is **2.14**.

- `Full_Fixed`: This folder contains **45** files that underwent full manual repair and successfully passed Verus verification.


> manual repair methods correspond to the **9** repair strategies proposed in the RQ3 section of the paper.