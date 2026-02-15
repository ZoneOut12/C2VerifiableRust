# Migration Framework C2VR
The objective of this work is to study the migration of formally specified C programs (i.e., C programs annotated with ACSL specifications) into verifiable Rust with Verus specifications.

This repository contains dataset and source code for migration.
- `data`: contains the benchmark used in the experiments.
- `src`: contains the source code of the framework.
- `transpiled_rust`: contains the transpiled Rust code.
- `RQ1_result`, `RQ3_result`: contains main experimental results of our research questions.

As RQ2 primarily involves manual analysis of the benchmarks and their migration outcomes produced by our framework, it does not have a dedicated directory.

## Pre-requisites
Our experiments are conducted on Ubuntu. To configure the environment, basic commands like `wget`, `curl`, and `unzip` should be available.

**Set up the Python environment:**
1. Install `conda`:
    ```bash
    cd ~
    wget https://repo.anaconda.com/miniconda/Miniconda3-latest-Linux-x86_64.sh
    bash Miniconda3-latest-Linux-x86_64.sh
    source ~/miniconda3/bin/activate
    conda init
    ```
2. Switch to the `C2VerifiableRust` directory, and create the virtual environment used in our experiments:
    ```bash
    conda env create -f environment.yml
    conda activate migration
    ```
**Install the Rust toolchain:**
```bash
curl --proto '=https' --tlsv1.2 -sSf https://sh.rustup.rs | sh
source $HOME/.cargo/env
```

**Install the Verus formatter:** 
```bash
sudo apt update
sudo apt install build-essential
cargo install verusfmt
```

**Install [Verus](https://github.com/verus-lang/verus):** Version used in our experiments: 0.2025.06.14.9b557d7
```bash
wget -O ~/verus-0.2025.06.14.9b557d7-x86-linux.zip https://github.com/verus-lang/verus/releases/download/release%2F0.2025.06.14.9b557d7/verus-0.2025.06.14.9b557d7-x86-linux.zip
unzip ~/verus-0.2025.06.14.9b557d7-x86-linux.zip -d ~
rustup toolchain install 1.85.1-x86_64-unknown-linux-gnu
```

**Install [CVC5](https://github.com/cvc5/cvc5) and add it to the system path:** Version used in our experiments: 1.2.2-dev.306.a7fef6990 [git a7fef6990 on branch main]
1. First, install cvc5.
    ```bash
    wget https://github.com/cvc5/cvc5/releases/download/cvc5-1.3.0/cvc5-Linux-x86_64-static.zip -P ~/
    unzip ~/cvc5-Linux-x86_64-static.zip -d ~/
    ```
2. Next, you need to add the CVC5 binary to your system's PATH.
    - Open your shell configuration file (e.g., `~/.bashrc`).
    - Add the following line to the file:
        ```bash
        export PATH="$HOME/cvc5-Linux-x86_64-static/bin:$PATH"
        ```
    - Save the file and close it.
    - Apply the changes by running:
        ```bash
        source ~/.bashrc
        ```
    - Verify that CVC5 is installed by running:
        ```bash
        cvc5 --version
        ```

**Install rust-analyzer:**
```bash
rustup component add rust-analyzer
```

**Install clang-format:**
```bash
sudo apt install clang-format
```

**Additional notes:**

The framework requires network access during runtime as it invokes Git and Cargo commands.

If you cannot access the internet directly, configure Git to use a proxy with:
```bash
git config --global http.proxy http://proxy-server:port
git config --global https.proxy http://proxy-server:port
``` 

## Usage
First, make sure you are in the `migration` Conda virtual environment.

### Configuration
Before running the framework, you need to fill in the required parameters in the `src/config.toml` file:
- `"dataset_txt"`: a `.txt` file listing source C file paths, one per line. We provide several `.txt` files within the `data/dataset_path` directory. Among them, `supported_benchmark.txt` stores the file paths of 173 migratable C programs.
- `"log_file"`: the path to the log file used to record the framework's execution details.
- `"result_dir"`: the directory where the output results of the framework execution are stored.
- `"verus"`: the path to the Verus binary used for verifying Rust. If you're following the steps for Verus installation, the default path for the Verus binary will be `~/verus-x86-linux/verus`.
- `"libclang_path"`: libclang library location.
- `"base_url"`, `"api_key"`, `"model_name"`: API configuration parameters.
- `"temperature"`, `"max_tokens"`, `"top_p"`: parameters setting.
- `"repair_round_threshold"`: the maximum number of repair attempts allowed when the initial LLM-translated result fails to compile.
- `"type_guidance"`: guides specification migration.

### Run
Use the following command to run the framework:
```
python -m src.workflow.main
``` 

To use the translated Rust code saved in the `transpiled_rust` directory, which contains the translation results produced by `Qwen3-235B-A22B` during our experiments, you should use the following command:
```
python -m src.workflow.main -l
``` 

## ⚠️Note
If you choose not to use our pre-translated results and instead specify your own LLM, the translation quality may vary, potentially leading to changes in migration results. In some cases, limitations of the LLM may lead to incomplete or incorrect translations, which could cause unexpected runtime failures.