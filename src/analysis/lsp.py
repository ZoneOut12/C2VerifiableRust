import subprocess, json, os, shutil
from pathlib import Path
from urllib.request import pathname2url
from urllib.parse import urlparse, unquote


class RustAnalyzerClient:
    def __init__(self, logger=None):
        self.logger = logger
        self.proc = subprocess.Popen(
            ["rust-analyzer"],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
        )
        self._id = 0
        self.processed_file = None
        self.target_project_path = None

    def _next_id(self):
        self._id += 1
        return self._id

    def initialize(self, target_project_dir):
        self.create_temp_rs_project(target_project_dir)
        init_id = self._next_id()
        # self.printlog(self.target_project_path)
        project_path = Path(self.target_project_path).resolve()
        project_uri = "file://" + pathname2url(str(project_path))
        self.send_request(
            {
                "jsonrpc": "2.0",
                "id": init_id,
                "method": "initialize",
                "params": {
                    "processId": None,
                    # "rootUri": "file://" + self.target_project_path,
                    "rootUri": project_uri,
                    "capabilities": {"window": {"workDoneProgress": True}},
                    "workspaceFolders": [
                        # {
                        # "uri": f"file://{self.target_project_path}",
                        # "name": "ra_test"
                        # }
                        {"uri": project_uri, "name": "ra_test"}
                    ],
                },
            }
        )

        self.printlog("→ initialize")
        resp = self.wait_for_response(init_id)
        # self.printlog("←", json.dumps(resp, indent=2))

        # send "initialized" notification
        self.send_request({"jsonrpc": "2.0", "method": "initialized", "params": {}})

    def send_request(self, msg_dict):
        msg = json.dumps(msg_dict)
        header = f"Content-Length: {len(msg)}\r\n\r\n"
        self.proc.stdin.write(header.encode("utf-8"))
        self.proc.stdin.write(msg.encode("utf-8"))
        self.proc.stdin.flush()

    def read_response(self):
        def _read_line():
            line = b""
            while not line.endswith(b"\r\n"):
                line += self.proc.stdout.read(1)
            return line.decode("utf-8")

        # Parse headers
        headers = {}
        while True:
            line = _read_line()
            if line == "\r\n":
                break
            key, val = line.strip().split(": ", 1)
            headers[key] = val
        content_length = int(headers["Content-Length"])
        content = self.proc.stdout.read(content_length).decode("utf-8")
        return json.loads(content)

    def wait_for_diagnostics(self, expected_uri):
        while True:
            msg = self.read_response()
            # self.printlog(msg)
            if msg.get("method") == "textDocument/publishDiagnostics":
                if msg["params"]["uri"] == expected_uri:
                    self.printlog("← diagnostics ready")
                    return

    def wait_for_response(self, expected_id=None):
        """
        wait for a response from the language server
        """
        while True:
            msg = self.read_response()
            if msg is None:
                continue
            # listen to rust-analyzer's "progress" completion signal
            if msg.get("method") == "$/progress":
                token = msg["params"].get("token")
                value = msg["params"].get("value", {})
                kind = value.get("kind")
                if token == "rustAnalyzer/cachePriming" and kind == "end":
                    self.printlog("Rust-analyzer ready for next request")
                    break
            # return other types of responses, such as hover, completion, etc.
            elif msg.get("id") is not None:
                if msg["id"] == expected_id:
                    return msg

    def printlog(self, *args, sep=" ", end="\n"):
        msg = sep.join(str(arg) for arg in args) + end
        if self.logger:
            self.logger.info(msg)
        else:
            print(*args, sep=sep, end=end)

    def did_open(self):
        """
        Constructs a LSP 'textDocument/didOpen' notification message to inform
        the language server that a file at the given path has been opened,
        sending its content.

        Args:
            text (str): The full text content of the file.

        Returns:
            dict: A JSON-RPC formatted message dictionary compliant with the LSP specification,
            ready to be sent to the language server.
        """
        file_path = self.processed_file
        text = ""
        with open(file_path, "r", encoding="utf-8") as f:
            text = f.read()
        # self.printlog(text)
        self.send_request(
            {
                "jsonrpc": "2.0",
                "method": "textDocument/didOpen",
                "params": {
                    "textDocument": {
                        "uri": f"file://{file_path}",
                        "languageId": "rust",
                        "version": 1,
                        "text": text,
                    }
                },
            }
        )
        self.printlog("→ didOpen", file_path)
        file_path = Path(file_path).resolve()
        self.wait_for_diagnostics(f"file://{file_path}")

        self.wait_for_response()

    def did_change(self, new_text):
        """
        Constructs a JSON-RPC notification message for the LSP 'textDocument/didChange' method.

        This message notifies the language server that the content of an opened text document
        has changed. It provides the updated full text content of the file so that the server
        can re-analyze and update its semantic information accordingly.

        Parameters:
        - new_text (str): The full new content of the file after the change.

        Returns:
        dict: A dictionary representing the LSP JSON-RPC 'didChange' notification message.
        """
        file_path = self.processed_file
        self.send_request(
            {
                "jsonrpc": "2.0",
                "method": "textDocument/didChange",
                "params": {
                    "textDocument": {"uri": f"file://{file_path}", "version": 2},
                    "contentChanges": [{"text": new_text}],
                },
            }
        )
        self.printlog("→ didChange", file_path)
        file_path = Path(file_path).resolve()
        resp = self.wait_for_diagnostics(f"file://{file_path}")
        self.wait_for_response()
        self.printlog("←", json.dumps(resp, indent=2))

    def hover(self, line, character):
        file_path = self.processed_file
        # Construct the LSP hover request message
        req_id = self._next_id()
        self.send_request(
            {
                "jsonrpc": "2.0",
                "id": req_id,
                "method": "textDocument/hover",
                "params": {
                    "textDocument": {"uri": f"file://{file_path}"},
                    "position": {"line": line, "character": character},
                },
            }
        )
        self.printlog("→ hover")
        resp = self.wait_for_response(req_id)
        self.printlog("←", json.dumps(resp, indent=2))

        return resp

    def document_symbol(self):
        file_path = self.processed_file
        req_id = self._next_id()
        self.send_request(
            {
                "jsonrpc": "2.0",
                "id": req_id,
                "method": "textDocument/documentSymbol",
                "params": {"textDocument": {"uri": f"file://{file_path}"}},
            }
        )
        self.printlog("→ documentSymbol")
        resp = self.wait_for_response(req_id)
        self.printlog("←", json.dumps(resp, indent=2))
        return resp

    def inlay_hint(self, start_line, start_char, end_line, end_char):
        file_path = self.processed_file
        req_id = self._next_id()
        self.send_request(
            {
                "jsonrpc": "2.0",
                "id": req_id,
                "method": "textDocument/inlayHint",
                "params": {
                    "textDocument": {"uri": f"file://{file_path}"},
                    "range": {
                        "start": {"line": start_line, "character": start_char},
                        "end": {"line": end_line, "character": end_char},
                    },
                },
            }
        )
        self.printlog("→ inlay_hint")
        resp = self.wait_for_response(req_id)
        self.printlog("←", json.dumps(resp, indent=2))
        return resp

    def get_file_line_count(self, file_path):
        """
        compute the number of lines in a file
        """
        with open(file_path, "r", encoding="utf-8") as f:
            return sum(1 for _ in f)

    def completion(self, line, character):
        file_path = self.processed_file
        req_id = self._next_id()
        self.send_request(
            {
                "jsonrpc": "2.0",
                "id": req_id,
                "method": "textDocument/completion",
                "params": {
                    "textDocument": {"uri": f"file://{file_path}"},
                    "position": {"line": line, "character": character},
                    "context": {"triggerKind": 1},
                },
            }
        )
        self.printlog("→ completion")
        resp = self.wait_for_response(req_id)
        self.printlog("←", json.dumps(resp, indent=2))
        return resp

    def close(self):
        if self.target_project_path and os.path.exists(self.target_project_path):
            shutil.rmtree(self.target_project_path)
            self.printlog(f"Deleted project at {self.target_project_path}")
        else:
            self.printlog(f"Path does not exist: {self.target_project_path}")
        self.proc.terminate()
        self.proc.wait()

    def create_temp_rs_project(self, target_project_dir):
        # Create a new Rust project using cargo new
        target_project_path = os.path.join(target_project_dir, "ra_test")
        self.target_project_path = target_project_path

        if os.path.exists(target_project_path):
            shutil.rmtree(target_project_path)
            self.printlog(f"Deleted existing directory at {target_project_path}")

        subprocess.run(["cargo", "new", target_project_path, "--bin"], check=True)
        self.printlog(f"Created Rust project at {target_project_path}")

    def copy_source_rs(self, source_rs_file):
        # copy the source.rs file into the new project's src/main.rs
        target_project_path = self.target_project_path
        if not os.path.exists(target_project_path):
            raise FileNotFoundError(
                f"Target project directory does not exist: {target_project_path}"
            )

        src_main_rs = os.path.join(target_project_path, "src", "main.rs")
        with open(source_rs_file, "r", encoding="utf-8") as src_file:
            code = src_file.read()
        with open(src_main_rs, "w", encoding="utf-8") as dst_file:
            dst_file.write(code)

        self.processed_file = src_main_rs
        self.printlog(f"Copied {source_rs_file} into {src_main_rs}")

    def extract_inlay_types(self, inlay_response):
        """
        Extracts type hints from a rust-analyzer inlayHint response.

        Args:
            inlay_response (dict): The parsed JSON response from inlayHint request.

        Returns:
            List[Tuple[int, int, str]]: A list of (line, character, type_string) tuples.
        """
        result = []
        for hint in inlay_response.get("result", []):
            label = hint.get("label", "")
            if isinstance(label, str) and label.startswith(": "):
                type_str = label[2:]  # remove leading ": "
                line = hint.get("position", {}).get("line", -1)
                character = hint.get("position", {}).get("character", -1)
                result.append((line, character, type_str))
        return result


if __name__ == "__main__":
    pass
