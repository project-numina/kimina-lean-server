import json
import os
import signal
import subprocess
import tempfile
import threading
import time

from func_timeout import FunctionTimedOut, func_timeout  # type: ignore
from loguru import logger

from utils.proof_utils import get_error_msg

from .config import settings

base = settings.WORKSPACE

path_to_repl = f"{base}/repl/.lake/build/bin/repl"
path_to_mathlib = f"{base}/mathlib4"


# error for lean crashes
class LeanCrashError(Exception):
    pass


class LeanREPL:
    def __init__(self):
        # Start the REPL process
        self.error_file = tempfile.TemporaryFile(
            "w+",
        )
        self.start_process()
        # Create a lock for thread safety
        self.lock = threading.Lock()
        self.header = None

    def _send_command(self, command):
        """
        Send a JSON command to the REPL and return the JSON response.
        """

        with self.lock:
            try:
                # Convert the command to JSON and add two newlines
                json_command = json.dumps(command, ensure_ascii=False) + "\n\n"
                # Send the command to the REPL
                time_elapsed = time.time()
                self.process.stdin.write(json_command)
                self.process.stdin.flush()

                # Read the response until a blank line is encountered
                response_lines = []
                stderr_lines = []

                while True:
                    # Read from both stdout and stderr
                    stdout_line = self.process.stdout.readline()

                    if stdout_line.strip() == "":
                        break

                    if stdout_line:
                        response_lines.append(stdout_line)
            except BrokenPipeError:
                raise LeanCrashError("Lean process broken pipe error")

            # Combine the response lines and parse the JSON
            response_str = "".join(response_lines)
            time_elapsed = time.time() - time_elapsed
            try:
                response_json = json.loads(response_str)
            except json.JSONDecodeError as e:
                logger.error("Error decoding JSON:", e)
                logger.error("Response received:", response_str)
                response_json = {
                    "messages": [
                        {
                            "severity": "error",
                            "data": "error decoding json response in leanrepl",
                        }
                    ]
                }

            error_content = self.get_error_content()
            if len(error_content.strip()) > 0:
                logger.error("Error from stderr: %s", error_content)
                raise LeanCrashError(
                    f"Lean process encountered an error: {error_content}"
                )
            response_json["time"] = time_elapsed
            return response_json

    def one_pass_verify(self, code, timeout, infotree_type=None):
        """
        Send code to verify in one pass.
        """
        if infotree_type is None:
            command = {"cmd": code}
        else:
            command = {"cmd": code, "infotree": infotree_type}
        try:
            response = func_timeout(timeout, self._send_command, args=(command,))
        except FunctionTimedOut:
            raise LeanCrashError("Lean process timed out")
        return response

    def create_env(self, code, timeout=150):
        """
        Send code to create a new context.
        """
        command = {"cmd": code}
        try:
            response = func_timeout(timeout, self._send_command, args=(command,))
        except FunctionTimedOut:
            raise LeanCrashError("Lean process timed out")
        if get_error_msg(response) is None:
            self.header = code
        return response

    def extend_env(self, context_id, code, timeout=150, infotree_type=None):
        """
        Send code to extend a context.
        """
        if infotree_type is None:
            command = {"cmd": code, "env": context_id}
        else:
            command = {"cmd": code, "env": context_id, "infotree": infotree_type}
        try:
            response = func_timeout(timeout, self._send_command, args=(command,))
        except FunctionTimedOut:
            raise LeanCrashError("Lean process timed out")
        return response

    def start_process(self):
        self.process = subprocess.Popen(
            ["lake", "env", path_to_repl],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=self.error_file,
            text=True,
            bufsize=1,  # Line-buffered
            cwd=path_to_mathlib,  # Set the working directory to 'mathlib4'
            env=os.environ,  # Inherit environment variables
            preexec_fn=os.setsid,
        )

    def get_error_content(self):
        # Ensure that we seek back to the beginning of the file before reading
        if self.error_file is None:
            print("Error file is None")
        self.error_file.seek(0)
        return self.error_file.read()

    def close(self):
        """
        Terminate the REPL process and all its child processes.
        """
        try:
            # stop input to repl (which will result in the program loop for lean repl terminating)
            self.process.stdin.close()
        except ProcessLookupError:
            # Process already terminated
            pass
        finally:
            # Wait for the process to exit
            self.process.wait()

    def __del__(self):
        self.close()
