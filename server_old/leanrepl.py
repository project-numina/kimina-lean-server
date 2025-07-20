import json
import os
import signal
import subprocess
import tempfile
import threading
import time
import psutil
import resource

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
        self.psutil_process = None
        self.children_processes = []
        self.run_command_total = 0 

    def _send_command(self, command):
        """
        Send a JSON command to the REPL and return the JSON response.
        """

        with self.lock:
            try:
                self.run_command_total += 1
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
            command = {"cmd": code, "gc": True}
        else:
            command = {"cmd": code, "infotree": infotree_type, "gc": True}
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
            command = {"cmd": code, "env": context_id, "gc": True}
        else:
            command = {"cmd": code, "env": context_id, "infotree": infotree_type, "gc": True}
        try:
            response = func_timeout(timeout, self._send_command, args=(command,))
        except FunctionTimedOut:
            raise LeanCrashError("Lean process timed out")
        return response

    def start_process(self):
        def preexec_fn():
            if settings.HARD_ENFORCE_MEMORY_LIMIT:
                soft_limit = settings.REPL_MEMORY_LIMIT_GB * 1024 * 1024 * 1024
                hard_limit = soft_limit
                resource.setrlimit(resource.RLIMIT_AS, (soft_limit, hard_limit))

            os.setsid()

        self.process = subprocess.Popen(
            ["lake", "env", path_to_repl],
            stdin=subprocess.PIPE,
            stdout=subprocess.PIPE,
            stderr=self.error_file,
            text=True,
            bufsize=1,  # Line-buffered
            cwd=path_to_mathlib,  # Set the working directory to 'mathlib4'
            env=os.environ,  # Inherit environment variables
            preexec_fn=preexec_fn,
        )

    def get_error_content(self):
        # Ensure that we seek back to the beginning of the file before reading
        if self.error_file is None:
            logger.debug("Error file is None")
        self.error_file.seek(0)
        return self.error_file.read()

    def close(self):
        """
        Terminate the REPL process and all its child processes.
        """
        try:
            # stop input to repl (which will result in the program loop for lean repl terminating)
            self.process.stdin.close()
            os.killpg(os.getpgid(self.process.pid), signal.SIGKILL)
        except ProcessLookupError:
            # Process already terminated
            pass
        finally:
            # Wait for the process to exit
            self.process.wait()

    def __del__(self):
        self.close()

    def exceeds_memory_limit(self, limit_gb):
        """
        Check if the REPL process exceeds the given memory limit.
        Returns True if memory usage exceeds limit, False otherwise.
        """

        if self.psutil_process is None:
            self.psutil_process = psutil.Process(self.process.pid)

        if self.psutil_process is not None:
            try:
                memory_usage = self.psutil_process.memory_info().rss
                try:
                    if not self.children_processes:
                        self.children_processes = self.psutil_process.children()
                        
                    if self.children_processes:
                        child_memory = sum(child.memory_info().rss for child in self.children_processes)
                        total_memory = memory_usage + child_memory
                    else:
                        total_memory = memory_usage
                except Exception as e:
                    logger.error(f"Error getting child processes: {e}")
                    total_memory = memory_usage
                
                logger.debug(f"REPL pid {self.process.pid} using {total_memory/1024/1024/1024:.2f}GB")
                return total_memory > limit_gb * 1024 * 1024 * 1024, total_memory
            except (psutil.NoSuchProcess, psutil.AccessDenied) as e:
                logger.error(f"Error accessing process: {e}")
                return False
            except Exception as e:
                logger.error(f"Error checking memory: {e}")
                return False
        return False
