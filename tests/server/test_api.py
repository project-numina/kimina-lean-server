import os
import textwrap
import time
import uuid

import psutil

from server.leanrepl import LeanREPL
from utils.proof_utils import has_error_response, parse_client_response


class TestLeanServer:
    def setup_method(self):
        self.api_key = os.environ.get("LEANSERVER_API_KEY", "")
        self.headers = {
            "Content-Type": "application/json",
            "Accept": "application/json",
            "Authorization": f"Bearer {self.api_key}",
        }
        self.timeout = 60

    def test_verify(self, test_client):
        """verifying batch simple proof."""
        data = {
            "codes": [
                {
                    "custom_id": str(uuid.uuid4()),
                    "proof": """import Mathlib\n\ndef f := 2\nexample : f = 2 := rfl""",
                }
                for _ in range(5)
            ],
            "timeout": self.timeout,
        }

        response = test_client.post("/verify", json=data, headers=self.headers)
        assert response.status_code == 200
        assert all(r["error"] is None for r in response.json()["results"]) is True

    def test_verify_warning(self, test_client):
        """Test a proof with warnings."""
        proof_code = textwrap.dedent(
            """\
            import Mathlib

            theorem number_theory_3784 (k m : ℕ) (hm : Odd m) (hk : 0 < k) :
                ∃ n : ℕ, 0 < n ∧ (n ^ n - m) % (2 ^ k) = 0 := by
            use 1
            constructor
            norm_num
            cases' hm with m hm
            simp [Nat.pow_succ, Nat.mul_mod, Nat.pow_mod, hm]
        """
        )

        data = {
            "codes": [{"proof": proof_code, "custom_id": "0"}],
            "timeout": self.timeout,
        }

        response = test_client.post("/verify", json=data, headers=self.headers)
        assert response.status_code == 200
        response = response.json()
        assert not has_error_response(response["results"][0]["response"])
        assert "warning" in str(response["results"][0]["response"])

    def test_verify_correct(self, test_client):
        """Test a correct proof without warnings or errors."""
        proof_code = textwrap.dedent(
            """\
            import Mathlib

            theorem algebra_260 (x : ℝ) (hx : x ≠ 0) : 1 / 2 - 1 / 3 = 1 / x ↔ x = 6 := by
            field_simp
            constructor
            intro h
            apply Eq.symm
            linarith
            intro h
            rw [h]
            norm_num
            """
        )

        data = {
            "codes": [{"proof": proof_code, "custom_id": "0"}],
            "timeout": self.timeout,
        }

        response = test_client.post("/verify", json=data, headers=self.headers)
        expected_output = {"error": None, "response": {"env": 0}}
        assert response.status_code == 200
        response = response.json()
        assert expected_output["error"] == response["results"][0]["error"]
        assert "env" in response["results"][0]["response"]
        assert "time" in response["results"][0]["response"]

    def test_verify_error(self, test_client):
        """Test a proof that results in an error."""
        proof_code = textwrap.dedent(
            """\
        import Mathlib

        theorem algebra_158 {a b : ℕ} (ha : a > b) (h : ∀ x, x^2 - 16 * x + 60 = (x - a) * (x - b)) :
            3 * b - a = 8 := by
          have h₁ := h 0
          have h₂ := h 1
          have h₃ := h 2
          have h₄ := h 3
          simp at h₁ h₂ h₃ h₄
          ring_nf at h₁ h₂ h₃ h₄
          omega
        """
        )

        data = {
            "codes": [{"proof": proof_code, "custom_id": "0"}],
            "timeout": self.timeout,
        }

        response = test_client.post("/verify", json=data, headers=self.headers)
        assert response.status_code == 200
        response = response.json()
        assert has_error_response(response["results"][0]["response"])

    def test_verify_sorry(self, test_client):
        proof_code = textwrap.dedent(
            """\
        import Mathlib

        theorem algebra_158 {a b : ℕ} (ha : a > b) (h : ∀ x, x^2 - 16 * x + 60 = (x - a) * (x - b)) :
            3 * b - a = 8 := by sorry
        """
        )

        data = {
            "codes": [{"proof": proof_code, "custom_id": "0"}],
            "timeout": self.timeout,
        }

        response = test_client.post("/verify", json=data, headers=self.headers)
        assert response.status_code == 200
        response = response.json()

        result = parse_client_response(response["results"][0])
        assert result["is_valid_with_sorry"]
        assert not result["is_valid_no_sorry"]

    def test_repl_close_graceful_termination(self):
        """Test that calling close() on a LeanREPL instance terminates the process gracefully."""
        # Create a new REPL instance
        repl = LeanREPL()

        # Get the process ID
        pid = repl.process.pid

        # Verify the process is running
        assert repl.process.poll() is None
        assert psutil.pid_exists(pid)

        # Create child processes tracker
        parent = psutil.Process(pid)
        children_before = parent.children(recursive=True)
        child_pids = [p.pid for p in children_before]

        # Execute a simple command to verify the REPL is working
        response = repl.one_pass_verify(
            "def f := 2\nexample : f = 2 := rfl", timeout=10
        )
        assert "error" not in response or not response["error"]

        # Call the close method
        repl.close()

        # Give it a moment to terminate
        start_time = time.time()
        max_wait_time = 5  # seconds

        # Wait for the process to terminate or timeout
        while repl.process.poll() is None and time.time() - start_time < max_wait_time:
            time.sleep(0.1)

        # Verify the process has terminated
        assert (
            repl.process.poll() is not None
        ), "Process did not terminate within timeout"

        # Verify that child processes have also terminated
        time.sleep(0.5)  # Give child processes time to terminate
        for child_pid in child_pids:
            assert not psutil.pid_exists(
                child_pid
            ), f"Child process {child_pid} is still running"

        # Verify we can create a new REPL after closing the old one
        new_repl = LeanREPL()
        assert new_repl.process.poll() is None
        new_repl.close()

    def test_repl_close_after_multiple_commands(self):
        """Test that calling close() works after executing multiple commands."""
        repl = LeanREPL()

        # Run a series of commands
        commands = [
            "def f := 2\nexample : f = 2 := rfl",
            "theorem simple_add : 2 + 2 = 4 := by simp",
            "def g (x : Nat) := x + 1\nexample : g 5 = 6 := rfl",
        ]

        for cmd in commands:
            response = repl.one_pass_verify(cmd, timeout=10)
            assert "error" not in response or not response["error"]

        # Now close the REPL
        repl.close()

        # Verify the process has terminated
        assert (
            repl.process.poll() is not None
        ), "Process did not terminate after close()"

    def test_repl_del_calls_close(self):
        """Test that deleting a LeanREPL instance calls close() implicitly."""
        repl = LeanREPL()
        pid = repl.process.pid

        # Verify the process is running
        assert psutil.pid_exists(pid)

        # Delete the repl instance
        del repl

        # Give it a moment to terminate
        time.sleep(1)

        # Verify the process has terminated
        assert not psutil.pid_exists(pid), "Process did not terminate after __del__"

    def test_repl_create_close_multiple(self):
        """Test creating and closing multiple REPL instances in sequence."""
        for _ in range(3):
            repl = LeanREPL()
            pid = repl.process.pid

            # Verify the process is running
            assert repl.process.poll() is None

            # Run a simple command
            response = repl.one_pass_verify("def f := 2", timeout=10)
            assert "error" not in response or not response["error"]

            # Close the REPL
            repl.close()

            # Verify the process has terminated
            assert repl.process.poll() is not None
            assert not psutil.pid_exists(pid)
