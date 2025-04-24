import os
import textwrap
import uuid

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
