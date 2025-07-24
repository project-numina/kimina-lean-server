import nest_asyncio

from client import Lean4Client

# Enable nested asyncio for Jupyter notebooks
nest_asyncio.apply()

client = Lean4Client(base_url="http://localhost:8000")
mock_proof = """import Mathlib
import Aesop

set_option maxHeartbeats 0

open BigOperators Real Nat Topology Rat

theorem lean_workbook_10009 (a b c: ℝ) (ha : a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 ∧ a + b + c = 1): a^3 + b^3 + c^3 + (15 * a * b * c)/4 ≥ 1/4 := by

nlinarith [sq_nonneg (a - b), sq_nonneg (b - c), sq_nonneg (c - a),
sq_nonneg (a + b + c)]"""

response = client.verify(
    [{"proof": mock_proof, "custom_id": "1"}, {"proof": mock_proof, "custom_id": "2"}],
    timeout=30,
)

# Expected response format:

# ```json
# {
#     "results":
#     [
#         {
#             "custom_id": "1",
#             "error": null,
#             "response": {
#                 "messages": [
#                     {
#                         "severity": "error",
#                         "pos": {"line": 8, "column": 0},
#                         "endPos": {"line": 9, "column": 22},
#                         "data": "linarith failed to find a contradiction\ncase a\na b c : ℝ\nha : a ≥ 0 ∧ b ≥ 0 ∧ c ≥ 0 ∧ a + b + c = 1\na✝ : 1 / 4 > a ^ 3 + b ^ 3 + c ^ 3 + 15 * a * b * c / 4\n⊢ False\nfailed"
#                     }
#                 ],
#                 "env": 1,
#                 "time": 1.0048656463623047
#             }
#         },
#         {
#             "custom_id": "2",
#             "..."
#         }
#     ]
# }
# ```
