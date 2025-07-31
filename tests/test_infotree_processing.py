from kimina_client import KiminaClient
from kimina_client.infotree import extract_data

def test_infotree_processing() -> None:
    client = KiminaClient()

    with open('examples/demo_search_2.lean', 'r') as file:
        code = file.read()

    check_response = client.check(code, infotree="original")
    result = check_response.results[0]
    infotree = result.response["infotree"]
    data = extract_data(infotree, code)

    assert len(data) == 11
    assert data[0]["tactic"] == 'by\n  have h₁ : 0 < a + b + c :='
    assert data[0]["goalsBefore"] == ['a b c : ℝ\nha : 0 < a\nhb : 0 < b\nhc : 0 < c\n⊢ a ^ 2 / (b + c) + b ^ 2 / (a + c) + 16 * c ^ 2 / (a + b) ≥ 1 / 9 * (64 * c - a - b)']
    assert data[0]["goalsAfter"] == ['a b c : ℝ\nha : 0 < a\nhb : 0 < b\nhc : 0 < c\n⊢ 0 < a + b + c']