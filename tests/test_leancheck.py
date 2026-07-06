from d2fs.leancheck import sorry_stub_failing_proofs
from d2fs.leangen import find_vacuous


CODE = """\
namespace X

def step (n : Nat) : Nat := n + 1

/-- REQ a -/
theorem req_a (n : Nat) : step n = n + 1 := by
  aesop

/-- REQ b -/
theorem req_b (n : Nat) : step n > n := by
  simp [step]

end X
"""


def test_stub_failing_proof_keeps_statement():
    # error inside req_a's proof body (line 7 = "  aesop")
    out, n = sorry_stub_failing_proofs(CODE, "D2fsSpecs/X.lean:7:2: unknown tactic")
    assert n == 1
    assert "theorem req_a (n : Nat) : step n = n + 1 := sorry" in out
    assert "simp [step]" in out  # req_b untouched


def test_no_errors_no_change():
    out, n = sorry_stub_failing_proofs(CODE, "some unrelated output")
    assert n == 0
    assert out == CODE


def test_error_in_def_not_stubbed():
    out, n = sorry_stub_failing_proofs(CODE, "D2fsSpecs/X.lean:3:10: type mismatch")
    assert n == 0


def test_find_vacuous():
    assert find_vacuous("theorem t : True := sorry") == ["t"]
    assert find_vacuous("theorem t (s : S) : s.x = 1 := sorry") == []
