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


MULTILINE = """\
namespace X

def step (n : Nat) : Nat := n + 1

theorem req_multi (n : Nat) :
    step n = n + 1 →
    let m := step n
    m > n := by
  simp [step]

theorem req_term (n : Nat) : step n = n + 1 := rfl

theorem req_broken_stmt (n : Nat) :
    let s' := sorry

end X
"""


def test_multiline_statement_with_let_preserved():
    # error inside req_multi's proof (line 10 = "  simp [step]")
    out, n = sorry_stub_failing_proofs(MULTILINE, "X.lean:10:2: unknown tactic")
    assert n == 1
    assert "let m := step n" in out          # statement kept, incl. inner :=
    assert "m > n := sorry" in out           # only proof replaced
    assert "-- BROKEN" not in out


def test_term_proof_killed_not_mangled():
    out, n = sorry_stub_failing_proofs(MULTILINE, "X.lean:12:40: type mismatch")
    assert n == 1
    assert "-- BROKEN: theorem req_term" in out


def test_broken_statement_killed():
    out, n = sorry_stub_failing_proofs(MULTILINE, "X.lean:15:14: unexpected token")
    assert n == 1
    assert "-- BROKEN: theorem req_broken_stmt" in out


def test_find_vacuous():
    assert find_vacuous("theorem t : True := sorry") == ["t"]
    assert find_vacuous("theorem t (s : S) : s.x = 1 := sorry") == []
