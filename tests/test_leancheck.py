from d2fs.leancheck import (
    build_file,
    is_theorem_block,
    kill_block,
    split_decls,
    split_theorem_region,
    stub_block,
)
from d2fs.leangen import find_vacuous

CODE = """\
namespace X

def step (n : Nat) : Nat := n + 1

-- Requirements as theorems

/-- REQ a: statement a -/
theorem req_a (n : Nat) : step n = n + 1 := by
  simp [step]

/-- REQ multi -/
theorem req_multi (n : Nat) :
    step n = n + 1 →
    let m := step n
    m > n := by
  simp [step]

theorem req_term (n : Nat) : step n = n + 1 := rfl

end X
"""


def test_split_and_reassemble_roundtrip():
    model, region = split_theorem_region(CODE, "X")
    assert "def step" in model and "theorem" not in model
    blocks = split_decls(region)
    thm_blocks = [b for b in blocks if is_theorem_block(b)]
    assert len(thm_blocks) == 3
    assert thm_blocks[0].startswith("/-- REQ a")
    text, offsets = build_file(model, blocks, "X")
    assert sum(l.startswith("theorem") for l in text.splitlines()) == 3
    assert text.rstrip().endswith("end X")
    assert len(offsets) == len(blocks)
    # offsets must locate each block in the assembled text
    lines = text.splitlines()
    for b, (lo, hi) in zip(blocks, offsets):
        first = b.splitlines()[0]
        assert first in lines[lo - 1 : hi]


def test_stub_block_multiline_let():
    model, reg = split_theorem_region(CODE, "X")
    blocks = [b for b in split_decls(reg) if is_theorem_block(b)]
    stubbed = stub_block(blocks[1])
    assert "let m := step n" in stubbed  # inner := untouched
    assert stubbed.rstrip().endswith(":= sorry")
    assert ":= by" not in stubbed


def test_stub_block_term_proof_kills():
    model, reg = split_theorem_region(CODE, "X")
    blocks = [b for b in split_decls(reg) if is_theorem_block(b)]
    killed = stub_block(blocks[2])  # term-mode rfl proof
    assert all(l.startswith("-- BROKEN:") for l in killed.splitlines())


def test_kill_block_idempotent():
    once = kill_block("theorem t : True := sorry")
    twice = kill_block(once)
    assert once == twice


def test_find_vacuous():
    assert find_vacuous("theorem t : True := sorry") == ["t"]
    assert find_vacuous("theorem t (s : S) : s.x = 1 := sorry") == []
