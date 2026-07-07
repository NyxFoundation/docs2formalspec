import D2fsSpecs.BlastRadius

/-!
# In-scope safety: protocol-design soundness against an ordinary (honest-roles) attacker

Third verification pillar (see `docs/06-safety-properties.md`). Distinct from requirement
conformance (`Apyx.lean`) and key-compromise blast radius (`BlastRadius.lean`): here every role
behaves honestly, and we ask whether the *design itself* lets a normal attacker — using only
legitimate operations in a clever order/amount/timing — extract value unfairly or create value
from nothing. Mostly trace-level generalizations of single-step lemmas already proved elsewhere.

Additive: `Apyx.lean` and `BlastRadius.lean` are untouched.
-/

namespace Apyx

end Apyx
