/-!
# `LiquidationBatcher` — bounding the one undelayed keyed role

`0x4dB4D934…b732`, reached by role 41, which carries **no execution delay** and is granted to a
single EOA (`model.md` §6). That combination is what makes it worth a model; reading the contract
is what makes the answer reassuring.

It liquidates on **Morpho Blue** (`0xBBBB…FFCb`), not on Apyx state — Apyx has no per-account
collateral positions, so there is no internal liquidation mechanism here that the rest of the
report is missing. Two construction-time pins bound what the keeper can do:

* the market allowlist is populated in the constructor and **has no setter**;
* `withdrawTokens(asset, amount)` takes **no destination argument** and always transfers to the
  immutable `WITHDRAW_DESTINATION`, which on-chain is the ops Safe.

Neither pausable nor upgradeable. This module states those two bounds as theorems, so that
"undelayed role" and "unbounded role" stay distinguished in the report.
-/

namespace LiquidationBatcher

abbrev Address := Nat
abbrev MarketId := Nat

structure State where
  /-- Fixed in the constructor; no setter exists. -/
  allowed  : MarketId → Bool
  /-- Fixed in the constructor; `withdrawTokens` has no destination parameter. -/
  dest     : Address
  /-- Token balances held by the batcher, per asset. -/
  held     : Address → Nat
  /-- Where proceeds have been sent, per (asset, recipient). -/
  sent     : Address → Address → Nat
deriving Inhabited

inductive Op
  /-- `batchLiquidate`. Fail-closed on the allowlist: a ticket naming a market outside it reverts
      the whole batch. Proceeds accrue on the contract. -/
  | batchLiquidate (markets : List MarketId) (proceedsAsset : Address) (proceeds : Nat)
  | withdrawTokens (asset : Address) (amount : Nat)
deriving DecidableEq

/-- **`caller` is deliberately ignored.** On chain every operation below is role-gated
(`restricted`), but this miniature admits any caller, so each theorem is quantified over an
adversary who may call *anything*. That makes the invariants below **stronger** than their
on-chain counterparts, not weaker — they survive even a total collapse of the role system. The
parameter is kept so the signature matches the other machines' `step`, and so `execTrace` can
carry caller-tagged traces. -/
def step (s : State) (op : Op) (_caller : Address) : Option State :=
  match op with
  | Op.batchLiquidate markets asset proceeds =>
    if markets.any (fun m => ! s.allowed m) then none
    else some { s with held := fun a => if a = asset then s.held a + proceeds else s.held a }
  | Op.withdrawTokens asset amount =>
    if amount = 0 then none
    else if s.held asset < amount then none
    else some { s with
      held := fun a => if a = asset then s.held a - amount else s.held a
      sent := fun a r => if a = asset ∧ r = s.dest then s.sent a r + amount else s.sent a r }

def execTrace (s : State) : List (Op × Address) → State
  | []           => s
  | (op, c) :: σ => match step s op c with
                    | some s' => execTrace s' σ
                    | none    => execTrace s σ

/-- **The allowlist is immutable.** Exhaustive over the closed `Op`: nothing the keeper can call
    widens the set of markets it may liquidate. On-chain the same holds because the mapping has no
    setter at all, and enabling a different market set means deploying a new instance. -/
theorem allowlist_immutable (s : State) (op : Op) (c : Address) (s' : State)
    (h : step s op c = some s') : s'.allowed = s.allowed := by
  cases op <;> simp only [step] at h <;> repeat' split at h
  all_goals first
    | (cases Option.some.inj h; rfl)
    | exact absurd h (by simp)

/-- **The withdrawal destination is immutable.** -/
theorem destination_immutable (s : State) (op : Op) (c : Address) (s' : State)
    (h : step s op c = some s') : s'.dest = s.dest := by
  cases op <;> simp only [step] at h <;> repeat' split at h
  all_goals first
    | (cases Option.some.inj h; rfl)
    | exact absurd h (by simp)

/-- **Proceeds can only reach one address.** A successful withdrawal credits `dest` and nobody
    else, whoever called it. -/
theorem withdraw_credits_only_the_pinned_destination (s : State) (c : Address)
    (asset : Address) (amount : Nat) (s' : State)
    (h : step s (Op.withdrawTokens asset amount) c = some s') :
    s'.sent asset s.dest = s.sent asset s.dest + amount ∧
    ∀ r, r ≠ s.dest → s'.sent asset r = s.sent asset r := by
  simp only [step] at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · cases Option.some.inj h
      exact ⟨by simp, fun r hr => by simp [hr]⟩

/-- A ticket naming a market outside the allowlist takes the whole batch down — fail-closed, so a
    keeper cannot slip one unlisted liquidation past inside a large batch. -/
theorem unlisted_market_reverts_the_batch (s : State) (c : Address)
    (markets : List MarketId) (asset : Address) (proceeds : Nat)
    (m : MarketId) (h_mem : m ∈ markets) (h_bad : s.allowed m = false) :
    step s (Op.batchLiquidate markets asset proceeds) c = none := by
  simp only [step]
  have : markets.any (fun m => ! s.allowed m) = true := by
    apply List.any_eq_true.mpr
    exact ⟨m, h_mem, by simp [h_bad]⟩
  simp [this]

/-- **The blast radius of role 41, over a whole trace.** However the keeper sequences liquidations
    and withdrawals, the set of markets stays fixed and every unit that leaves the contract lands
    on the one pinned address. Undelayed, but not unbounded. -/
theorem role41_trace_blast_radius (s : State) (σ : List (Op × Address)) :
    (execTrace s σ).allowed = s.allowed ∧ (execTrace s σ).dest = s.dest := by
  induction σ generalizing s with
  | nil => exact ⟨rfl, rfl⟩
  | cons p σ ih =>
    obtain ⟨op, c⟩ := p
    simp only [execTrace]
    cases hstep : step s op c with
    | none    => exact ih s
    | some s1 =>
      obtain ⟨ha, hd⟩ := ih s1
      exact ⟨by rw [ha, allowlist_immutable s op c s1 hstep],
             by rw [hd, destination_immutable s op c s1 hstep]⟩

end LiquidationBatcher
