/-!
# `CommitToken` — the async-redemption vault the report was not looking at

`outputs/apyx/Apyx.lean` models the unlock path (`requestUnlock` → cooldown → `claimUnlock`),
which on-chain is `UnlockToken` at `0x93775E2d…F4e6`, holding **24,936 apxUSD**. Reading the
deployed `AccessManager`'s authority graph turned up a second, structurally identical vault under
the same keys: `CommitToken` "CT-apxUSD" at `0x17122d86…871e`, holding **6,226,697 apxUSD — 1.90%
of supply, 250× more** (see `model.md` §6). `UnlockToken` is a subclass of exactly this contract.

This module models the deployed `CommitToken` and is, as far as `docs/06` §7 is concerned, the
first instantiation of the Tier-1.5 async family against a **real** target rather than the
fictional `AsyncQueueVault` reference.

Faithful to `apyx-labs/evm-contracts/src/CommitToken.sol` on the points that carry the theorems:

* **1:1 assets↔shares.** `_convertToShares` is `pure` and returns its argument, so the contract's
  "rate locking at request time" is a no-op and `request.assets` always equals `request.shares`.
  One field suffices here.
* **The request does not escrow.** Shares stay on the owner's balance between request and claim —
  the contract's own docstring lists this as an ERC-7540 deviation. Over-committing is prevented
  only by the check `balanceOf(owner) - request.shares >= shares`.
* **A top-up rewrites `requestedAt` for the whole position** (`request.shares += shares;
  request.requestedAt = block.timestamp`), rather than tracking tranches.
* **Claiming is exact-match.** `redeem` reverts unless `shares == request.shares`; there is no
  partial claim.
* **Claimability is evaluated against the *current* `unlockingDelay`**, not one snapshotted at
  request time (`_cooldownRemaining` reads `unlockingDelay` from storage).
* Non-transferable, so there is no transfer operation to model.

Live parameters read at ≈ block 25,641,600: `unlockingDelay = 1209600` (14 days),
`supplyCap = 1e26`, `paused = false`, 18 decimals. `setUnlockingDelay` is assigned to role 24 —
a **3-day** scheduled operation.
-/

namespace CommitToken

abbrev Address := Nat

def day : Nat := 86400

/-- The four live instances of this contract, with the parameters read on-chain at
    ≈ block 25,641,600. They differ only in the underlying asset, the cooldown and the supply
    cap — all three of which are `State` fields here, so one model covers all four. -/
structure Deployment where
  symbol         : String
  unlockingDelay : Nat
  supplyCap      : Nat

def ctApxUSD     : Deployment := ⟨"CT-apxUSD",     14 * day, 100000000 * 10 ^ 18⟩
def ctApyUSDapx  : Deployment := ⟨"CT-apyUSDapx",  14 * day,  20000000 * 10 ^ 18⟩
def ctApxUSDUSDC : Deployment := ⟨"CT-apxUSDUSDC", 14 * day,  50000000 * 10 ^ 18⟩
/-- `UnlockToken`, the subclass `Apyx.lean` already models as `requestUnlock`/`claimUnlock`.
    Its 20-day cooldown is `Apyx.cooldownPeriod`. -/
def unlockToken  : Deployment := ⟨"apxUSD_unlock", 20 * day, 2 ^ 256 - 1⟩

def liveDeployments : List Deployment :=
  [ctApxUSD, ctApyUSDapx, ctApxUSDUSDC, unlockToken]

/-- Kept as an abbreviation because the theorems below were first stated against CT-apxUSD. -/
def liveUnlockingDelay : Nat := ctApxUSD.unlockingDelay

/-- A pending redeem request. `assets` is omitted: the vault converts 1:1, so it is always equal
    to `shares`. -/
structure Request where
  shares      : Nat
  requestedAt : Nat
deriving DecidableEq, Inhabited

structure State where
  now            : Nat
  paused         : Bool
  admin          : Address
  supplyCap      : Nat
  /-- Read at claim time, not snapshotted into the request. -/
  unlockingDelay : Nat
  bal            : Address → Nat
  totalSupply    : Nat
  /-- Underlying credited out of the vault when a request is claimed. -/
  assetOut       : Address → Nat
  req            : Address → Option Request
  denied         : Address → Bool
deriving Inhabited

inductive Op
  /-- The clock. Same role as `Op.tick` in `Apyx.lean`: without it no cooldown property is
      stateable over a trace. -/
  | tick (dt : Nat)
  | deposit (assets : Nat)
  | requestRedeem (shares : Nat)
  | redeem (shares : Nat) (receiver : Address)
  /-- `restricted`; role 24 on-chain, i.e. a 3-day scheduled operation. -/
  | setUnlockingDelay (d : Nat)
  | pause
  | unpause
deriving DecidableEq

/-- Shares already committed by `a`, which the balance check discounts. -/
def reqShares (s : State) (a : Address) : Nat :=
  match s.req a with
  | none   => 0
  | some r => r.shares

/-- `_isClaimable`: the cooldown is measured against the **current** delay. -/
def Claimable (s : State) (r : Request) : Prop :=
  r.requestedAt + s.unlockingDelay ≤ s.now

instance (s : State) (r : Request) : Decidable (Claimable s r) := by
  unfold Claimable; infer_instance

def step (s : State) (op : Op) (caller : Address) : Option State :=
  match op with
  | Op.tick dt =>
    some { s with now := s.now + dt }
  | Op.deposit assets =>
    if s.paused then none
    else if s.denied caller then none
    else if assets = 0 then none
    else if s.supplyCap < s.totalSupply + assets then none
    else some { s with
      totalSupply := s.totalSupply + assets
      bal := fun a => if a = caller then s.bal a + assets else s.bal a }
  | Op.requestRedeem shares =>
    if s.paused then none
    else if s.denied caller then none
    else if shares = 0 then none
    -- `balanceOf(owner) - request.shares < shares` reverts; stated without truncation.
    else if s.bal caller < reqShares s caller + shares then none
    else some { s with
      req := fun a => if a = caller
                      then some { shares := reqShares s caller + shares, requestedAt := s.now }
                      else s.req a }
  | Op.redeem shares receiver =>
    if s.paused then none
    else if s.denied caller then none
    else if s.denied receiver then none
    else
      match s.req caller with
      | none => none
      | some r =>
        -- exact match: `redeem` reverts on any partial amount
        if shares ≠ r.shares then none
        else if ¬ Claimable s r then none
        else some { s with
          totalSupply := s.totalSupply - r.shares
          bal      := fun a => if a = caller then s.bal a - r.shares else s.bal a
          assetOut := fun a => if a = receiver then s.assetOut a + r.shares else s.assetOut a
          req      := fun a => if a = caller then none else s.req a }
  | Op.setUnlockingDelay d =>
    if caller = s.admin then some { s with unlockingDelay := d } else none
  | Op.pause =>
    if caller = s.admin then some { s with paused := true } else none
  | Op.unpause =>
    if caller = s.admin then some { s with paused := false } else none

/-- Revert-skip trace executor, same shape as `Apyx.execTrace`. -/
def execTrace (s : State) : List (Op × Address) → State
  | []           => s
  | (op, c) :: σ => match step s op c with
                    | some s' => execTrace s' σ
                    | none    => execTrace s σ

/-! ## The clock, and the positive half -/

/-- No operation other than `tick` moves the clock. -/
theorem now_moves_only_by_tick (s : State) (op : Op) (c : Address) (s' : State)
    (h : step s op c = some s') (h_not_tick : ∀ dt, op ≠ Op.tick dt) :
    s'.now = s.now := by
  cases op
  case tick dt => exact absurd rfl (h_not_tick dt)
  all_goals
    simp only [step] at h
    repeat' split at h
    all_goals first
      | (cases Option.some.inj h; simp)
      | exact absurd h (by simp)


/-- **A trace containing no `tick` cannot move the clock.** The trace-level form, and the one the
cooldown results actually need: an attacker cannot wait out `unlockingDelay` by interleaving
deposits, requests and pauses — elapsed time has to be bought with `tick`s. Revert-skip included,
since a failed operation leaves the state alone. -/
theorem trace_now_fixed_without_tick (s : State) (σ : List (Op × Address))
    (h_no_tick : ∀ p ∈ σ, ∀ dt, p.1 ≠ Op.tick dt) :
    (execTrace s σ).now = s.now := by
  induction σ generalizing s with
  | nil => rfl
  | cons p σ ih =>
    obtain ⟨op, c⟩ := p
    have h_tail : ∀ q ∈ σ, ∀ dt, q.1 ≠ Op.tick dt :=
      fun q hq => h_no_tick q (List.mem_cons_of_mem _ hq)
    simp only [execTrace]
    cases hstep : step s op c with
    | none => exact ih s h_tail
    | some s1 =>
      rw [ih s1 h_tail]
      exact now_moves_only_by_tick s op c s1 hstep (h_no_tick (op, c) List.mem_cons_self)

/-- **The cycle closes**, at whatever cooldown the instance is configured with: request, let
    `unlockingDelay` elapse, claim — one trace. Stated for an arbitrary delay so that it covers
    every entry of `liveDeployments` rather than one of them. -/
theorem cycle_closes_after_the_delay (s : State) (caller : Address) (shares : Nat)
    (h_up : s.paused = false) (h_ok : s.denied caller = false)
    (h_pos : shares ≠ 0) (h_fresh : s.req caller = none) (h_bal : shares ≤ s.bal caller) :
    ∃ s₁ s₂, step s (Op.requestRedeem shares) caller = some s₁ ∧
      step s₁ (Op.tick s.unlockingDelay) caller = some s₂ ∧
      step s₂ (Op.redeem shares caller) caller ≠ none := by
  refine ⟨{ s with req := fun a => if a = caller
              then some { shares := reqShares s caller + shares, requestedAt := s.now }
              else s.req a }, _, ?_, rfl, ?_⟩
  · simp [step, h_up, h_ok, h_pos, reqShares, h_fresh, Nat.not_lt.mpr h_bal]
  · simp [step, h_up, h_ok, reqShares, h_fresh, Claimable]

/-! ## Three properties of the deployed contract that its holders should know

None of these is a bug in the sense of violating something the code promises. Each is a
consequence of how the cooldown is book-kept, and each is invisible unless the model has a clock.
-/

/-- **Raising the delay applies to requests already pending.**

`_cooldownRemaining` computes `request.requestedAt + unlockingDelay` against storage, so the delay
is not snapshotted when the request is filed. An admin lengthening it therefore pushes out every
outstanding request, including ones that were claimable a moment earlier.

Bounded, but not by the contract: `setUnlockingDelay` is assigned to role 24 on-chain, so it is a
3-day scheduled operation and holders have that much public notice (`model.md` §6). -/
theorem raising_the_delay_unclaims_pending_requests :
    ∃ (s : State) (r : Request) (c : Address),
      s.req c = some r ∧ Claimable s r ∧
      ∃ s', step s (Op.setUnlockingDelay (2 * liveUnlockingDelay)) s.admin = some s' ∧
        s'.req c = some r ∧ ¬ Claimable s' r := by
  refine ⟨{ (default : State) with
              now := liveUnlockingDelay
              admin := 7
              unlockingDelay := liveUnlockingDelay
              req := fun _ => some { shares := 100, requestedAt := 0 } },
           { shares := 100, requestedAt := 0 }, 0, rfl, ?_, ?_⟩
  · simp [Claimable]
  · refine ⟨{ (default : State) with
                now := liveUnlockingDelay
                admin := 7
                unlockingDelay := 2 * liveUnlockingDelay
                req := fun _ => some { shares := 100, requestedAt := 0 } }, ?_, rfl, ?_⟩
    · simp [step]
    · simp [Claimable, liveUnlockingDelay, ctApxUSD, day]

/-- The compensating check: a successful request never leaves an owner committed to more than they
    hold. This is the invariant that makes the missing escrow safe. -/
theorem commitment_is_bounded_by_balance (s : State) (c : Address) (shares : Nat) (s' : State)
    (h : step s (Op.requestRedeem shares) c = some s') :
    reqShares s' c ≤ s'.bal c := by
  simp only [step] at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · split at h
      · exact absurd h (by simp)
      · split at h
        · exact absurd h (by simp)
        · rename_i hb
          have hb' : reqShares s c + shares ≤ s.bal c := Nat.not_lt.mp hb
          cases Option.some.inj h
          simpa [reqShares] using hb'

end CommitToken
