import D2fsSpecs.Apyx

/-!
# Reachable registry invariants

`HolderValue` folds the standard and flexible request registries over
`List.range s.nextUnlockId`.  The existing `RegistryBounded` and
`OwnerPointerSound` predicates describe part of the condition that makes this
fold complete, but they were not previously shown to survive the public
transition function.  This module supplies the missing preservation layer.

The two registries share one allocation counter.  Therefore boundedness alone
does not express that a fresh id is not occupied in the other registry.  The
additional `RegistryDisjoint` predicate makes that model fact explicit.  It is
deliberately narrower than a full `RegistryConsistent`: lifecycle origin,
receipt amount agreement, and user-facing uniqueness are separate claims.
-/

namespace Apyx

/-- A registry id cannot contain both a standard and a flexible request. -/
def RegistryDisjoint (s : State) : Prop :=
  ∀ i, s.unlockRequests i = none ∨ s.flexibleUnlockRequests i = none

/-- The registry facts currently proved for reachable-state reasoning. -/
def RegistryWellIndexed (s : State) : Prop :=
  RegistryBounded s ∧ OwnerPointerSound s ∧ RegistryDisjoint s

/-- Equality of the five state projections read by `RegistryWellIndexed`. -/
def RegistryFrame (s s' : State) : Prop :=
  s'.nextUnlockId = s.nextUnlockId ∧
  s'.unlockRequestId = s.unlockRequestId ∧
  s'.unlockRequests = s.unlockRequests ∧
  s'.flexibleUnlockRequests = s.flexibleUnlockRequests ∧
  s'.unlockTokenOwner = s.unlockTokenOwner

theorem registryWellIndexed_of_frame (s s' : State) (hframe : RegistryFrame s s')
    (h : RegistryWellIndexed s) : RegistryWellIndexed s' := by
  rcases h with ⟨⟨hstd, hflex⟩, hp, hd⟩
  rcases hframe with ⟨hnext, hptr, hstdReq, hflexReq, htoken⟩
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · intro i hi
      have hi' : s.nextUnlockId ≤ i := by simpa [hnext] using hi
      rw [hstdReq]
      exact hstd i hi'
    · intro i hi
      have hi' : s.nextUnlockId ≤ i := by simpa [hnext] using hi
      rw [hflexReq]
      exact hflex i hi'
  · intro a i hi
    have hi' : s.unlockRequestId a = some i := by simpa [hptr] using hi
    obtain ⟨howner, amount, cooldownEnd, hentry⟩ := hp a i hi'
    exact ⟨by simpa [htoken] using howner, amount, cooldownEnd, by
      simpa [hstdReq] using hentry⟩
  · intro i
    rw [hstdReq, hflexReq]
    exact hd i

theorem registryDisjoint_default : RegistryDisjoint (default : State) := by
  intro i
  exact Or.inl rfl

theorem registryDisjoint_createStandardUnlock (s : State) (owner : Address) (amount : Nat)
    (h : RegistryDisjoint s) (hb : RegistryBounded s) :
    RegistryDisjoint (createStandardUnlock s owner amount) := by
  intro i
  by_cases hi : i = s.nextUnlockId
  · right
    subst i
    simpa [createStandardUnlock] using hb.2 s.nextUnlockId (Nat.le_refl _)
  · simpa [createStandardUnlock, hi] using h i

theorem registryDisjoint_createFlexibleUnlock (s : State) (owner : Address) (amount : Nat)
    (h : RegistryDisjoint s) (hb : RegistryBounded s) :
    RegistryDisjoint (createFlexibleUnlock s owner amount) := by
  intro i
  by_cases hi : i = s.nextUnlockId
  · left
    subst i
    simpa [createFlexibleUnlock] using hb.1 s.nextUnlockId (Nat.le_refl _)
  · simpa [createFlexibleUnlock, hi] using h i

theorem registryDisjoint_retireStandardUnlock (s : State) (id : Nat) (owner : Address)
    (h : RegistryDisjoint s) :
    RegistryDisjoint (retireStandardUnlock s id owner) := by
  intro i
  by_cases hi : i = id
  · left
    simp [retireStandardUnlock, burnUnlockNFT, hi]
  · simpa [retireStandardUnlock, burnUnlockNFT, hi] using h i

theorem registryDisjoint_retireFlexibleUnlock (s : State) (id : Nat)
    (h : RegistryDisjoint s) :
    RegistryDisjoint (retireFlexibleUnlock s id) := by
  intro i
  by_cases hi : i = id
  · right
    simp [retireFlexibleUnlock, burnUnlockNFT, hi]
  · simpa [retireFlexibleUnlock, burnUnlockNFT, hi] using h i

theorem registryBounded_createFlexibleUnlock (s : State) (owner : Address) (amount : Nat)
    (h : RegistryBounded s) :
    RegistryBounded (createFlexibleUnlock s owner amount) := by
  obtain ⟨hstd, hflex⟩ := h
  refine ⟨?_, ?_⟩ <;> intro i hi
  · have hge : s.nextUnlockId + 1 ≤ i := by
      simpa [createFlexibleUnlock] using hi
    simpa [createFlexibleUnlock] using hstd i (by omega)
  · have hge : s.nextUnlockId + 1 ≤ i := by
      simpa [createFlexibleUnlock] using hi
    have hne : i ≠ s.nextUnlockId := by omega
    simp [createFlexibleUnlock, hne, hflex i (by omega)]

theorem registryBounded_retireStandardUnlock (s : State) (id : Nat) (owner : Address)
    (h : RegistryBounded s) :
    RegistryBounded (retireStandardUnlock s id owner) := by
  obtain ⟨hstd, hflex⟩ := h
  refine ⟨?_, ?_⟩ <;> intro i hi
  · by_cases hieq : i = id
    · simp [retireStandardUnlock, burnUnlockNFT, hieq]
    · simpa [retireStandardUnlock, burnUnlockNFT, hieq] using hstd i hi
  · by_cases hieq : i = id
    · subst i
      have hi' : s.nextUnlockId ≤ id := by simpa [retireStandardUnlock, burnUnlockNFT] using hi
      exact hflex id hi'
    · simpa [retireStandardUnlock, burnUnlockNFT, hieq] using hflex i hi

theorem registryBounded_retireFlexibleUnlock (s : State) (id : Nat)
    (h : RegistryBounded s) :
    RegistryBounded (retireFlexibleUnlock s id) := by
  obtain ⟨hstd, hflex⟩ := h
  refine ⟨?_, ?_⟩ <;> intro i hi
  · by_cases hieq : i = id
    · subst i
      have hi' : s.nextUnlockId ≤ id := by simpa [retireFlexibleUnlock, burnUnlockNFT] using hi
      exact hstd id hi'
    · simpa [retireFlexibleUnlock, burnUnlockNFT, hieq] using hstd i hi
  · by_cases hieq : i = id
    · simp [retireFlexibleUnlock, burnUnlockNFT, hieq]
    · simpa [retireFlexibleUnlock, burnUnlockNFT, hieq] using hflex i hi

theorem ownerPointerSound_createFlexibleUnlock (s : State) (owner : Address) (amount : Nat)
    (hb : RegistryBounded s) (h : OwnerPointerSound s) :
    OwnerPointerSound (createFlexibleUnlock s owner amount) := by
  intro a i hptr
  have hptr' : s.unlockRequestId a = some i := by simpa [createFlexibleUnlock] using hptr
  obtain ⟨htoken, amt, ce, hreq⟩ := h a i hptr'
  have hne : i ≠ s.nextUnlockId := by
    intro hcontra
    rw [hcontra] at hreq
    rw [std_unallocated_at_counter s hb] at hreq
    exact absurd hreq (by simp)
  exact ⟨by simp [createFlexibleUnlock, hne, htoken], amt, ce, by
    simp [createFlexibleUnlock, hreq]⟩

theorem registryBounded_updateStandardUnlock_of_entry (s : State) (id : Nat) (owner : Address)
    (addAmount : Nat) (h : RegistryBounded s) (hid : id < s.nextUnlockId)
    (hreq : ∃ o oa oe, s.unlockRequests id = some (o, oa, oe)) :
    RegistryBounded (updateStandardUnlock s id owner addAmount) := by
  obtain ⟨hstd, hflex⟩ := h
  obtain ⟨o, oa, oe, hentry⟩ := hreq
  have hnext : (updateStandardUnlock s id owner addAmount).nextUnlockId = s.nextUnlockId := by
    simp [updateStandardUnlock, hentry]
  refine ⟨?_, ?_⟩ <;> intro i hi
  · have hi' : s.nextUnlockId ≤ i := by simpa [hnext] using hi
    have hne : i ≠ id := by omega
    rw [updateStandardUnlock_unlockRequests_eq s id owner addAmount o oa oe hentry i]
    simp [hne, hstd i hi']
  · have hi' : s.nextUnlockId ≤ i := by simpa [hnext] using hi
    simpa [updateStandardUnlock, hentry] using hflex i hi'

theorem registryDisjoint_updateStandardUnlock_of_entry (s : State) (id : Nat) (owner : Address)
    (addAmount : Nat) (h : RegistryDisjoint s)
    (hreq : ∃ o oa oe, s.unlockRequests id = some (o, oa, oe)) :
    RegistryDisjoint (updateStandardUnlock s id owner addAmount) := by
  obtain ⟨o, oa, oe, hentry⟩ := hreq
  intro i
  by_cases hieq : i = id
  · right
    have hnone : s.flexibleUnlockRequests id = none := by
      rcases h id with hstd | hflex
      · simp [hentry] at hstd
      · exact hflex
    simpa [updateStandardUnlock, hentry, hieq] using hnone
  · simpa [updateStandardUnlock, hentry, hieq] using h i

theorem ownerPointerSound_updateStandardUnlock_of_entry (s : State) (id : Nat)
    (owner : Address) (addAmount oldAmount oldEnd : Nat) (h : OwnerPointerSound s)
    (hentry : s.unlockRequests id = some (owner, oldAmount, oldEnd))
    (htoken : s.unlockTokenOwner id = some owner) :
    OwnerPointerSound (updateStandardUnlock s id owner addAmount) := by
  unfold updateStandardUnlock
  rw [hentry]
  intro a i hptr
  by_cases ha : a = owner
  · subst a
    by_cases hieq : i = id
    · subst i
      exact ⟨htoken, oldAmount + addAmount, s.now + cooldownPeriod, by simp⟩
    · have hptr' : s.unlockRequestId owner = some i := by simpa [hieq] using hptr
      obtain ⟨htoken', amount, ce, hentry'⟩ := h owner i hptr'
      exact ⟨by simpa [hieq] using htoken', amount, ce, by
        simpa [hieq] using hentry'⟩
  · have hptr' : s.unlockRequestId a = some i := by simpa [ha] using hptr
    obtain ⟨htoken', amount, ce, hentry'⟩ := h a i hptr'
    have hne : i ≠ id := by
      intro hieq
      subst i
      rw [hentry'] at hentry
      simp at hentry
      exact ha hentry.1
    exact ⟨by simpa [hne] using htoken', amount, ce, by
      simpa [hne] using hentry'⟩

theorem registryWellIndexed_createStandardUnlock (s : State) (owner : Address) (amount : Nat)
    (h : RegistryWellIndexed s) :
    RegistryWellIndexed (createStandardUnlock s owner amount) := by
  obtain ⟨hb, hp, hd⟩ := h
  exact ⟨registryBounded_createStandardUnlock s owner amount hb,
    ownerPointerSound_createStandardUnlock s owner amount hb hp,
    registryDisjoint_createStandardUnlock s owner amount hd hb⟩

theorem registryWellIndexed_createFlexibleUnlock (s : State) (owner : Address) (amount : Nat)
    (h : RegistryWellIndexed s) :
    RegistryWellIndexed (createFlexibleUnlock s owner amount) := by
  obtain ⟨hb, hp, hd⟩ := h
  exact ⟨registryBounded_createFlexibleUnlock s owner amount hb,
    ownerPointerSound_createFlexibleUnlock s owner amount hb hp,
    registryDisjoint_createFlexibleUnlock s owner amount hd hb⟩

theorem registryWellIndexed_burnApxUSD (s : State) (caller amount : Nat)
    (h : RegistryWellIndexed s) :
    RegistryWellIndexed (burnApxUSD s caller amount) := by
  simpa [burnApxUSD, RegistryWellIndexed, RegistryBounded, OwnerPointerSound,
    RegistryDisjoint] using h

theorem registryWellIndexed_pullVestedYield (s : State) (h : RegistryWellIndexed s) :
    RegistryWellIndexed (pullVestedYield s) := by
  unfold pullVestedYield
  dsimp only
  split <;> exact h

theorem registryWellIndexed_mintApxUSD (s : State) (to amount : Nat)
    (h : RegistryWellIndexed s) :
    RegistryWellIndexed (mintApxUSD s to amount) := by
  simpa [mintApxUSD, RegistryWellIndexed, RegistryBounded, OwnerPointerSound,
    RegistryDisjoint] using h

theorem registryWellIndexed_requestUnlockStep (s : State) (caller amount : Nat)
    (h : RegistryWellIndexed s) :
    RegistryWellIndexed (requestUnlockStep s caller amount) := by
  let b := burnApxUSD s caller amount
  have hb : RegistryWellIndexed b := by
    simpa [b] using registryWellIndexed_burnApxUSD s caller amount h
  change RegistryWellIndexed (match b.unlockRequestId caller with
    | some id =>
      match b.unlockRequests id with
      | some (o, _, _) =>
        if o = caller then updateStandardUnlock b id caller amount
        else createStandardUnlock b caller amount
      | none => createStandardUnlock b caller amount
    | none => createStandardUnlock b caller amount)
  generalize hptr : b.unlockRequestId caller = ptr
  cases ptr with
  | none => simpa using registryWellIndexed_createStandardUnlock b caller amount hb
  | some id =>
    generalize hentry : b.unlockRequests id = entry
    cases entry with
    | none => simpa [hentry] using registryWellIndexed_createStandardUnlock b caller amount hb
    | some triple =>
      rcases triple with ⟨o, oldAmount, oldEnd⟩
      by_cases ho : o = caller
      · subst o
        have hentry' : b.unlockRequests id = some (caller, oldAmount, oldEnd) := hentry
        have hid : id < b.nextUnlockId := by
          by_cases hlt : id < b.nextUnlockId
          · exact hlt
          · have hnone := hb.1.1 id (by omega)
            rw [hnone] at hentry'
            simp at hentry'
        have htoken : b.unlockTokenOwner id = some caller :=
          (hb.2.1 caller id hptr).1
        simpa [hentry] using (show RegistryWellIndexed (updateStandardUnlock b id caller amount) from ⟨
          registryBounded_updateStandardUnlock_of_entry b id caller amount hb.1 hid
            ⟨caller, oldAmount, oldEnd, hentry'⟩,
          ownerPointerSound_updateStandardUnlock_of_entry b id caller amount oldAmount oldEnd
            hb.2.1 hentry' htoken,
          registryDisjoint_updateStandardUnlock_of_entry b id caller amount hb.2.2
            ⟨caller, oldAmount, oldEnd, hentry'⟩⟩)
      · simpa [hentry, ho] using registryWellIndexed_createStandardUnlock b caller amount hb

private theorem requestUnlock_post (s : State) (amount : Nat) (caller : Address) (s' : State)
    (h : step s (Op.requestUnlock amount) caller = some s') :
    s.globalPause = false ∧ amount ≤ s.apxUSDBal caller ∧
    s' = requestUnlockStep s caller amount := by
  simp only [step] at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · split at h
      · exact absurd h (by simp)
      · exact ⟨by simp_all, by omega, (Option.some.inj h).symm⟩

theorem registryWellIndexed_requestUnlock_step (s : State) (amount : Nat) (caller : Address)
    (s' : State) (h : RegistryWellIndexed s)
    (hstep : step s (Op.requestUnlock amount) caller = some s') :
    RegistryWellIndexed s' := by
  obtain ⟨-, -, hpost⟩ := requestUnlock_post s amount caller s' hstep
  rw [hpost]
  exact registryWellIndexed_requestUnlockStep s caller amount h

theorem ownerPointerSound_retireStandardUnlock (s : State) (id : Nat) (owner : Address)
    (hreq : ∃ amount ce, s.unlockRequests id = some (owner, amount, ce))
    (h : OwnerPointerSound s) :
    OwnerPointerSound (retireStandardUnlock s id owner) := by
  intro a i hptr
  by_cases ha : a = owner
  · subst a
    simp only [retireStandardUnlock, burnUnlockNFT] at hptr
    split at hptr
    · exact False.elim (by simp at hptr)
    · rename_i hkeep
      have hptr' : s.unlockRequestId owner = some i := by simpa using hptr
      obtain ⟨htoken, amount, ce, hentry⟩ := h owner i hptr'
      have hne : i ≠ id := by
        intro hieq
        subst i
        apply hkeep
        simp [hptr']
      exact ⟨by simpa [retireStandardUnlock, burnUnlockNFT, hne] using htoken,
        amount, ce, by simpa [retireStandardUnlock, burnUnlockNFT, hne] using hentry⟩
  · have hptr' : s.unlockRequestId a = some i := by
      simpa [retireStandardUnlock, burnUnlockNFT, ha] using hptr
    obtain ⟨htoken, amount, ce, hentry⟩ := h a i hptr'
    have hne : i ≠ id := by
      intro hieq
      subst hieq
      obtain ⟨amount', ce', hreq'⟩ := hreq
      rw [hentry] at hreq'
      simp at hreq'
      exact ha hreq'.1
    exact ⟨by simpa [retireStandardUnlock, burnUnlockNFT, hne] using htoken,
      amount, ce, by simpa [retireStandardUnlock, burnUnlockNFT, hne] using hentry⟩

theorem ownerPointerSound_retireFlexibleUnlock (s : State) (id : Nat)
    (hflex : ∃ owner amount requestTime cooldownEnd,
      s.flexibleUnlockRequests id = some (owner, amount, requestTime, cooldownEnd))
    (hd : RegistryDisjoint s) (h : OwnerPointerSound s) :
    OwnerPointerSound (retireFlexibleUnlock s id) := by
  intro a i hptr
  have hptr' : s.unlockRequestId a = some i := by
    simpa [retireFlexibleUnlock, burnUnlockNFT] using hptr
  obtain ⟨htoken, amount, ce, hentry⟩ := h a i hptr'
  have hne : i ≠ id := by
    intro hieq
    subst i
    obtain ⟨owner, amount', requestTime, cooldownEnd, hflex'⟩ := hflex
    have hflex_not_none : ¬ s.flexibleUnlockRequests id = none := by
      intro hnone
      rw [hnone] at hflex'
      simp at hflex'
    have hstdNone := (hd id).resolve_right hflex_not_none
    rw [hentry] at hstdNone
    simp at hstdNone
  exact ⟨by simpa [retireFlexibleUnlock, burnUnlockNFT, hne] using htoken,
    amount, ce, by simpa [retireFlexibleUnlock, burnUnlockNFT, hne] using hentry⟩

theorem registryWellIndexed_retireStandardUnlock (s : State) (id : Nat) (owner : Address)
    (h : RegistryWellIndexed s)
    (hentry : ∃ amount ce, s.unlockRequests id = some (owner, amount, ce)) :
    RegistryWellIndexed (retireStandardUnlock s id owner) := by
  obtain ⟨hb, hp, hd⟩ := h
  exact ⟨registryBounded_retireStandardUnlock s id owner hb,
    ownerPointerSound_retireStandardUnlock s id owner hentry hp,
    registryDisjoint_retireStandardUnlock s id owner hd⟩

theorem registryWellIndexed_retireFlexibleUnlock (s : State) (id : Nat)
    (h : RegistryWellIndexed s)
    (hentry : ∃ owner amount requestTime cooldownEnd,
      s.flexibleUnlockRequests id = some (owner, amount, requestTime, cooldownEnd)) :
    RegistryWellIndexed (retireFlexibleUnlock s id) := by
  obtain ⟨hb, hp, hd⟩ := h
  exact ⟨registryBounded_retireFlexibleUnlock s id hb,
    ownerPointerSound_retireFlexibleUnlock s id hentry hd hp,
    registryDisjoint_retireFlexibleUnlock s id hd⟩

private theorem claimUnlock_post (s : State) (id : Nat) (caller : Address) (s' : State)
    (h : step s (Op.claimUnlock id) caller = some s') :
    ∃ owner amount cooldownEnd,
      s.unlockRequests id = some (owner, amount, cooldownEnd) ∧
      s.unlockTokenOwner id = some owner ∧
      (caller = owner ∨ caller = s.unlockTokenOperator) ∧
      cooldownEnd ≤ s.now ∧
      s' = mintApxUSD (retireStandardUnlock s id owner) owner amount := by
  simp only [step] at h
  split at h
  · exact absurd h (by simp)
  · rename_i owner amount cooldownEnd heq
    split at h
    · exact absurd h (by simp)
    · split at h
      · exact absurd h (by simp)
      · split at h
        · split at h
          · exact absurd h (by simp)
          · exact ⟨owner, amount, cooldownEnd, heq, by simp_all, by assumption, by omega,
              (Option.some.inj h).symm⟩
        · exact absurd h (by simp)

private theorem flexibleClaimUnlock_post (s : State) (id : Nat) (caller : Address) (s' : State)
    (h : step s (Op.flexibleClaimUnlock id) caller = some s') :
    ∃ owner amount requestTime cooldownEnd,
      s.flexibleUnlockRequests id = some (owner, amount, requestTime, cooldownEnd) ∧
      s.unlockTokenOwner id = some owner ∧
      (caller = owner ∨ caller = s.unlockTokenOperator) ∧
      requestTime + minFlexibleClaim ≤ s.now ∧
      s' = mintApxUSD (retireFlexibleUnlock s id) owner
        (amount - amount * flexibleUnlockFee requestTime s.now / 10000) := by
  simp only [step] at h
  split at h
  · exact absurd h (by simp)
  · rename_i owner amount requestTime cooldownEnd heq
    split at h
    · exact absurd h (by simp)
    · split at h
      · exact absurd h (by simp)
      · split at h
        · split at h
          · exact absurd h (by simp)
          · exact ⟨owner, amount, requestTime, cooldownEnd, heq, by simp_all, by assumption,
              by omega, (Option.some.inj h).symm⟩
        · exact absurd h (by simp)

theorem registryWellIndexed_claimUnlock_step (s : State) (id : Nat) (caller : Address)
    (s' : State) (h : RegistryWellIndexed s)
    (hstep : step s (Op.claimUnlock id) caller = some s') :
    RegistryWellIndexed s' := by
  obtain ⟨owner, amount, cooldownEnd, hreq, -, -, -, hpost⟩ := claimUnlock_post s id caller s' hstep
  rw [hpost]
  exact registryWellIndexed_mintApxUSD _ _ _
    (registryWellIndexed_retireStandardUnlock s id owner h ⟨amount, cooldownEnd, hreq⟩)

theorem registryWellIndexed_flexibleClaimUnlock_step (s : State) (id : Nat) (caller : Address)
    (s' : State) (h : RegistryWellIndexed s)
    (hstep : step s (Op.flexibleClaimUnlock id) caller = some s') :
    RegistryWellIndexed s' := by
  obtain ⟨owner, amount, requestTime, cooldownEnd, hreq, -, -, -, hpost⟩ :=
    flexibleClaimUnlock_post s id caller s' hstep
  rw [hpost]
  exact registryWellIndexed_mintApxUSD _ _ _
    (registryWellIndexed_retireFlexibleUnlock s id h
      ⟨owner, amount, requestTime, cooldownEnd, hreq⟩)

private theorem flexibleRequestUnlock_post (s : State) (amount : Nat) (caller : Address) (s' : State)
    (h : step s (Op.flexibleRequestUnlock amount) caller = some s') :
    s.globalPause = false ∧ amount ≤ s.apxUSDBal caller ∧
    s' = createFlexibleUnlock (burnApxUSD s caller amount) caller amount := by
  simp only [step] at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · split at h
      · exact absurd h (by simp)
      · exact ⟨by simp_all, by omega, (Option.some.inj h).symm⟩

theorem registryWellIndexed_flexibleRequestUnlock_step (s : State) (amount : Nat)
    (caller : Address) (s' : State) (h : RegistryWellIndexed s)
    (hstep : step s (Op.flexibleRequestUnlock amount) caller = some s') :
    RegistryWellIndexed s' := by
  obtain ⟨-, -, hpost⟩ := flexibleRequestUnlock_post s amount caller s' hstep
  rw [hpost]
  exact registryWellIndexed_createFlexibleUnlock _ _ _
    (registryWellIndexed_burnApxUSD s caller amount h)

/-- Registry preservation along the shared tail of the two ERC-4626 vault exits
(`Op.withdraw` / `Op.redeem`): burn the caller's apyUSD, debit the vault, allocate a fresh
standard unlock position for the receiver, republish the exchange rate, emit the event.
The apyUSD burn and vault debit are pure registry frames; the allocation is the existing
`createStandardUnlock` preservation; the rate republish and event emission are discharged
per projection (`simp`) rather than by one whole-structure `rfl`, which sends the kernel
into deep recursion on this 40-field state. -/
theorem registryWellIndexed_vaultExitChain (s1 : State) (caller shares assets : Nat)
    (receiver : Address) (name : String) (evArgs : List Nat)
    (h : RegistryWellIndexed s1) :
    RegistryWellIndexed (emitEvent (updateExchangeRate (createStandardUnlock
      { burnApyUSD s1 caller shares with
          vaultApxUSDBal := (burnApyUSD s1 caller shares).vaultApxUSDBal - assets }
      receiver assets)) name evArgs) := by
  have h2 : RegistryWellIndexed
      ({ burnApyUSD s1 caller shares with
          vaultApxUSDBal := (burnApyUSD s1 caller shares).vaultApxUSDBal - assets } : State) :=
    registryWellIndexed_of_frame s1 _ ⟨rfl, rfl, rfl, rfl, rfl⟩ h
  have h3 : RegistryWellIndexed (createStandardUnlock
      { burnApyUSD s1 caller shares with
          vaultApxUSDBal := (burnApyUSD s1 caller shares).vaultApxUSDBal - assets }
      receiver assets) :=
    registryWellIndexed_createStandardUnlock _ receiver assets h2
  exact registryWellIndexed_of_frame _ _
    ⟨by simp [emitEvent, updateExchangeRate], by simp [emitEvent, updateExchangeRate],
     by simp [emitEvent, updateExchangeRate], by simp [emitEvent, updateExchangeRate],
     by simp [emitEvent, updateExchangeRate]⟩ h3

/-- A successful `Op.withdraw` preserves the registry invariants.

**Model caveat (documented, not repaired here).** The exit allocates its receipt with
`createStandardUnlock`, which *unconditionally overwrites* `unlockRequestId receiver`.
If the receiver already had a live standard unlock position (from an earlier
`requestUnlock`), that position's per-user pointer is lost: the old entry stays in
`unlockRequests`/`unlockTokenOwner` and remains claimable by id through `claimUnlock`,
but it can no longer be topped up (the `requestUnlockStep` coalescing path follows the
pointer) and `requestUnlockStep_caller_position`'s "single tracked position" reading no
longer covers it. `RegistryWellIndexed` survives because `OwnerPointerSound` constrains
only ids a pointer *currently* references — the orphaned entry is simply out of the
pointer's view. The theorem is stated over the model as-is. -/
theorem registryWellIndexed_withdraw_step (s : State) (assets : Nat) (receiver caller : Address)
    (s' : State) (h : RegistryWellIndexed s)
    (hstep : step s (Op.withdraw assets receiver) caller = some s') :
    RegistryWellIndexed s' := by
  have h1 : RegistryWellIndexed (pullVestedYield s) := registryWellIndexed_pullVestedYield s h
  simp only [step] at hstep
  (repeat' split at hstep) <;>
    first
      | cases Option.some.inj hstep
        exact registryWellIndexed_vaultExitChain (pullVestedYield s) caller _ assets
          receiver _ _ h1
      | exact absurd hstep (by simp)

/-- A successful `Op.redeem` preserves the registry invariants. Same exit tail and same
pointer-overwrite caveat as `registryWellIndexed_withdraw_step`. -/
theorem registryWellIndexed_redeem_step (s : State) (shares : Nat) (receiver caller : Address)
    (s' : State) (h : RegistryWellIndexed s)
    (hstep : step s (Op.redeem shares receiver) caller = some s') :
    RegistryWellIndexed s' := by
  have h1 : RegistryWellIndexed (pullVestedYield s) := registryWellIndexed_pullVestedYield s h
  simp only [step] at hstep
  (repeat' split at hstep) <;>
    first
      | cases Option.some.inj hstep
        exact registryWellIndexed_vaultExitChain (pullVestedYield s) caller shares _
          receiver _ _ h1
      | exact absurd hstep (by simp)

/-- Operations outside the six registry-writing branches leave all registry projections alone.
The two vault exit branches are intentionally excluded: they allocate a new standard position. -/
def RegistryStaticOp (op : Op) : Prop :=
  (∀ n, op ≠ Op.requestUnlock n) ∧
  (∀ n, op ≠ Op.claimUnlock n) ∧
  (∀ n r, op ≠ Op.withdraw n r) ∧
  (∀ n r, op ≠ Op.redeem n r) ∧
  (∀ n, op ≠ Op.flexibleRequestUnlock n) ∧
  (∀ n, op ≠ Op.flexibleClaimUnlock n)

theorem registryWellIndexed_static_step (s : State) (op : Op) (caller : Address) (s' : State)
    (h : RegistryWellIndexed s) (hop : RegistryStaticOp op)
    (hstep : step s op caller = some s') :
    RegistryWellIndexed s' := by
  cases op
  case requestUnlock n => exact False.elim (hop.1 n rfl)
  case claimUnlock n => exact False.elim (hop.2.1 n rfl)
  case withdraw n r => exact False.elim (hop.2.2.1 n r rfl)
  case redeem n r => exact False.elim (hop.2.2.2.1 n r rfl)
  case flexibleRequestUnlock n => exact False.elim (hop.2.2.2.2.1 n rfl)
  case flexibleClaimUnlock n => exact False.elim (hop.2.2.2.2.2 n rfl)
  all_goals
    simp only [step] at hstep
    (repeat' split at hstep) <;>
      first
        | cases Option.some.inj hstep
          exact registryWellIndexed_of_frame _ _ ⟨rfl, rfl, rfl, rfl, rfl⟩ h
        | exact absurd hstep (by simp)

/-- Capstone: **every** successful public transition preserves the registry invariants.
The six registry-writing operations are dispatched to their dedicated preservation
theorems; every other constructor is a registry frame via
`registryWellIndexed_static_step`. -/
theorem registryWellIndexed_step (s : State) (op : Op) (caller : Address) (s' : State)
    (h : RegistryWellIndexed s) (hstep : step s op caller = some s') :
    RegistryWellIndexed s' := by
  cases op
  case requestUnlock n =>
    exact registryWellIndexed_requestUnlock_step s n caller s' h hstep
  case claimUnlock n =>
    exact registryWellIndexed_claimUnlock_step s n caller s' h hstep
  case withdraw n r =>
    exact registryWellIndexed_withdraw_step s n r caller s' h hstep
  case redeem n r =>
    exact registryWellIndexed_redeem_step s n r caller s' h hstep
  case flexibleRequestUnlock n =>
    exact registryWellIndexed_flexibleRequestUnlock_step s n caller s' h hstep
  case flexibleClaimUnlock n =>
    exact registryWellIndexed_flexibleClaimUnlock_step s n caller s' h hstep
  all_goals
    exact registryWellIndexed_static_step s _ caller s' h
      (by simp [RegistryStaticOp]) hstep

end Apyx
