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

end Apyx
