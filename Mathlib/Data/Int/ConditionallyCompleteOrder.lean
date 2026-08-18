/-
Copyright (c) 2021 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.Data.Int.LeastGreatest
public import Mathlib.Order.ConditionallyCompleteLattice.Defs

/-!
## `ℤ` forms a conditionally complete linear order

The integers form a conditionally complete linear order.
-/

public section

open Int

noncomputable section

namespace Int

set_option backward.isDefEq.respectTransparency false in
open scoped Classical in
instance : ConditionallyCompleteLinearOrder ℤ where
  __ := instLinearOrder
  __ := LinearOrder.toLattice
  sSup s :=
    if h : s.Nonempty ∧ BddAbove s then
      greatestOfBdd (Classical.choose h.2) (Classical.choose_spec h.2) h.1
    else 0
  sInf s :=
    if h : s.Nonempty ∧ BddBelow s then
      leastOfBdd (Classical.choose h.2) (Classical.choose_spec h.2) h.1
    else 0
  isLUB_csSup _ hn hb := by
    rw [dite_eq_left ⟨hn, hb⟩]
    exact (isGreatest_coe_greatestOfBdd ..).isLUB
  isGLB_csInf _ hn hb := by
    rw [dite_eq_left ⟨hn, hb⟩]
    exact (isLeast_coe_leastOfBdd ..).isGLB
  csSup_of_not_bddAbove := fun s hs ↦ by simp [hs]
  csInf_of_not_bddBelow := fun s hs ↦ by simp [hs]

set_option backward.isDefEq.respectTransparency false in
theorem csSup_eq_greatestOfBdd {s : Set ℤ} [DecidablePred (· ∈ s)] (b : ℤ) (Hb : ∀ z ∈ s, z ≤ b)
    (Hinh : ∃ z : ℤ, z ∈ s) : sSup s = greatestOfBdd b Hb Hinh := by
  have : s.Nonempty ∧ BddAbove s := ⟨Hinh, b, Hb⟩
  simp only [sSup, dite_eq_left this]
  convert! (coe_greatestOfBdd_eq Hb (Classical.choose_spec (⟨b, Hb⟩ : BddAbove s)) Hinh).symm

instance instSupSetEmptyZero : SupSetEmptyZero ℤ where
  sSup_empty := dite_eq_right (by simp)

@[deprecated (since := "2026-08-17")] alias csSup_empty := sSup_empty_eq_zero

@[deprecated (since := "2026-08-17")] alias csSup_of_not_bddAbove := csSup_of_not_bddAbove₀

set_option backward.isDefEq.respectTransparency false in
theorem csInf_eq_leastOfBdd {s : Set ℤ} [DecidablePred (· ∈ s)] (b : ℤ) (Hb : ∀ z ∈ s, b ≤ z)
    (Hinh : ∃ z : ℤ, z ∈ s) : sInf s = leastOfBdd b Hb Hinh := by
  have : s.Nonempty ∧ BddBelow s := ⟨Hinh, b, Hb⟩
  simp only [sInf, dite_eq_left this]
  convert! (coe_leastOfBdd_eq Hb (Classical.choose_spec (⟨b, Hb⟩ : BddBelow s)) Hinh).symm

instance instInfSetEmptyZero : InfSetEmptyZero ℤ where
  sInf_empty := dite_eq_right (by simp)

@[deprecated (since := "2026-08-17")] alias csInf_empty := sInf_empty_eq_zero

@[deprecated (since := "2026-08-17")] alias csInf_of_not_bddBelow := csInf_of_not_bddBelow₀

theorem csSup_mem {s : Set ℤ} (h1 : s.Nonempty) (h2 : BddAbove s) : sSup s ∈ s := by
  convert! (greatestOfBdd _ (Classical.choose_spec h2) h1).2.1
  exact dite_eq_left ⟨h1, h2⟩

theorem csInf_mem {s : Set ℤ} (h1 : s.Nonempty) (h2 : BddBelow s) : sInf s ∈ s := by
  convert! (leastOfBdd _ (Classical.choose_spec h2) h1).2.1
  exact dite_eq_left ⟨h1, h2⟩

end Int

end

--  this example tests that the `Lattice ℤ` instance is computable;
-- i.e., that it is not found via the noncomputable instance in this file.
example : Lattice ℤ := inferInstance
