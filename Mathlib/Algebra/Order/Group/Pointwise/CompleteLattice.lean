/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Algebra.Order.Group.Pointwise.Bounds
public import Mathlib.Order.ConditionallyCompleteLattice.Indexed
public import Mathlib.Order.ConditionallyCompleteLattice.Pointwise
public import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-!
# Infima/suprema in ordered monoids and groups

In this file we prove a few facts like “The infimum of `-s` is `-` the supremum of `s`”.

## TODO

`sSup (s • t) = sSup s • sSup t` and `sInf (s • t) = sInf s • sInf t` hold as well but
`CovariantClass` is currently not polymorphic enough to state it.
-/

public section

open Set
open scoped Pointwise

variable {ι : Sort*} {M : Type*}

section ConditionallyCompleteLattice
variable [ConditionallyCompleteLattice M]

section One
variable [One M]

@[to_additive (attr := simp)] lemma csSup_one : sSup (1 : Set M) = 1 := csSup_singleton _
@[to_additive (attr := simp)] lemma csInf_one : sInf (1 : Set M) = 1 := csInf_singleton _

end One

section Group
variable [Group M] [MulLeftMono M] [MulRightMono M]
  {s t : Set M}

@[to_additive]
lemma csSup_inv (hs₀ : s.Nonempty) (hs₁ : BddBelow s) : sSup s⁻¹ = (sInf s)⁻¹ := by
  rw [← image_inv_eq_inv]
  exact ((OrderIso.inv _).map_csInf' hs₀ hs₁).symm

@[to_additive]
lemma csInf_inv (hs₀ : s.Nonempty) (hs₁ : BddAbove s) : sInf s⁻¹ = (sSup s)⁻¹ := by
  rw [← image_inv_eq_inv]
  exact ((OrderIso.inv _).map_csSup' hs₀ hs₁).symm

@[to_additive]
lemma csSup_mul (hs₀ : s.Nonempty) (hs₁ : BddAbove s) (ht₀ : t.Nonempty) (ht₁ : BddAbove t) :
    sSup (s * t) = sSup s * sSup t :=
  csSup_image2_eq_csSup_csSup (fun _ => (OrderIso.mulRight _).to_galoisConnection)
    (fun _ => (OrderIso.mulLeft _).to_galoisConnection) hs₀ hs₁ ht₀ ht₁

@[to_additive]
lemma csInf_mul (hs₀ : s.Nonempty) (hs₁ : BddBelow s) (ht₀ : t.Nonempty) (ht₁ : BddBelow t) :
    sInf (s * t) = sInf s * sInf t :=
  csInf_image2_eq_csInf_csInf (fun _ => (OrderIso.mulRight _).symm.to_galoisConnection)
    (fun _ => (OrderIso.mulLeft _).symm.to_galoisConnection) hs₀ hs₁ ht₀ ht₁

@[to_additive]
lemma csSup_div (hs₀ : s.Nonempty) (hs₁ : BddAbove s) (ht₀ : t.Nonempty) (ht₁ : BddBelow t) :
    sSup (s / t) = sSup s / sInf t := by
  rw [div_eq_mul_inv, csSup_mul hs₀ hs₁ ht₀.inv ht₁.inv, csSup_inv ht₀ ht₁, div_eq_mul_inv]

@[to_additive]
lemma csInf_div (hs₀ : s.Nonempty) (hs₁ : BddBelow s) (ht₀ : t.Nonempty) (ht₁ : BddAbove t) :
    sInf (s / t) = sInf s / sSup t := by
  rw [div_eq_mul_inv, csInf_mul hs₀ hs₁ ht₀.inv ht₁.inv, csInf_inv ht₀ ht₁, div_eq_mul_inv]

end Group
end ConditionallyCompleteLattice

section ConditionallyCompleteLinearOrder
variable [ConditionallyCompleteLinearOrder M]

section AddGroup
variable [AddGroup M]

section AddLeftMono
variable [AddLeftMono M] {s : Set M} {a ε : M}

theorem lt_sInf_add_pos (h : s.Nonempty) (hε : 0 < ε) : ∃ a ∈ s, a < sInf s + ε :=
  exists_lt_of_csInf_lt h <| lt_add_of_pos_right _ hε

theorem add_neg_lt_sSup (h : s.Nonempty) (hε : ε < 0) : ∃ a ∈ s, sSup s + ε < a :=
  exists_lt_of_lt_csSup h <| add_lt_iff_neg_left.2 hε

theorem csInf_le_iff_forall_pos_lt_add (h : BddBelow s) (h' : s.Nonempty) :
    sInf s ≤ a ↔ ∀ ε, 0 < ε → ∃ x ∈ s, x < a + ε := by
  rw [le_iff_forall_pos_lt_add]
  constructor <;> intro H ε ε_pos
  · exact exists_lt_of_csInf_lt h' (H ε ε_pos)
  · rcases H ε ε_pos with ⟨x, x_in, hx⟩
    exact csInf_lt_of_lt h x_in hx

variable [AddRightMono M]

theorem le_csSup_iff_forall_neg_add_lt (h : BddAbove s) (h' : s.Nonempty) :
    a ≤ sSup s ↔ ∀ ε, ε < 0 → ∃ x ∈ s, a + ε < x := by
  rw [le_iff_forall_pos_lt_add]
  refine ⟨fun H ε ε_neg => ?_, fun H ε ε_pos => ?_⟩
  · refine exists_lt_of_lt_csSup h' (lt_sub_iff_add_lt.mp ?_)
    simpa [sub_eq_add_neg] using H _ (neg_pos.mpr ε_neg)
  · rcases H _ (neg_lt_zero.mpr ε_pos) with ⟨x, x_in, hx⟩
    refine sub_lt_iff_lt_add.mp (lt_csSup_of_lt h x_in ?_)
    simpa [sub_eq_add_neg] using hx

variable [InfSetEmptyZero M] [SupSetEmptyZero M] (s : Set M)

@[simp]
lemma sSup_neg₀ : sSup (-s) = -sInf s := by
  obtain rfl | hn := s.eq_empty_or_nonempty; · simp
  by_cases hb : BddBelow s
  · rw [csSup_neg hn hb]
  · rw [csInf_of_not_bddBelow hb, sInf_empty_eq_zero,
      csSup_of_not_bddAbove (bddAbove_neg.not.2 hb), sSup_empty_eq_zero, neg_zero]

@[simp]
lemma sInf_neg₀ : sInf (-s) = -sSup s := by
  rw [← neg_eq_iff_eq_neg, ← sSup_neg₀, neg_neg]

end AddLeftMono

end AddGroup
end ConditionallyCompleteLinearOrder

section CompleteLattice
variable [CompleteLattice M]

section One
variable [One M]

@[to_additive] lemma sSup_one : sSup (1 : Set M) = 1 := sSup_singleton
@[to_additive] lemma sInf_one : sInf (1 : Set M) = 1 := sInf_singleton

end One

section Group
variable [Group M] [MulLeftMono M] [MulRightMono M]
  (s t : Set M)

@[to_additive]
lemma sSup_inv (s : Set M) : sSup s⁻¹ = (sInf s)⁻¹ := by
  rw [← image_inv_eq_inv, sSup_image]
  exact ((OrderIso.inv M).map_sInf _).symm

@[to_additive]
lemma sInf_inv (s : Set M) : sInf s⁻¹ = (sSup s)⁻¹ := by
  rw [← image_inv_eq_inv, sInf_image]
  exact ((OrderIso.inv M).map_sSup _).symm

@[to_additive]
lemma sSup_mul : sSup (s * t) = sSup s * sSup t :=
  (sSup_image2_eq_sSup_sSup fun _ => (OrderIso.mulRight _).to_galoisConnection) fun _ =>
    (OrderIso.mulLeft _).to_galoisConnection

@[to_additive]
lemma sInf_mul : sInf (s * t) = sInf s * sInf t :=
  (sInf_image2_eq_sInf_sInf fun _ => (OrderIso.mulRight _).symm.to_galoisConnection) fun _ =>
    (OrderIso.mulLeft _).symm.to_galoisConnection

@[to_additive]
lemma sSup_div : sSup (s / t) = sSup s / sInf t := by simp_rw [div_eq_mul_inv, sSup_mul, sSup_inv]

@[to_additive]
lemma sInf_div : sInf (s / t) = sInf s / sSup t := by simp_rw [div_eq_mul_inv, sInf_mul, sInf_inv]

end Group
end CompleteLattice
