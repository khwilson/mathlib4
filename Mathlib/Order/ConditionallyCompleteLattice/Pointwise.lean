/-
Copyright (c) 2026 Kevin H. Wilson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin H. Wilson
-/
module

public import Mathlib.Algebra.GroupWithZero.Action.Pointwise.Set
public import Mathlib.Algebra.Order.Module.Pointwise
public import Mathlib.Order.ConditionallyCompleteLattice.Indexed
public import Mathlib.Algebra.Order.CauSeq.Basic

/-!
# Pointwise operations interaction with `sSup` and `sInf`

This file shows that `sInf (a • s) = a • sInf s` and `sSup (a • s) = a • sSup s` when
`𝕜` is a conditionally complete lattice with `sInf ∅ = 0` and `sSup ∅ = 0` acted on by a group
`α` with `0` and some further conditions. In particular, when `α = 𝕜` is `ℕ`, `ℤ`, `ℚ`, `ℝ`, `ℝ≥0`,
and similar, this holds.

From these, the file relates `⨅ i, a • f i = a • (⨅ i, f i)` and `⨆ i, a • f i = a • (⨆ i, f i)`
and when `α = 𝕜`, the same replacing `•` with `*`.
-/
public section

assert_not_exists Finset

open Set
open scoped Pointwise

variable {ι : Sort*} {α : Type*}
 {𝕜 : Type*} [ConditionallyCompleteLinearOrder 𝕜]

section MulActionWithZero

variable [GroupWithZero α] [PartialOrder α]
  [Zero 𝕜] [MulActionWithZero α 𝕜] [PosSMulMono α 𝕜] [PosSMulReflectLE α 𝕜]
  {a : α}

theorem csInf_smul_of_nonneg [InfSetEmptyZero 𝕜] (ha : 0 ≤ a) (s : Set 𝕜) :
    sInf (a • s) = a • sInf s := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · rw [smul_set_empty, sInf_empty_eq_zero, smul_zero]
  obtain rfl | ha' := ha.eq_or_lt
  · rw [zero_smul_set hs, zero_smul]
    exact csInf_singleton 0
  by_cases h : BddBelow s
  · exact ((OrderIso.smulRight ha').map_csInf' hs h).symm
  · rw [csInf_of_not_bddBelow (mt (bddBelow_smul_iff_of_pos ha').1 h),
        csInf_of_not_bddBelow h, sInf_empty_eq_zero, smul_zero]

theorem smul_ciInf_of_nonneg [InfSetEmptyZero 𝕜] (ha : 0 ≤ a) (f : ι → 𝕜) :
    (a • ⨅ i, f i) = ⨅ i, a • f i :=
  (csInf_smul_of_nonneg ha _).symm.trans <| congr_arg sInf <| (range_comp _ _).symm

theorem csSup_smul_of_nonneg [SupSetEmptyZero 𝕜] (ha : 0 ≤ a) (s : Set 𝕜) :
    sSup (a • s) = a • sSup s := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · rw [smul_set_empty, sSup_empty_eq_zero, smul_zero]
  obtain rfl | ha' := ha.eq_or_lt
  · rw [zero_smul_set hs, zero_smul]
    exact csSup_singleton 0
  by_cases h : BddAbove s
  · exact ((OrderIso.smulRight ha').map_csSup' hs h).symm
  · rw [csSup_of_not_bddAbove (mt (bddAbove_smul_iff_of_pos ha').1 h),
        csSup_of_not_bddAbove h, sSup_empty_eq_zero, smul_zero]

theorem smul_ciSup_of_nonneg [SupSetEmptyZero 𝕜] (ha : 0 ≤ a) (f : ι → 𝕜) :
    (a • ⨆ i, f i) = ⨆ i, a • f i :=
  (csSup_smul_of_nonneg ha _).symm.trans <| congr_arg sSup <| (range_comp _ _).symm

end MulActionWithZero

section Module

variable [Field α] [LinearOrder α] [IsStrictOrderedRing α]
 [AddCommGroup 𝕜] [IsOrderedAddMonoid 𝕜]
 [Module α 𝕜] [IsOrderedModule α 𝕜] [InfSetEmptyZero 𝕜] [SupSetEmptyZero 𝕜]
 {a : α}

theorem csInf_smul_of_nonpos (ha : a ≤ 0) (s : Set 𝕜) : sInf (a • s) = a • sSup s := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · rw [smul_set_empty, sInf_empty_eq_zero, sSup_empty_eq_zero, smul_zero]
  obtain rfl | ha' := ha.eq_or_lt
  · rw [zero_smul_set hs, zero_smul]
    exact csInf_singleton 0
  by_cases h : BddAbove s
  · exact ((OrderIso.smulRightDual 𝕜 ha').map_csSup' hs h).symm
  · rw [csInf_of_not_bddBelow (mt (bddBelow_smul_iff_of_neg ha').1 h),
        csSup_of_not_bddAbove h, sInf_empty_eq_zero, sSup_empty_eq_zero, smul_zero]

theorem smul_ciSup_of_nonpos (ha : a ≤ 0) (f : ι → 𝕜) : (a • ⨆ i, f i) = ⨅ i, a • f i :=
  (csInf_smul_of_nonpos ha _).symm.trans <| congr_arg sInf <| (range_comp _ _).symm

theorem csSup_smul_of_nonpos (ha : a ≤ 0) (s : Set 𝕜) : sSup (a • s) = a • sInf s := by
  obtain rfl | hs := s.eq_empty_or_nonempty
  · rw [smul_set_empty, sSup_empty_eq_zero, sInf_empty_eq_zero, smul_zero]
  obtain rfl | ha' := ha.eq_or_lt
  · rw [zero_smul_set hs, zero_smul]
    exact csSup_singleton 0
  by_cases h : BddBelow s
  · exact ((OrderIso.smulRightDual 𝕜 ha').map_csInf' hs h).symm
  · rw [csSup_of_not_bddAbove (mt (bddAbove_smul_iff_of_neg ha').1 h),
        csInf_of_not_bddBelow h, sInf_empty_eq_zero, sSup_empty_eq_zero, smul_zero]

theorem smul_ciInf_of_nonpos (ha : a ≤ 0) (f : ι → 𝕜) : (a • ⨅ i, f i) = ⨆ i, a • f i :=
  (csSup_smul_of_nonpos ha _).symm.trans <| congr_arg sSup <| (range_comp _ _).symm

end Module

/-! ## Special cases for multiplication -/

section Mul

variable [Field 𝕜] [IsStrictOrderedRing 𝕜] [InfSetEmptyZero 𝕜] [SupSetEmptyZero 𝕜]
variable {r : 𝕜}

omit [SupSetEmptyZero 𝕜] in
theorem mul_ciInf_of_nonneg (ha : 0 ≤ r) (f : ι → 𝕜) : (r * ⨅ i, f i) = ⨅ i, r * f i :=
  smul_ciInf_of_nonneg ha f

omit [InfSetEmptyZero 𝕜] in
theorem mul_ciSup_of_nonneg (ha : 0 ≤ r) (f : ι → 𝕜) : (r * ⨆ i, f i) = ⨆ i, r * f i :=
  smul_ciSup_of_nonneg ha f

theorem mul_ciInf_of_nonpos (ha : r ≤ 0) (f : ι → 𝕜) : (r * ⨅ i, f i) = ⨆ i, r * f i :=
  smul_ciInf_of_nonpos ha f

theorem mul_ciSup_of_nonpos (ha : r ≤ 0) (f : ι → 𝕜) : (r * ⨆ i, f i) = ⨅ i, r * f i :=
  smul_ciSup_of_nonpos ha f

omit [SupSetEmptyZero 𝕜] in
theorem ciInf_mul_of_nonneg (ha : 0 ≤ r) (f : ι → 𝕜) : (⨅ i, f i) * r = ⨅ i, f i * r := by
  simp only [mul_ciInf_of_nonneg ha, mul_comm]

omit [InfSetEmptyZero 𝕜] in
theorem ciSup_mul_of_nonneg (ha : 0 ≤ r) (f : ι → 𝕜) : (⨆ i, f i) * r = ⨆ i, f i * r := by
  simp only [mul_ciSup_of_nonneg ha, mul_comm]

theorem ciInf_mul_of_nonpos (ha : r ≤ 0) (f : ι → 𝕜) : (⨅ i, f i) * r = ⨆ i, f i * r := by
  simp only [mul_ciInf_of_nonpos ha, mul_comm]

theorem ciSup_mul_of_nonpos (ha : r ≤ 0) (f : ι → 𝕜) : (⨆ i, f i) * r = ⨅ i, f i * r := by
  simp only [mul_ciSup_of_nonpos ha, mul_comm]

end Mul
