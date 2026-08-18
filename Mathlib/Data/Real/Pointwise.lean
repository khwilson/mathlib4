/-
Copyright (c) 2021 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Eric Wieser
-/
module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Pointwise

/-!
# Pointwise operations on sets of reals

This file relates `sInf (a • s)`/`sSup (a • s)` with `a • sInf s`/`a • sSup s` for `s : Set ℝ`.

From these, it relates `⨅ i, a • f i` / `⨆ i, a • f i` with `a • (⨅ i, f i)` / `a • (⨆ i, f i)`,
and provides lemmas about distributing `*` over `⨅` and `⨆`.

N.B. This entire file is _deprecated_ in favor of using
`Mathlib.Order.ConditionallyCompleteLattice.Pointwise` which generalizes these
results.
-/

public section

assert_not_exists Finset

open Set

open scoped Pointwise

variable {ι : Sort*} {α : Type*} [Field α] [LinearOrder α] [IsStrictOrderedRing α]

section MulActionWithZero

variable [MulActionWithZero α ℝ] [IsOrderedModule α ℝ] {a : α}

@[deprecated (since := "2026-08-17")]
alias Real.sInf_smul_of_nonneg := csInf_smul_of_nonneg

@[deprecated (since := "2026-08-17")]
alias Real.smul_iInf_of_nonneg := smul_ciInf_of_nonneg

@[deprecated (since := "2026-08-17")]
alias Real.sSup_smul_of_nonneg := csSup_smul_of_nonneg

@[deprecated (since := "2026-08-17")]
alias Real.smul_iSup_of_nonneg := smul_ciSup_of_nonneg

end MulActionWithZero

section Module

variable [Module α ℝ] [IsOrderedModule α ℝ] {a : α}

@[deprecated (since := "2026-08-17")]
alias Real.sInf_smul_of_nonpos := csInf_smul_of_nonpos

@[deprecated (since := "2026-08-17")]
alias Real.smul_iSup_of_nonpos := smul_ciSup_of_nonpos

@[deprecated (since := "2026-08-17")]
alias Real.sSup_smul_of_nonpos := csSup_smul_of_nonpos

@[deprecated (since := "2026-08-17")]
alias Real.smul_iInf_of_nonpos := smul_ciInf_of_nonpos

end Module

/-! ## Special cases for real multiplication -/

section Mul

variable {r : ℝ}

@[deprecated (since := "2026-08-17")]
alias Real.mul_iInf_of_nonneg := mul_ciInf_of_nonneg

@[deprecated (since := "2026-08-17")]
alias Real.mul_iSup_of_nonneg := mul_ciSup_of_nonneg

@[deprecated (since := "2026-08-17")]
alias Real.mul_iInf_of_nonpos := mul_ciInf_of_nonpos

@[deprecated (since := "2026-08-17")]
alias Real.mul_iSup_of_nonpos := mul_ciSup_of_nonpos

@[deprecated (since := "2026-08-17")]
alias Real.iInf_mul_of_nonneg := ciInf_mul_of_nonneg

@[deprecated (since := "2026-08-17")]
alias Real.iSup_mul_of_nonneg := ciSup_mul_of_nonneg

@[deprecated (since := "2026-08-17")]
alias Real.iInf_mul_of_nonpos := ciInf_mul_of_nonpos

@[deprecated (since := "2026-08-17")]
alias Real.iSup_mul_of_nonpos := ciSup_mul_of_nonpos

end Mul
