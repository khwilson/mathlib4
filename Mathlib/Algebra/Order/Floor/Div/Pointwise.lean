/-
Copyright (c) 2026 Kevin H. Wilson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin H. Wilson
-/
module

public import Mathlib.Algebra.Order.Floor.Div
public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import Mathlib.Order.ConditionallyCompleteLattice.Pointwise
public import Mathlib.Order.Lattice.Nat

/-!
# Flooring/ceiling division interacts with `sSup` and `sInf`

`FloorDiv α β` asserts that `b ↦ a • b` has a right adjoint for `0 < a`, and `CeilDiv α β` that it
has a left adjoint. Adjoints preserve the suprema and infima that exist, so under the
`sSup ∅ = 0` and `sInf ∅ = 0` conventions this gives `sSup (a • s) = a • sSup s` and
`sInf (a • s) = a • sInf s` with no invertibility assumption on `a`.

This is what covers `ℕ` and `ℤ`, where the adjoint is flooring resp. ceiling division rather than
multiplication by `a⁻¹`. For invertible scalars, where the adjoint *is* `a⁻¹ • ·`, see
`Mathlib/Order/ConditionallyCompleteLattice/Pointwise.lean`; both routes are corollaries of
`GaloisConnection.l_csSup₀` and `GaloisConnection.u_csInf₀`.
-/

public section

open Set
open scoped Pointwise

variable {ι : Sort*} {α β : Type*} [AddCommMonoid α] [PartialOrder α] [AddCommMonoid β]
  [ConditionallyCompleteLinearOrder β] [SMulZeroClass α β] {a : α}

section FloorDiv

variable [SupSetEmptyZero β] [FloorDiv α β]

theorem csSup_smul_of_pos (ha : 0 < a) (s : Set β) : sSup (a • s) = a • sSup s := by
  rw [← image_smul, GaloisConnection.l_csSup₀ (gc_floorDiv_smul ha) (smul_zero a) s]

theorem smul_ciSup_of_pos (ha : 0 < a) (f : ι → β) : (a • ⨆ i, f i) = ⨆ i, a • f i :=
  (csSup_smul_of_pos ha _).symm.trans <| congr_arg sSup <| (range_comp _ _).symm

end FloorDiv

section CeilDiv

variable [InfSetEmptyZero β] [CeilDiv α β]

theorem csInf_smul_of_pos (ha : 0 < a) (s : Set β) : sInf (a • s) = a • sInf s := by
  rw [← image_smul, GaloisConnection.u_csInf₀ (gc_smul_ceilDiv ha) (smul_zero a) s]

theorem smul_ciInf_of_pos (ha : 0 < a) (f : ι → β) : (a • ⨅ i, f i) = ⨅ i, a • f i :=
  (csInf_smul_of_pos ha _).symm.trans <| congr_arg sInf <| (range_comp _ _).symm

end CeilDiv

/-! ## The cases `ℕ` and `ℤ`, which no invertibility argument reaches -/

namespace Nat

theorem mul_ciSup_of_pos {a : ℕ} (ha : 0 < a) (f : ι → ℕ) : (a * ⨆ i, f i) = ⨆ i, a * f i :=
  smul_ciSup_of_pos ha f

theorem mul_ciInf_of_pos {a : ℕ} (ha : 0 < a) (f : ι → ℕ) : (a * ⨅ i, f i) = ⨅ i, a * f i :=
  smul_ciInf_of_pos ha f

end Nat

namespace Int

theorem mul_ciSup_of_pos {a : ℤ} (ha : 0 < a) (f : ι → ℤ) : (a * ⨆ i, f i) = ⨆ i, a * f i :=
  smul_ciSup_of_pos ha f

theorem mul_ciInf_of_pos {a : ℤ} (ha : 0 < a) (f : ι → ℤ) : (a * ⨅ i, f i) = ⨅ i, a * f i :=
  smul_ciInf_of_pos ha f

end Int
