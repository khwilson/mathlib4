/-
Copyright (c) 2026 Kevin H. Wilson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin H. Wilson
-/
module

public import Mathlib.Topology.Semicontinuity.Hemicontinuity
public import Mathlib.Topology.Compactness.Paracompact
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.Topology.PartitionOfUnity
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Topology.UniformSpace.UniformApproximation
public import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Michael's selection theorem

This file proves Michael's selection theorem, that a lower hemicontinuous function with
convex closed values admits a continuous selection

TODO: The `NormalSpace` assumption is not necessary but requires some workarounds
-/

public section

variable {α β : Type*} [TopologicalSpace α] [NormalSpace α] [ParacompactSpace α]
  [NormedAddCommGroup β] [NormedSpace ℝ β] [CompleteSpace β] [TopologicalSpace.SeparableSpace β]
  {f : α → Set β}

open Metric Set in
theorem michael (hf : LowerHemicontinuous f) (hfe : ∀ x, (f x).Nonempty) (hfc : ∀ x, IsClosed (f x)) (hfv : ∀ x, Convex ℝ (f x)) :
    ∃ g : α → β, Continuous g ∧ ∀ x, g x ∈ f x := by
  choose F hF using hfe

  let U : ℝ → α → Set α := fun ε x ↦ (f ⁻¹' (Iic (ball (F x) ε)ᶜ))ᶜ
  have hU_open : ∀ ε x, IsOpen (U ε x) := fun ε x ↦
      lowerHemicontinuous_iff_isOpen_compl_preimage_Iic_compl.mp hf _ isOpen_ball

  have hU_rw : ∀ ε x, U ε x = {x' | (f x' ∩ (ball (F x) ε)).Nonempty} := by
    simp [U, Set.ext_iff, Iic, Set.mem_compl_iff, Set.not_subset, Set.Nonempty]

  have hU_mem : ∀ ε x, 0 < ε → x ∈ U ε x := by
    intro ε x hε
    rw [hU_rw]
    use F x
    simp [hF, hε]

  have hU_cover : ∀ ε, 0 < ε → (⋃ x, U ε x) = Set.univ := by
    intro ε hε
    ext x
    constructor
    · simp
    · intro _
      refine mem_iUnion.mpr ?_
      exact ⟨x, hU_mem ε x hε⟩

  have : ∀ ε, 0 < ε → ∃ (f : PartitionOfUnity α α univ), f.IsSubordinate (U ε) := by
    intro ε hε
    exact PartitionOfUnity.exists_isSubordinate isClosed_univ (U ε) (hU_open ε) (by simp [hU_cover ε hε])
  choose φ hφ using this

  have : ∀ ε, (hε : 0 < ε) → ∀ x, Summable (fun x' ↦ (φ ε hε x' x) • (F x)) := by
    intro ε hε x
    apply summable_of_hasFiniteSupport
    have : Function.HasFiniteSupport (fun x' ↦ φ ε hε x' x) := by sorry
    simpa using this.comp (g := fun (c : ℝ) ↦ c • (F x))

  let g : (ε : ℝ) → (0 < ε) → α → β := fun ε hε x ↦ ∑' x', (φ ε hε x' x) • (F x)
  have hg_cont : ∀ ε, (hε : 0 < ε) → Continuous (g ε hε) := sorry
  have hg_infdist : ∀ ε, (hε : 0 < ε) → ∀ x, infDist (g ε hε x) (f x) < ε := sorry

  -- Goal is to do it again, but now we get a sequence of functions h:

  let h : ℕ → α → β := sorry
  have hh_cont : ∀ n, Continuous (h n) := sorry
  have hh_setdist : ∀ n x, ⨆ x' ∈ f x, dist (h n x) x' < ((2 : ℝ)⁻¹) ^ n := sorry
  have hh_precauchy : ∀ n x, ‖h (n + 1) x - h n x‖ < ((2 : ℝ)⁻¹) ^ n  := sorry

  have : ∀ x, CauchySeq (fun n ↦ h n x) := sorry
  choose H hH using fun x ↦ cauchySeq_tendsto_of_complete (this x)
  use H

  have : TendstoUniformly h H Filter.atTop := by
    rw [tendstoUniformly_iff]
    intro ε hε
    obtain ⟨n, hn⟩ := ((tendsto_pow_atTop_nhds_zero_of_lt_one (r := (2 : ℝ)⁻¹) (by norm_num) (by norm_num)).eventually ((gt_mem_nhds hε))).exists
    filter_upwards [Filter.eventually_ge_atTop n] with m hm
    intro x
    sorry

  constructor
  · apply this.continuous
    apply Filter.Frequently.of_forall
    exact hh_cont
  · sorry

end
