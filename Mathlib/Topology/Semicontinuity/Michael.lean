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
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Analysis.Normed.Module.Convex

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

lemma foo (G : α → Set β) (hG_convex : ∀ x, Convex ℝ (G x))
    (hG_section : ∀ b : β, IsOpen {x | b ∈ G x}) (hG_nonempty : ∀ x, (G x).Nonempty) :
    ∃ h : α → β, Continuous h ∧ ∀ x, h x ∈ G x := by
  choose F hF using hG_nonempty
  -- Open cover: U x' = {y | F x' ∈ G y}, open by hG_section; self-covers since F x' ∈ G x'
  let U : α → Set α := fun x' ↦ {y | F x' ∈ G y}
  have hU_open : ∀ x', IsOpen (U x') := fun x' ↦ hG_section (F x')
  have hU_mem : ∀ x', x' ∈ U x' := hF
  have hU_cover : (⋃ x', U x') = Set.univ := by
    ext x; simp only [Set.mem_iUnion, Set.mem_univ, iff_true]; exact ⟨x, hU_mem x⟩
  obtain ⟨φ, hφ⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ U hU_open
    hU_cover.symm.subset
  let h : α → β := fun y ↦ ∑' x', (φ x' y : ℝ) • F x'
  refine ⟨h, ?_, ?_⟩
  · -- Continuity of h
    rw [continuous_iff_continuousAt]
    intro y; simp only [h]
    refine ContinuousAt.congr (f := fun y ↦ ∑ᶠ x', (φ x' y : ℝ) • F x') ?_ ?_
    · exact (φ.continuous_finsum_smul (fun i _ _ ↦ continuousAt_const)).continuousAt
    · apply Filter.Eventually.of_forall; intro z; symm
      exact tsum_eq_finsum ((φ.locallyFinite.point_finite z).subset
        (Function.support_smul_subset_left _ _))
  · -- h y ∈ G y: each F x' in the support satisfies F x' ∈ G y (from y ∈ U x')
    intro y
    have heq : h y = ∑ᶠ x', (φ x' y : ℝ) • F x' :=
      tsum_eq_finsum ((φ.locallyFinite.point_finite y).subset
        (Function.support_smul_subset_left _ _))
    rw [heq]
    apply (hG_convex y).finsum_mem
        (fun x' ↦ φ.nonneg x' y)
        (φ.sum_eq_one (Set.mem_univ y))
    intro x' hx'
    exact hφ x' (subset_tsupport _ (Function.mem_support.mpr hx'))

open Metric Set in
theorem michael (hf : LowerHemicontinuous f) (hfe : ∀ x, (f x).Nonempty) (hfc : ∀ x, IsClosed (f x))
    (hfv : ∀ x, Convex ℝ (f x)) :
    ∃ g : α → β, Continuous g ∧ ∀ x, g x ∈ f x := by
  obtain ⟨g, hg_cont, hg_mem⟩ := foo _ (fun x ↦ (hfv x).thickening 1) sorry (by simp [hfe])

  -- State exactly what we want our sequence to satisfy
  obtain ⟨h, h_zero, h_cont, h_mem, h_dist⟩ : ∃ h : ℕ → α → β,
      h 0 = g ∧
      (∀ n, Continuous (h n)) ∧
      (∀ n x, h n x ∈ thickening ((2 : ℝ)⁻¹ ^ n) (f x)) ∧
      (∀ n x, dist (h (n + 1) x) (h n x) < (2 : ℝ)⁻¹ ^ (n + 1)) := by

    -- 1. Define the invariant property for each approximation step
    let P := fun (n : ℕ) (h_curr : α → β) ↦
      Continuous h_curr ∧ ∀ x, h_curr x ∈ thickening ((2 : ℝ)⁻¹ ^ n) (f x)

    -- 2. Prove the inductive step locally
    have step : ∀ (n : ℕ) (hn : α → β), P n hn →
        ∃ h_next, P (n + 1) h_next ∧ ∀ x, dist (h_next x) (hn x) < (2 : ℝ)⁻¹ ^ (n + 1) := by
      intro n hn hn_prop
      obtain ⟨h', hh'_cont, hh'_mem⟩ := foo (fun x ↦ (thickening ((2 : ℝ)⁻¹ ^ (n + 1)) (f x)) ∩ ball (hn x) ((2 : ℝ)⁻¹ ^ (n + 1))) sorry sorry sorry
      use h'
      simp only [hh'_cont, true_and, P]
      constructor
      · intro x
        simpa using (hh'_mem x).1
      · intro x
        simpa using (hh'_mem x).2

    -- 3. Construct the sequence using dependent recursion via Nat.recOn
    -- We bundle the function and its invariant proof into a Subtype.
    let h_seq : (n : ℕ) → {h' // P n h'} := fun n ↦
      Nat.recOn (motive := fun k ↦ {h' // P k h'}) n
        -- Base case (n = 0): Supply g and prove it satisfies P 0
        ⟨g, hg_cont, by simp [hg_mem]⟩
        -- Inductive step (n = k + 1)
        (fun k curr ↦
          -- Extract the witness and proof from our `step` lemma
          let h_next := Classical.choose (step k curr.val curr.prop)
          let h_spec := Classical.choose_spec (step k curr.val curr.prop)
          ⟨h_next, h_spec.1⟩)

    -- 4. Provide the extracted sequence to satisfy the `∃` goal
    refine ⟨fun n ↦ (h_seq n).val, rfl, fun n ↦ (h_seq n).prop.1, fun n ↦ (h_seq n).prop.2, ?_⟩

    -- 5. Prove the distance bound for the sequence
    intro n x
    exact (Classical.choose_spec (step n (h_seq n).val (h_seq n).prop)).2 x

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
    exact h_cont
  · sorry

end
