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

open Set

variable {α β : Type*} [TopologicalSpace α] [NormalSpace α] [ParacompactSpace α]
  [NormedAddCommGroup β] [NormedSpace ℝ β]
  {f : α → Set β}

/-- An approximate version of Michael's selection theorem: Any paracompact space which admits
partitions of unity admits continuous _approximate_ selections. In order that these approximate
selections converge, to a true selection, the target space must be a `CompleteSpace` and a
`TopologicalSpace.SeparableSpace`. See `XXX`. -/
lemma foo (G : α → Set β) (hG_convex : ∀ x, Convex ℝ (G x))
    (hG_section : ∀ b : β, IsOpen {x | b ∈ G x}) (hG_nonempty : ∀ x, (G x).Nonempty) :
    ∃ h : α → β, Continuous h ∧ ∀ x, h x ∈ G x := by
  choose F hF using hG_nonempty
  let U : α → Set α := fun x' ↦ {y | F x' ∈ G y}
  have hU_cover : (⋃ x', U x') = univ := by ext x; simpa using ⟨x, hF x⟩
  obtain ⟨φ, hφ⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ U
    (fun x' ↦ hG_section (F x')) hU_cover.symm.subset
  let h : α → β := fun y ↦ ∑ᶠ x', (φ x' y : ℝ) • F x'
  refine ⟨h, φ.continuous_finsum_smul (fun _ _ _ ↦ continuousAt_const), ?_⟩
  · intro y
    apply (hG_convex y).finsum_mem (by simp [φ.nonneg]) (φ.sum_eq_one (mem_univ y))
    intro x' hx'
    exact hφ x' (subset_tsupport _ (Function.mem_support.mpr hx'))

variable [CompleteSpace β] [TopologicalSpace.SeparableSpace β]

open Metric in
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

  have : ∀ x, CauchySeq (fun n ↦ h n x) := fun x ↦
    cauchySeq_of_le_geometric (2 : ℝ)⁻¹ (2 : ℝ)⁻¹ (by norm_num) fun n ↦ by
      rw [dist_comm]
      exact le_of_lt ((h_dist n x).trans_eq (by ring))
  choose H hH using fun x ↦ cauchySeq_tendsto_of_complete (this x)
  use H

  have : TendstoUniformly h H Filter.atTop := by
    rw [tendstoUniformly_iff]
    intro ε hε
    obtain ⟨n, hn⟩ := ((tendsto_pow_atTop_nhds_zero_of_lt_one (r := (2 : ℝ)⁻¹) (by norm_num) (by norm_num)).eventually ((gt_mem_nhds hε))).exists
    filter_upwards [Filter.eventually_ge_atTop n] with m hm
    intro x
    rw [dist_comm]
    have hu : ∀ k, dist (h k x) (h (k + 1) x) ≤ (2 : ℝ)⁻¹ * (2 : ℝ)⁻¹ ^ k := fun k ↦ by
      rw [dist_comm]; exact le_of_lt ((h_dist k x).trans_eq (by ring))
    calc dist (h m x) (H x)
        ≤ (2 : ℝ)⁻¹ * (2 : ℝ)⁻¹ ^ m / (1 - (2 : ℝ)⁻¹) :=
          dist_le_of_le_geometric_of_tendsto (2 : ℝ)⁻¹ (2 : ℝ)⁻¹ (by norm_num) hu (hH x) m
      _ = (2 : ℝ)⁻¹ ^ m := by field_simp; ring
      _ ≤ (2 : ℝ)⁻¹ ^ n := pow_le_pow_of_le_one (by norm_num) (by norm_num) hm
      _ < ε := hn

  constructor
  · apply this.continuous
    apply Filter.Frequently.of_forall
    exact h_cont
  · intro x
    have hinfDist : ∀ n, infDist (h n x) (f x) < (2 : ℝ)⁻¹ ^ n := fun n ↦ by
      rw [← Metric.mem_thickening_iff_infDist_lt (hfe x)]; exact h_mem n x
    have hconv : Filter.Tendsto (fun n ↦ infDist (h n x) (f x))
        Filter.atTop (nhds (infDist (H x) (f x))) :=
      ((continuous_infDist_pt (f x)).tendsto (H x)).comp (hH x)
    have h0 : infDist (H x) (f x) = 0 :=
      tendsto_nhds_unique hconv <| squeeze_zero (fun _ ↦ infDist_nonneg)
        (fun n ↦ (hinfDist n).le)
        (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
    exact (hfc x).mem_iff_infDist_zero (hfe x) |>.mpr h0

end
