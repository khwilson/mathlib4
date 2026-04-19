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
public import Mathlib.Topology.Semicontinuity.Metric

/-!
# Michael's selection theorem

This file proves Michael's selection theorem, that a lower hemicontinuous function with
convex closed nonempty values admits a continuous selection.

## Main results

- `HasOpenLowerSections.approx_of_convex_nonempty`: A correspondence with open lower sections and
  convex, nonempty values admits a continuous selection. A key ingredient to the proof of Michael's
  selction theorem
- `LowerHemicontinuous.approx_of_convex_closed_nonempty`: Michael's selection theorem that a
  lower hemicontinous function from a paracompact space to a separable Banach space which takes
  convex, closed, nonempty values admits a continuous selection
-/

public section

open Set Metric

variable {α β : Type*} {f : α → Set β} {g : α → β}

variable [TopologicalSpace α] [NormalSpace α] [ParacompactSpace α]
  [NormedAddCommGroup β] [NormedSpace ℝ β]
  {f : α → Set β}

/-- A correspondence with open lower sections and convex, nonempty values admits a
continuous selection -/
lemma HasOpenLowerSections.exists_continuous_selection (hf : HasOpenLowerSections f)
    (hf_nonempty : ∀ x, (f x).Nonempty) (hf_convex : ∀ x, Convex ℝ (f x)) :
    ∃ h : α → β, Continuous h ∧ ∀ x, h x ∈ f x := by
  choose F hF using hf_nonempty
  obtain ⟨φ, hφ⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ
    _ (fun x' ↦ hf.isOpen (F x')) (fun x _ ↦ Set.mem_iUnion.mpr ⟨x, hF x⟩)
  exact ⟨fun y ↦ ∑ᶠ x', (φ x' y) • F x',
    φ.continuous_finsum_smul (fun _ _ _ ↦ continuousAt_const), fun y ↦
    (hf_convex y).finsum_mem (fun i ↦ φ.nonneg i y) (φ.sum_eq_one (mem_univ y)) fun x' hx' ↦
      hφ x' (subset_tsupport _ hx')⟩

variable [CompleteSpace β]

theorem LowerHemicontinuous.exists_continuous_selection (hf : LowerHemicontinuous f)
    (hf_nonempty : ∀ x, (f x).Nonempty) (hf_convex : ∀ x, Convex ℝ (f x))
    (hf_isClosed : ∀ x, IsClosed (f x)) : ∃ g : α → β, Continuous g ∧ ∀ x, g x ∈ f x := by
  obtain ⟨g, hg_cont, hg_mem⟩ := (hf.thickening_hasOpenLowerSections 1).exists_continuous_selection
    (by simp [hf_nonempty]) (fun x ↦ (hf_convex x).thickening 1)
  obtain ⟨h, hh_cont, hh_mem, hh_mem_ball⟩ : ∃ h : ℕ → α → β, (∀ n, Continuous (h n)) ∧
      (∀ n x, h n x ∈ Metric.thickening ((2 : ℝ)⁻¹ ^ n) (f x)) ∧
      (∀ n x, h (n + 1) x ∈ ball (h n x) ((2 : ℝ) ⁻¹ ^ (n + 1))) := by
    let P (n : ℕ) (h : α → β) :=
      Continuous h ∧ ∀ x, h x ∈ Metric.thickening ((2 : ℝ)⁻¹ ^ n) (f x)
    have step : ∀ n hn, P n hn →
        ∃ h', P (n + 1) h' ∧ ∀ x, (h' x) ∈ ball (hn x) ((2 : ℝ)⁻¹ ^ (n + 1)) := by
      intro n hn hn_prop
      let ε := (2 : ℝ)⁻¹ ^ (n + 1)
      have hε : 0 < ε := by positivity
      have : HasOpenLowerSections (fun x ↦ Metric.thickening ε (f x) ∩ ball (hn x) ε) :=
        hasOpenLowerSections_iff_isOpen.mpr fun b ↦ by
          simpa [dist_comm b] using ((hf.thickening_hasOpenLowerSections _).isOpen _).inter <|
            hn_prop.1.isOpen_preimage _ isOpen_ball
      obtain ⟨h', hh'_cont, hh'_mem⟩ := this.exists_continuous_selection
        (fun x ↦ by
          obtain ⟨z, hz_mem, hz_dist⟩ := mem_thickening_iff.mp (hn_prop.2 x)
          have key : (2 : ℝ)⁻¹ * dist (hn x) z < ε :=
            calc _ < (2 : ℝ)⁻¹ * (2 : ℝ)⁻¹ ^ n := mul_lt_mul_of_pos_left hz_dist (by norm_num)
                _ = ε := by ring
          refine ⟨(2 : ℝ)⁻¹ • (hn x + z), mem_thickening_iff.mpr ⟨z, hz_mem, ?_⟩, mem_ball.mpr ?_⟩
          · rwa [dist_eq_norm, show (2 : ℝ)⁻¹ • (hn x + z) - z = (2 : ℝ)⁻¹ • (hn x - z) by module,
              norm_smul, Real.norm_of_nonneg (by norm_num), ← dist_eq_norm]
          · rwa [dist_eq_norm,
              show (2 : ℝ)⁻¹ • (hn x + z) - hn x = (2 : ℝ)⁻¹ • (z - hn x) by module,
              norm_smul, Real.norm_of_nonneg (by norm_num), ← dist_eq_norm, dist_comm])
        (fun x ↦ (hf_convex x).thickening _ |>.inter <| convex_ball ..)
      exact ⟨h', ⟨hh'_cont, fun x ↦ (hh'_mem x).1⟩, fun x ↦ by simpa [ε] using (hh'_mem x).2⟩
    let seq : (n : ℕ) → {h' // P n h'} := fun n ↦
      Nat.recOn n ⟨g, hg_cont, by simp [hg_mem]⟩ fun n curr ↦
        let S := step n curr.val curr.prop; ⟨S.choose, S.choose_spec.1⟩
    exact ⟨fun n ↦ (seq n).val, fun n ↦ (seq n).prop.1, fun n x ↦ (seq n).prop.2 x,
      fun n ↦ (step n (seq n).val (seq n).prop).choose_spec.2⟩
  have hCauchy : ∀ x, CauchySeq (fun n ↦ h n x) := fun x ↦
    cauchySeq_of_le_geometric (2 : ℝ)⁻¹ (2 : ℝ)⁻¹ (by norm_num) fun n ↦ by
      rw [dist_comm]; exact (hh_mem_ball n x).le.trans_eq (by ring)
  choose H hH using fun x ↦ cauchySeq_tendsto_of_complete (hCauchy x)
  have unif : TendstoUniformly h H Filter.atTop := by
    rw [tendstoUniformly_iff]
    intro ε hε
    obtain ⟨n, hn⟩ := ((tendsto_pow_atTop_nhds_zero_of_lt_one (r := (2 : ℝ)⁻¹) (by norm_num)
      (by norm_num)).eventually (gt_mem_nhds hε)).exists
    filter_upwards [Filter.eventually_ge_atTop n] with m hm x
    rw [dist_comm]
    have hu : ∀ k, dist (h k x) (h (k + 1) x) ≤ (2 : ℝ)⁻¹ * (2 : ℝ)⁻¹ ^ k := fun k ↦ by
      rw [dist_comm]; exact (hh_mem_ball k x).le.trans_eq (by ring)
    calc dist (h m x) (H x)
        ≤ (2 : ℝ)⁻¹ * (2 : ℝ)⁻¹ ^ m / (1 - (2 : ℝ)⁻¹) :=
          dist_le_of_le_geometric_of_tendsto (2 : ℝ)⁻¹ (2 : ℝ)⁻¹ (by norm_num) hu (hH x) m
      _ = (2 : ℝ)⁻¹ ^ m := by field_simp; ring
      _ ≤ (2 : ℝ)⁻¹ ^ n := pow_le_pow_of_le_one (by norm_num) (by norm_num) hm
      _ < ε := hn
  refine ⟨H, unif.continuous (Filter.Frequently.of_forall fun n ↦ hh_cont n), fun x ↦ ?_⟩
  have hinfDist : ∀ n, infDist (h n x) (f x) < (2 : ℝ)⁻¹ ^ n := fun n ↦ by
    simpa [← Metric.mem_thickening_iff_infDist_lt (hf_nonempty x)] using hh_mem n x
  have hconv : Filter.Tendsto (fun n ↦ infDist (h n x) (f x)) Filter.atTop
      (nhds (infDist (H x) (f x))) :=
    ((continuous_infDist_pt (f x)).tendsto (H x)).comp (hH x)
  have h0 : infDist (H x) (f x) = 0 :=
    tendsto_nhds_unique hconv <| squeeze_zero (fun _ ↦ infDist_nonneg)
      (fun n ↦ (hinfDist n).le)
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num))
  exact (hf_isClosed x).mem_iff_infDist_zero (hf_nonempty x) |>.mpr h0

end
