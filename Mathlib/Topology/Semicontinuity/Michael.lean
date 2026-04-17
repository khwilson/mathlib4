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

open Metric in
lemma foo (hf : LowerHemicontinuous f) (hfe : ∀ x, (f x).Nonempty) (hfv : ∀ x, Convex ℝ (f x))
    (g : α → β) (hg_cont : Continuous g) (ε : ℝ)
    (hg_setdist : ∀ x, infDist (g x) (f x) < ε) :
    ∃ h : α → β, Continuous h ∧ (∀ x, infDist (h x) (f x) < ε / 2)
      ∧ (∀ x, dist (h x) (g x) < ε / 2) := by
  -- Choose F(x) ∈ f(x) with dist(g(x), F(x)) < ε
  have hF_exists : ∀ x, ∃ y ∈ f x, dist (g x) y < ε :=
    fun x => (Metric.infDist_lt_iff (hfe x)).mp (hg_setdist x)
  choose F hF_mem hF_dist using hF_exists
  -- V x' is the midpoint of g x' and F x'; both lie within ε/2 of V x'
  let V : α → β := fun x' ↦ (2 : ℝ)⁻¹ • (g x' + F x')
  have hV_gdist : ∀ x', dist (g x') (V x') < ε / 2 := fun x' => by
    have heq : dist (g x') (V x') = dist (g x') (F x') / 2 := by
      rw [dist_eq_norm, dist_eq_norm]
      have : g x' - V x' = (2 : ℝ)⁻¹ • (g x' - F x') := by simp only [V]; module
      rw [this, norm_smul, show ‖(2 : ℝ)⁻¹‖ = (2 : ℝ)⁻¹ from
          Real.norm_of_nonneg (by positivity)]
      ring
    linarith [hF_dist x']
  have hV_Fdist : ∀ x', dist (F x') (V x') < ε / 2 := fun x' => by
    have heq : dist (F x') (V x') = dist (g x') (F x') / 2 := by
      rw [dist_eq_norm, dist_eq_norm]
      have : F x' - V x' = (2 : ℝ)⁻¹ • (F x' - g x') := by simp only [V]; module
      rw [this, norm_smul, show ‖(2 : ℝ)⁻¹‖ = (2 : ℝ)⁻¹ from
          Real.norm_of_nonneg (by positivity), norm_sub_rev (F x') (g x')]
      ring
    linarith [hF_dist x']
  -- Open cover: LHC ball of radius ε/2 and g-preimage ball of radius ε/2, both at V x'
  let U : α → Set α := fun x' ↦
    (f ⁻¹' (Set.Iic (ball (V x') (ε / 2))ᶜ))ᶜ ∩ g ⁻¹' (ball (V x') (ε / 2))
  have hU_open : ∀ x', IsOpen (U x') := fun x' ↦
    (lowerHemicontinuous_iff_isOpen_compl_preimage_Iic_compl.mp hf _
      isOpen_ball).inter (isOpen_ball.preimage hg_cont)
  have hU_rw : ∀ x' y, y ∈ U x' ↔
      (f y ∩ ball (V x') (ε / 2)).Nonempty ∧ g y ∈ ball (V x') (ε / 2) := by
    intro x' y
    simp only [U, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_preimage, Set.mem_Iic,
               Set.Nonempty, Set.mem_inter_iff]
    refine and_congr ?_ Iff.rfl
    constructor
    · intro h
      obtain ⟨z, hz1, hz2⟩ := Set.not_subset.mp h
      simp only [Set.mem_compl_iff, not_not] at hz2
      exact ⟨z, hz1, hz2⟩
    · rintro ⟨z, hz1, hz2⟩
      apply Set.not_subset.mpr
      exact ⟨z, hz1, by simp only [Set.mem_compl_iff, not_not]; exact hz2⟩
  -- x' ∈ U x': F x' witnesses the LHC condition; g x' satisfies the g condition
  have hU_mem : ∀ x', x' ∈ U x' := fun x' => by
    rw [hU_rw]
    exact ⟨⟨F x', hF_mem x', mem_ball.mpr (hV_Fdist x')⟩, mem_ball.mpr (hV_gdist x')⟩
  have hU_cover : (⋃ x', U x') = Set.univ := by
    ext x; simp only [Set.mem_iUnion, Set.mem_univ, iff_true]; exact ⟨x, hU_mem x⟩
  obtain ⟨φ, hφ⟩ := PartitionOfUnity.exists_isSubordinate isClosed_univ U hU_open
    hU_cover.symm.subset
  let h : α → β := fun y ↦ ∑' x', (φ x' y : ℝ) • V x'
  refine ⟨h, ?_, ?_, ?_⟩
  · -- Continuity of h
    rw [continuous_iff_continuousAt]
    intro y; simp only [h]
    refine ContinuousAt.congr (f := fun y ↦ ∑ᶠ x', (φ x' y : ℝ) • V x') ?_ ?_
    · exact (φ.continuous_finsum_smul (fun i _ _ ↦ continuousAt_const)).continuousAt
    · apply Filter.Eventually.of_forall; intro z; symm
      exact tsum_eq_finsum ((φ.locallyFinite.point_finite z).subset
        (Function.support_smul_subset_left _ _))
  · -- infDist bound: each V x' ∈ thickening(f y, ε/2) since f y ∩ ball(V x', ε/2) ≠ ∅
    intro y
    have heq : h y = ∑ᶠ x', (φ x' y : ℝ) • V x' :=
      tsum_eq_finsum ((φ.locallyFinite.point_finite y).subset
        (Function.support_smul_subset_left _ _))
    rw [heq, ← Metric.mem_thickening_iff_infDist_lt (hfe y)]
    apply ((hfv y).thickening (ε / 2)).finsum_mem
        (fun x' ↦ φ.nonneg x' y)
        (φ.sum_eq_one (Set.mem_univ y))
    intro x' hx'
    rw [Metric.mem_thickening_iff]
    have hy_in : y ∈ U x' :=
      hφ x' (subset_tsupport _ (Function.mem_support.mpr hx'))
    rw [hU_rw] at hy_in
    obtain ⟨⟨z, hz_f, hz_ball⟩, -⟩ := hy_in
    exact ⟨z, hz_f, mem_ball'.mp hz_ball⟩
  · -- dist bound: each V x' ∈ ball(g y, ε/2) since g y ∈ ball(V x', ε/2)
    intro y
    have heq : h y = ∑ᶠ x', (φ x' y : ℝ) • V x' :=
      tsum_eq_finsum ((φ.locallyFinite.point_finite y).subset
        (Function.support_smul_subset_left _ _))
    rw [heq, ← mem_ball]
    apply (convex_ball (g y) (ε / 2)).finsum_mem
        (fun x' ↦ φ.nonneg x' y)
        (φ.sum_eq_one (Set.mem_univ y))
    intro x' hx'
    have hy_in : y ∈ U x' :=
      hφ x' (subset_tsupport _ (Function.mem_support.mpr hx'))
    rw [hU_rw] at hy_in
    obtain ⟨-, hy_ball⟩ := hy_in
    rw [mem_ball, dist_comm]
    exact mem_ball.mp hy_ball

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

  have : ∀ ε, (hε : 0 < ε) → ∀ x, Summable (fun x' ↦ (φ ε hε x' x) • (F x')) := by
    intro ε hε x
    apply summable_of_hasFiniteSupport
    exact ((φ ε hε).locallyFinite.point_finite x).subset (Function.support_smul_subset_left _ _)

  let g : (ε : ℝ) → (0 < ε) → α → β := fun ε hε x ↦ ∑' x', (φ ε hε x' x) • (F x')
  have hg_cont : ∀ ε, (hε : 0 < ε) → Continuous (g ε hε) := by
    intro ε hε
    rw [continuous_iff_continuousAt]
    intro x
    simp only [g]
    refine ContinuousAt.congr (f := (fun x ↦ ∑ᶠ (x' : α), ((φ ε hε) x') x • F x')) ?_ ?_
    · exact ((φ ε hε).continuous_finsum_smul (fun i _ _ ↦ continuousAt_const)).continuousAt
    · apply Filter.Eventually.of_forall
      intro y
      symm
      exact tsum_eq_finsum (((φ ε hε).locallyFinite.point_finite y).subset
        (Function.support_smul_subset_left _ _))
  have hg_infdist : ∀ ε, (hε : 0 < ε) → ∀ x, infDist (g ε hε x) (f x) < ε := by
    intro ε hε x
    have heq : g ε hε x = ∑ᶠ x', (φ ε hε x' x) • F x' :=
      tsum_eq_finsum (((φ ε hε).locallyFinite.point_finite x).subset
        (Function.support_smul_subset_left _ _))
    rw [heq, ← Metric.mem_thickening_iff_infDist_lt ⟨F x, hF x⟩]
    apply ((hfv x).thickening ε).finsum_mem
        (fun x' ↦ (φ ε hε).nonneg x' x)
        ((φ ε hε).sum_eq_one (mem_univ x))
    intro x' hx'
    rw [Metric.mem_thickening_iff]
    have hx_in : x ∈ U ε x' :=
      hφ ε hε x' (subset_tsupport _ (Function.mem_support.mpr hx'))
    rw [hU_rw] at hx_in
    obtain ⟨z, hz_f, hz_ball⟩ := hx_in
    exact ⟨z, hz_f, mem_ball'.mp hz_ball⟩

  -- Goal is to do it again, but now we get a sequence of functions h:
  let h : ℕ → α → β
  | 0 => g 1 (by linarith)
  | n + 1 => sorry


  obtain ⟨h, hh_cont, hh_setdist⟩ : ∃ h : ℕ → α → β, (∀ n, Continuous (h n)) ∧ (∀ n x, infDist (h n x) (f x) < ((2 : ℝ)⁻¹) ^ n) ∧ (∀ n x, ‖h (n + 1) x - h n x‖ < ((2 : ℝ)⁻¹) ^ n) := by

    sorry

  -- let h : ℕ → α → β := sorry
  -- have hh_cont : ∀ n, Continuous (h n) := sorry
  -- have hh_setdist : ∀ n x, infDist (h n x) (f x) < ((2 : ℝ)⁻¹) ^ n := sorry
  -- have hh_precauchy : ∀ n x, ‖h (n + 1) x - h n x‖ < ((2 : ℝ)⁻¹) ^ n  := sorry

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
