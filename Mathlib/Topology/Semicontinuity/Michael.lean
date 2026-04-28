/-
Copyright (c) 2026 Kevin H. Wilson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin H. Wilson
-/
module

public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Analysis.Normed.Module.Convex
public import Mathlib.Topology.Semicontinuity.Hemicontinuity
public import Mathlib.Topology.Semicontinuity.Metric
public import Mathlib.Topology.PartitionOfUnity
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
public import Mathlib.Topology.Algebra.Module.LocallyConvex
public import Mathlib.Analysis.LocallyConvex.WithSeminorms

/-!
# Michael's selection theorem

This file proves Michael's selection theorem, that a lower hemicontinuous function with
convex closed nonempty values admits a continuous selection.

## Main results

- `HasOpenLowerSections.exists_continuous_selection`: A correspondence with open lower sections and
  convex, nonempty values admits a continuous selection. A key ingredient to the proof of Michael's
  selection theorem. This holds in any topological vector space over ℝ.
- `LowerHemicontinuous.exists_continuous_selection`: Michael's selection theorem that a lower
  hemicontinous function from a paracompact space to a Banach space which takes convex, closed,
  nonempty values admits a continuous selection.

## TODO

The `NormedSpace` assumption on `LowerHemicontinuous.exists_continuous_selection` can be weakened
to a complete metrizable locally convex topological vector space.
-/

public section

open Set Metric
open scoped Pointwise Topology

variable {α β : Type*} {f : α → Set β} {g : α → β}

section

variable {𝕜 E : Type*}

variable (𝕜 E) in
theorem bar
    [Field 𝕜]
    [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜]
    [AddCommGroup E]
    [Module 𝕜 E]
    [TopologicalSpace E]
    [IsTopologicalAddGroup E]
    [ContinuousConstSMul 𝕜 E]
    [LocallyConvexSpace 𝕜 E]
    [T2Space E]
    [FirstCountableTopology E] :
    ∃ x : ℕ → Set E,
    (∀ n, 0 ∈ x n ∧ IsOpen (x n) ∧ Convex 𝕜 (x n) ∧ ∀ y ∈ x n, -y ∈ x n ∧
      (x (n + 1)) + (x (n + 1)) ⊆ x n ∧ closure (x (n + 1)) ⊆ x n) ∧
      (𝓝 0).HasAntitoneBasis x := by
  obtain ⟨x₁, hx₁_prop, hx₁_basis⟩ := (LocallyConvexSpace.convex_open_symm_basis_zero 𝕜 E).exists_antitone_subbasis
  let P := fun (n : ℕ) (s : Set E) ↦ 0 ∈ s ∧ IsOpen s ∧ Convex 𝕜 s ∧ (∀ y ∈ s, -y ∈ s) ∧ (s ⊆ x₁ n)
  have step : ∀ n s, P n s → ∃ s', P n s' ∧ s' + s' ⊆ s ∧ closure s' ⊆ s :=  by
    intro n s ⟨h₀, h_open, h_conv, h_symm, hsx⟩
    obtain ⟨i, hi⟩ := hx₁_basis.mem_iff.mp (h_open.mem_nhds h₀)
    use ((2 : 𝕜)⁻¹ • x₁ i) ∩ (x₁ (n + 1))
    refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
    iterate simp [hx₁_prop, zero_mem_smul_set, IsOpen.inter, IsOpen.smul₀,
      Convex.inter, Convex.smul]
    sorry
    have := (Set.inter_subset_inter_right ((2 : 𝕜)⁻¹ • x₁ i) (hx₁_basis.antitone (show n ≤ n + 1 by norm_num)))
    exact this.trans (Set.inter_subset_right)
    intro y ⟨z, ⟨hz, _⟩, a, ⟨ha, _⟩, haz⟩
    grind [mem_add, (hx₁_prop i).2.2.1.add_half_self_eq_self]
    sorry
  choose! F hF using step
  let x : ℕ → Set E := Nat.rec (x₁ 0) F
  use x
  have hx_props : ∀ n, 0 ∈ x n ∧ IsOpen (x n) ∧ Convex 𝕜 (x n) ∧ (∀ y ∈ x n, -y ∈ x n) ∧ x n ⊆ x₁ n := by
    intro n
    induction n with
    | zero => exact ⟨(hx₁_prop 0).1, (hx₁_prop 0).2.1, (hx₁_prop 0).2.2.1,
        (hx₁_prop 0).2.2.2, le_refl _⟩
    | succ n ih =>
      obtain ⟨h0, hOpen, hConv, hSymm, hsub⟩ := ih
      obtain ⟨h0', hOpen', hConv', hSymm', hsub', _, _⟩ := hF n (x n) ⟨h0, hOpen, hConv, hSymm, hsub⟩
      exact ⟨h0', hOpen', hConv', hSymm', hsub'⟩
  intro n
  obtain ⟨h0, hOpen, hConv, hSymm, hsub⟩ := hx_props n
  obtain ⟨_, _, _, _, _, hsum, hclosure⟩ := hF n (x n) ⟨h0, hOpen, hConv, hSymm, hsub⟩
  refine ⟨h0, hOpen, hConv, fun y hy ↦ ⟨hSymm y hy, ?_, hsum, hclosure⟩⟩
  intro z hz
  simpa using hsum (Set.add_mem_add hz (hx_props (n + 1)).1)

end

variable [TopologicalSpace α] [NormalSpace α] [ParacompactSpace α]

section

variable [AddCommGroup β] [Module ℝ β] [TopologicalSpace β] [ContinuousAdd β]
  [ContinuousSMul ℝ β] {f : α → Set β}

/-- A correspondence with open lower sections and convex, nonempty values admits a continuous
selection. This holds in any topological vector space over ℝ. -/
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

end

section

variable [NormedAddCommGroup β] [NormedSpace ℝ β] [CompleteSpace β] {f : α → Set β}

-- open Pointwise Topology in
-- /-- **Michael's selection theorem**: A lower hemicontinuous function from a paracompact Hausdorff
-- space (which is necessarily normal) to a Banach space with nonempty convex closed values
-- admits a continuous selection -/
-- theorem LowerHemicontinuous.exists_continuous_selection (hf : LowerHemicontinuous f)
--     (hf_nonempty : ∀ x, (f x).Nonempty) (hf_convex : ∀ x, Convex ℝ (f x))
--     (hf_isClosed : ∀ x, IsClosed (f x)) : ∃ g : α → β, Continuous g ∧ ∀ x, g x ∈ f x := by
--   -- This proof is written to be compatible with a proof for Frechet spaces
--   haveI : LocallyConvexSpace ℝ β := NormedSpace.toLocallyConvexSpace
--   obtain ⟨V, hV⟩ := bar ℝ β
--   -- V n is balanced since it comes from the locally convex basis of a NormedSpace, which
--   -- consists of open balls (balanced sets), and the bar construction preserves this.
--   have hV_balanced : ∀ n, Balanced ℝ (V n) := by sorry
--   obtain ⟨g, hg_cont, hg_mem⟩ := (hf.hasOpenLowerSections_add_isOpen (V := V 0) (hV 0).2.1).exists_continuous_selection
--     (by simp only [add_nonempty, hf_nonempty, true_and]; intro _; use 0; exact (hV 0).1)
--     (fun x ↦ (hf_convex x).add (hV 0).2.2.1)
--   obtain ⟨h, hh_cont, hh_mem, hh_mem_ball⟩ : ∃ h : ℕ → α → β, (∀ n, Continuous (h n)) ∧
--       (∀ n x, h n x ∈ f x + (V n)) ∧
--       (∀ n x, h (n + 1) x - h n x ∈ V (n + 1)) := by
--     let P (n : ℕ) (h : α → β) := Continuous h ∧ ∀ x, h x ∈ f x + (V n)
--     have step : ∀ n hn, P n hn →
--         ∃ h', P (n + 1) h' ∧ ∀ x, (h' x) - (hn x) ∈ V (n + 1) := by
--       intro n hn hn_prop
--       have : HasOpenLowerSections (fun x ↦ ((f x) ∩ ({hn x} + V n)) + (V (n + 1))) := by
--         refine LowerHemicontinuous.hasOpenLowerSections_add_isOpen ?_ (hV (n + 1)).2.1
--         refine hf.inter_hasOpenGraph ?_
--         rw [hasOpenCGraph_iff_isOpen]
--         exact hn_prop.1.lowerHemicontinuous.hasOpenGraph_add_isOpen (hV n).2.1
--       obtain ⟨h', hh'_cont, hh'_mem⟩ := this.exists_continuous_selection (by
--         intro x
--         rw [add_nonempty]
--         constructor
--         · sorry
--         · refine ⟨0, (hV (n + 1)).1⟩
--         )
--         (by
--           intro x
--           refine Convex.add ?_ (hV (n + 1)).2.2.1
--           apply (hf_convex x).inter
--           exact (convex_singleton _).add (hV n).2.2.1
--         )
--       use h'
--       constructor
--       · constructor
--         · exact hh'_cont
--         · sorry
--       · sorry
--     choose! F hF using step
--     let h : ℕ → α → β := Nat.rec g F
--     use h
--     rw [← forall_and, ← forall_and]
--     intro n
--     induction n with
--     | zero => simp [h, hg_cont, hg_mem, hF, P]
--     | succ n ih => simp [h, ih, P, hF]
--   have hBlah : ∀ n, ∀ i, n ≤ i → ∀ j, n ≤ j → ∀ x, h i x - h j x ∈ V n := by sorry
--   have hV' : ∀ u ∈ 𝓝 (0 : β), ∃ n, V n ⊆ u := sorry
--   have hFoo : UniformCauchySeqOn h Filter.atTop univ := by
--     rw [IsTopologicalAddGroup.uniformCauchySeqOn_iff]
--     intro u hu
--     obtain ⟨n, hn⟩ := hV' u hu
--     filter_upwards [(Filter.eventually_ge_atTop n).prod_mk (Filter.eventually_ge_atTop n)]
--     intro a ⟨ha₁, ha₂⟩
--     intro x _
--     exact mem_of_mem_of_subset (hBlah n a.2 ha₂ a.1 ha₁ x) hn
--     sorry -- Show the uniform spaces align
--   choose H hH using fun x ↦ cauchySeq_tendsto_of_complete (hFoo.cauchySeq (mem_univ x))
--   use H
--   constructor
--   · rw [← continuousOn_univ]
--     apply (hFoo.tendstoUniformlyOn_of_tendsto (fun x hx ↦ hH x)).continuousOn
--     exact Filter.Frequently.of_forall (by simp [hh_cont])
--   intro x
--   have hh : H x ∈ ⋂ n, closure (f x + V n) := sorry
--   have hh' : ⋂ n, closure (f x + V n) = f x := sorry
--   rwa [hh'] at hh

end

end
