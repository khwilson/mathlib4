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

theorem fool' [Field 𝕜]
    [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜]
    [AddCommGroup E]
    [Module 𝕜 E]
    {s : Set E} (hs : Convex 𝕜 s) :
    (2 : 𝕜)⁻¹ • s + (2 : 𝕜)⁻¹ • s = s := by
  rw [← hs.add_smul (by norm_num) (by norm_num)]
  ring_nf
  rw [one_smul]

theorem fool [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  {s : Set E} (h0 : 0 ∈ s) (ho : IsOpen s) : closure s ⊆ s + s := by
  intro x hx
  rw [mem_closure_iff_nhds] at hx
  have hkey : (fun y => x - y) ⁻¹' s ∈ 𝓝 x :=
    (ho.preimage (continuous_const.sub continuous_id)).mem_nhds (by simpa)
  obtain ⟨a, ha_mem, ha_s⟩ := hx _ hkey
  exact Set.mem_add.mpr ⟨x - a, ha_mem, a, ha_s, sub_add_cancel x a⟩

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
    (∀ n, 0 ∈ x n ∧ IsOpen (x n) ∧ Convex 𝕜 (x n) ∧
      (x (n + 1)) ⊆ x n ∧
      (x (n + 1)) + (x (n + 1)) ⊆ x n ∧
      closure (x (n + 1)) ⊆ x n) := by
  obtain ⟨x₁, hx₁_prop, hx₁_basis⟩ :=
    (LocallyConvexSpace.convex_open_basis_zero 𝕜 E).exists_antitone_subbasis
  have step :
      ∀ (n : ℕ) (s : Set E),
        0 ∈ s ∧ IsOpen s ∧ Convex 𝕜 s ∧ (s ⊆ x₁ n) →
        ∃ s', 0 ∈ s' ∧ IsOpen s' ∧ Convex 𝕜 s' ∧
          (s' ⊆ x₁ (n + 1)) ∧
          s' + s' ⊆ s ∧
          closure s' ⊆ s := by
    intro n s hs
    rcases hs with ⟨h0s, hOpen, hConv, hsx⟩
    -- continuity of addition gives a neighborhood shrinking
    have hnhds : s ∈ 𝓝 (0 : E) := by
      simpa using IsOpen.mem_nhds hOpen h0s
    obtain ⟨t, ht0, htOpen, htConv, ht_small, ht_cl⟩ :
        ∃ t, 0 ∈ t ∧ IsOpen t ∧ Convex 𝕜 t ∧ t + t ⊆ s ∧ closure t ⊆ s := by
      obtain ⟨i, hi⟩ := hx₁_basis.mem_iff.mp hnhds
      have ht0 : (0 : E) ∈ (2 : 𝕜)⁻¹ • x₁ i := ⟨0, (hx₁_prop i).1, smul_zero _⟩
      have htOpen : IsOpen ((2 : 𝕜)⁻¹ • x₁ i) :=
        (hx₁_prop i).2.1.smul₀ (c := (2 : 𝕜)⁻¹) (by norm_num)
      exact ⟨(2 : 𝕜)⁻¹ • x₁ i, ht0, htOpen, (hx₁_prop i).2.2.smul _,
        by rwa [fool' (hx₁_prop i).2.2],
        (fool ht0 htOpen |>.trans_eq (fool' (hx₁_prop i).2.2)).trans hi⟩
    -- intersect with the basis element to ensure filtration
    exact ⟨t ∩ x₁ (n + 1), ⟨ht0, (hx₁_prop (n + 1)).1⟩, htOpen.inter (hx₁_prop (n + 1)).2.1,
      htConv.inter (hx₁_prop (n + 1)).2.2, fun _ hx ↦ hx.2,
      by rintro x ⟨a, ha, b, hb, hab⟩; exact ht_small ⟨a, ha.1, b, hb.1, hab⟩,
      (closure_mono inter_subset_left).trans ht_cl⟩
  choose! F hF using step
  let x : ℕ → Set E := Nat.rec (x₁ 0) F
  use x
  have hx_props : ∀ n, 0 ∈ x n ∧ IsOpen (x n) ∧ Convex 𝕜 (x n) ∧ x n ⊆ x₁ n := by
    intro n
    induction n with
    | zero => exact ⟨(hx₁_prop 0).1, (hx₁_prop 0).2.1, (hx₁_prop 0).2.2, le_refl _⟩
    | succ n ih =>
      obtain ⟨h0, hOpen, hConv, hsub⟩ := ih
      obtain ⟨h0', hOpen', hConv', hsub', _, _⟩ := hF n (x n) ⟨h0, hOpen, hConv, hsub⟩
      exact ⟨h0', hOpen', hConv', hsub'⟩
  intro n
  obtain ⟨h0, hOpen, hConv, hsub⟩ := hx_props n
  obtain ⟨_, _, _, _, hsum, hclosure⟩ := hF n (x n) ⟨h0, hOpen, hConv, hsub⟩
  refine ⟨h0, hOpen, hConv, ?_, hsum, hclosure⟩
  intro y hy
  have h0_next := (hx_props (n + 1)).1
  simpa using hsum (Set.add_mem_add hy h0_next)

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

open Pointwise Topology in
/-- **Michael's selection theorem**: A lower hemicontinuous function from a paracompact Hausdorff
space (which is necessarily normal) to a Banach space with nonempty convex closed values
admits a continuous selection -/
theorem LowerHemicontinuous.exists_continuous_selection (hf : LowerHemicontinuous f)
    (hf_nonempty : ∀ x, (f x).Nonempty) (hf_convex : ∀ x, Convex ℝ (f x))
    (hf_isClosed : ∀ x, IsClosed (f x)) : ∃ g : α → β, Continuous g ∧ ∀ x, g x ∈ f x := by
  -- This proof is written to be compatible with a proof for Frechet spaces
  haveI : LocallyConvexSpace ℝ β := by sorry
  obtain ⟨V, hV⟩ := bar ℝ β
  obtain ⟨g, hg_cont, hg_mem⟩ := (hf.hasOpenLowerSections_add_isOpen (V := V 0) (hV 0).2.1).exists_continuous_selection
    (by simp only [add_nonempty, hf_nonempty, true_and]; intro _; use 0; exact (hV 0).1)
    (fun x ↦ (hf_convex x).add (hV 0).2.2.1)
  obtain ⟨h, hh_cont, hh_mem, hh_mem_ball⟩ : ∃ h : ℕ → α → β, (∀ n, Continuous (h n)) ∧
      (∀ n x, h n x ∈ f x + (V n)) ∧
      (∀ n x, h (n + 1) x - h n x ∈ V (n + 1)) := by
    let P (n : ℕ) (h : α → β) :=
      Continuous h ∧ ∀ x, h x ∈ f x + (V n)
    have step : ∀ n hn, P n hn →
        ∃ h', P (n + 1) h' ∧ ∀ x, (h' x) - (hn x) ∈ V (n + 1) := by
      intro n hn hn_prop
      have : HasOpenLowerSections (fun x ↦ (f x + V (n + 1)) ∩ ({hn x} + V (n + 1))) :=
        HasOpenLowerSections.inter
          (hf.hasOpenLowerSections_add_isOpen (V := V (n + 1)) (hV _).2.1)
          (hn_prop.1.lowerHemicontinuous.hasOpenLowerSections_add_isOpen
            (V := V (n + 1)) (hV _).2.1)
      obtain ⟨h', hh'_cont, hh'_mem⟩ := this.exists_continuous_selection sorry
        fun x ↦ ((hf_convex _).add (hV _).2.2.1).inter <| (convex_singleton _).add (hV _).2.2.1
      use h'
      constructor
      · constructor
        · exact hh'_cont
        · exact fun x ↦ (hh'_mem x).1
      · intro x
        have := (hh'_mem x).2
        obtain ⟨y, hy, z, hz, hyz⟩ := this
        simp at hy
        rw [← hy, ← hyz]
        simp [hz]
    choose! F hF using step
    let h : ℕ → α → β := Nat.rec g F
    use h
    rw [← forall_and, ← forall_and]
    intro n
    induction n with
    | zero => simp [h, hg_cont, hg_mem, hF, P]
    | succ n ih => simp [h, ih, P, hF]
  have hBlah : ∀ n, ∀ i, n ≤ i → ∀ j, n ≤ j → ∀ x, h i x - h j x ∈ V n := by sorry
  have hV' : ∀ u ∈ 𝓝 (0 : β), ∃ n, V n ⊆ u := sorry
  have hFoo : UniformCauchySeqOn h Filter.atTop univ := by
    rw [IsTopologicalAddGroup.uniformCauchySeqOn_iff]
    intro u hu
    obtain ⟨n, hn⟩ := hV' u hu
    filter_upwards [(Filter.eventually_ge_atTop n).prod_mk (Filter.eventually_ge_atTop n)]
    intro a ⟨ha₁, ha₂⟩
    intro x _
    exact mem_of_mem_of_subset (hBlah n a.2 ha₂ a.1 ha₁ x) hn
    sorry -- Show the uniform spaces align
  choose H hH using fun x ↦ cauchySeq_tendsto_of_complete (hFoo.cauchySeq (mem_univ x))
  use H
  constructor
  · rw [← continuousOn_univ]
    apply (hFoo.tendstoUniformlyOn_of_tendsto (fun x hx ↦ hH x)).continuousOn
    exact Filter.Frequently.of_forall (by simp [hh_cont])
  intro x
  have hh : H x ∈ ⋂ n, closure (f x + V n) := sorry
  have hh' : ⋂ n, closure (f x + V n) = f x := sorry
  rwa [hh'] at hh

end

end
