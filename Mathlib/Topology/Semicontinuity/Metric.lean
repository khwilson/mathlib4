/-
Copyright (c) 2026 Kevin H. Wilson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin H. Wilson
-/
module

public import Mathlib.Topology.Semicontinuity.Hemicontinuity
public import Mathlib.Topology.MetricSpace.Thickening
public import Mathlib.Topology.Filter

/-!
# Constructions of hemicontinuous maps to metric spaces

This file provides some standard constructions of hemicontinuous maps and maps with
open sections images are metric spaces.

## Main Results

- `Continuous.lowerHemicontinuous_ball`: Given a continuous map `f : α → β` where
  `β` is a metric space, the thickening `g x = ball ε (f x)` is lower hemicontinuous
- `Continuous.upperHemicontinuous_closedBall`: Given a continuous map `f : α → β` where
  `β` is a metric space, the thickening `g x = closedBall ε (f x)` is upper hemicontinuous
-/

@[expose] public section

open Metric Set
open scoped Pointwise Topology

variable {α β : Type*} [TopologicalSpace α]

section topologicalSpace

variable [TopologicalSpace β]

lemma Continuous.lowerHemicontinuous {f : α → β} (hf : Continuous f) :
    LowerHemicontinuous (fun x ↦ {f x}) := by
  rw [lowerHemicontinuous_iff_isOpen_inter_nonempty]
  intro u hu
  have : {x | f x ∈ u} = f ⁻¹' u := by ext; simp
  simpa [this] using hf.isOpen_preimage _ hu

lemma Continuous.upperHemicontinuous {f : α → β} (hf : Continuous f) :
    UpperHemicontinuous (fun x ↦ {f x}) := by
  rw [upperHemicontinuous_iff_forall_isOpen]
  intro x u hu hxu
  simp [hf.continuousAt.eventually_mem <| hu.mem_nhds (singleton_subset_iff.mp hxu)]

end topologicalSpace

section topologicalVectorSpace

open scoped Pointwise

variable [AddCommGroup β] [TopologicalSpace β] [ContinuousSub β]

theorem LowerHemicontinuous.hasOpenGraph_add_isOpen {f : α → Set β}
    (hf : LowerHemicontinuous f) {V : Set β} (hV : IsOpen V) :
    IsOpen {x : α × β | x.2 ∈ (fun x ↦ f x + V) x.1} := by
  -- A set is open if it's a neighborhood of all its points
  rw [isOpen_iff_forall_mem_open]
  rintro ⟨x, y⟩ hxy
  change y ∈ f x + V at hxy

  -- By definition of set addition, y = z + v
  rw [Set.mem_add] at hxy
  obtain ⟨z, hz, v, hv, rfl⟩ := hxy

  -- The preimage of V under subtraction is an open set
  have h_pre_open : IsOpen ((fun p : β × β ↦ p.1 - p.2) ⁻¹' V) :=
    continuous_sub.isOpen_preimage _ hV

  -- The point (z + v, z) is in this preimage because (z + v) - z = v ∈ V
  have h_mem_pre : (z + v, z) ∈ (fun p : β × β ↦ p.1 - p.2) ⁻¹' V := by
    change (z + v) - z ∈ V
    have h_eq : z + v - z = v := by abel
    rw [h_eq]
    exact hv

  -- Because the preimage is open in the product space, there exist basic open sets around the point
  rw [isOpen_prod_iff] at h_pre_open
  obtain ⟨O, U, hO_open, hU_open, hz_v_O, hz_U, hOU⟩ :=
    h_pre_open (z + v) z h_mem_pre

  -- Apply lower hemicontinuity to get an open neighborhood in α
  rw [lowerHemicontinuous_iff_isOpen_inter_nonempty] at hf
  have hU_alpha : IsOpen {x' | (f x' ∩ U).Nonempty} := hf U hU_open
  have hx_mem : x ∈ {x' | (f x' ∩ U).Nonempty} := ⟨z, hz, hz_U⟩

  -- The product of these sets is an open neighborhood in α × β
  have h_prod_open : IsOpen ({x' | (f x' ∩ U).Nonempty} ×ˢ O) :=
    hU_alpha.prod hO_open

  -- Provide this open neighborhood to satisfy the goal
  refine ⟨_, ?_, h_prod_open, ⟨hx_mem, hz_v_O⟩⟩
  rintro ⟨x', y'⟩ ⟨hx', hy'⟩
  change y' ∈ f x' + V

  obtain ⟨z', hz'_f, hz'_U⟩ := hx'

  -- Since y' ∈ O and z' ∈ U, their difference lands in V
  have h_sub : y' - z' ∈ V := hOU (mk_mem_prod hy' hz'_U)

  -- Thus y' = z' + (y' - z') which means it is in f x' + V
  rw [Set.mem_add]
  exact ⟨z', hz'_f, y' - z', h_sub, by abel⟩

lemma LowerHemicontinuous.hasOpenLowerSections_add_isOpen {f : α → Set β}
    (hf : LowerHemicontinuous f) {V : Set β} (hV : IsOpen V) :
    HasOpenLowerSections (fun x ↦ f x + V) := by
  rw [hasOpenLowerSections_iff_isOpen]
  intro b
  -- Translate the pointwise addition into a set intersection
  have h_eq : {x | b ∈ f x + V} = {x | (f x ∩ (fun y ↦ b - y) ⁻¹' V).Nonempty} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_add, Set.Nonempty, Set.mem_inter_iff, Set.mem_preimage]
    constructor
    · rintro ⟨y, hy, v, hv, rfl⟩
      use y, hy
      convert hv using 1
      abel
    · rintro ⟨y, hy, hv⟩
      use y, hy, b - y, hv
      abel
  rw [h_eq]
  let U := ((fun y ↦ b - y) ⁻¹' V)
  have hU : IsOpen U := hV.preimage (continuous_const.sub continuous_id)
  rw [lowerHemicontinuous_iff_isOpen_inter_nonempty] at hf
  exact hf U hU

omit [AddCommGroup β] [ContinuousSub β] in
lemma LowerHemicontinuous.inter_hasOpenGraph {f g : α → Set β}
    (hf : LowerHemicontinuous f) (hg : HasOpenCGraph g) :
    LowerHemicontinuous (fun x ↦ f x ∩ g x) := by
  simp_rw [lowerHemicontinuous_iff_isOpen_inter_nonempty] at ⊢ hf
  intro t ht
  rw [isOpen_iff_forall_mem_open]
  intro x ⟨y, ⟨hyf, hyg⟩, hyt⟩
  obtain ⟨U, V, hU, hV, hxU, hyV, hUV⟩ := (isOpen_prod_iff.mp hg.isOpen) x y hyg
  refine ⟨U ∩ {x' | (f x' ∩ (t ∩ V)).Nonempty}, ?_, hU.inter (hf _ (ht.inter hV)),
      ⟨hxU, y, hyf, hyt, hyV⟩⟩
  intro x' ⟨hx'U, z, hzf, hzt, hzV⟩
  exact ⟨z, ⟨hzf, hUV (Set.mk_mem_prod hx'U hzV)⟩, hzt⟩

end topologicalVectorSpace

section metric

variable [MetricSpace β]

lemma LowerHemicontinuous.hasOpenLowerSections_thickening {f : α → Set β}
    (hf : LowerHemicontinuous f) (ε : ℝ) :
    HasOpenLowerSections (fun x ↦ Metric.thickening ε (f x)) := by
  rw [hasOpenLowerSections_iff_isOpen]
  intro b
  have : {x | b ∈ thickening ε (f x)} = (f ⁻¹' (Iic (ball b ε)ᶜ))ᶜ := by
    ext; simp [Set.not_subset, mem_thickening_iff, dist_comm b]
  exact this ▸ lowerHemicontinuous_iff_isOpen_compl_preimage_Iic_compl.mp hf _ isOpen_ball

lemma Continuous.hasOpenLowerSections_ball {f : α → β} (hf : Continuous f) (ε : ℝ) :
    HasOpenLowerSections (fun x ↦ Metric.ball (f x) ε) := by
  have : (fun x ↦ thickening ε {f x}) = fun x ↦ ball (f x) ε := by ext; simp
  simpa [← this] using hf.lowerHemicontinuous.hasOpenLowerSections_thickening ε

lemma LowerHemicontinuous.thickening {f : α → Set β} (hf : LowerHemicontinuous f) (ε : ℝ) :
  LowerHemicontinuous (fun x ↦ Metric.thickening ε (f x)) :=
  (hf.hasOpenLowerSections_thickening ε).lowerHemicontinuous

end metric

end
