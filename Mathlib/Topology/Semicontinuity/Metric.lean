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

lemma Continuous.upperHemicontinuous_closedBall {f : α → β} (hf : Continuous f) (ε : ℝ) :
  UpperHemicontinuous (fun x ↦ Metric.closedBall (f x) ε) := by

  rw [upperHemicontinuous_iff_isClosed_compl_preimage_Iic_compl]
  intro u _hu
  have hfcomp : ((fun x ↦ closedBall (f x) ε) ⁻¹' (Iic uᶜ))ᶜ =
      {x | (closedBall (f x) ε ∩ u).Nonempty} := by
    simp [Set.ext_iff, Iic, Set.mem_compl_iff, Set.not_subset, Set.Nonempty]
  have heq : {x | (closedBall (f x) ε ∩ u).Nonempty} = f ⁻¹' cthickening ε u := by
    ext x
    simp only [mem_setOf, mem_preimage, mem_cthickening_iff, Set.Nonempty, infEDist, edist_dist]
    simp_rw [dist_comm]
    constructor
    · intro ⟨z, hz, hzu⟩
      apply iInf₂_le_of_le z hzu
      gcongr
      exact hz
    · sorry
  simpa [hfcomp, heq] using isClosed_cthickening.preimage hf

lemma LowerHemicontinuous.thickening {f : α → Set β} (hf : LowerHemicontinuous f) (ε : ℝ) :
  LowerHemicontinuous (fun x ↦ Metric.thickening ε (f x)) :=
  (hf.hasOpenLowerSections_thickening ε).lowerHemicontinuous

lemma UpperHemicontinuous.cthickening {f : α → Set β} (hf : UpperHemicontinuous f) (ε : ℝ) :
  UpperHemicontinuous (fun x ↦ Metric.cthickening ε (f x)) := sorry

end metric

end
