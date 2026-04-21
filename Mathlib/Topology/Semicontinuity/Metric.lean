/-
Copyright (c) 2026 Kevin H. Wilson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin H. Wilson
-/
module

public import Mathlib.Topology.Semicontinuity.Hemicontinuity
public import Mathlib.Topology.MetricSpace.Thickening

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

variable {α β : Type*} [TopologicalSpace α] [MetricSpace β]

lemma Continuous.lowerHemicontinuous_ball {f : α → β} (hf : Continuous f) (ε : ℝ) :
    LowerHemicontinuous (fun x ↦ Metric.ball (f x) ε) := by
  rw [lowerHemicontinuous_iff_isOpen_compl_preimage_Iic_compl]
  intro u _hu
  have hfcomp : ((fun x ↦ ball (f x) ε) ⁻¹' (Iic uᶜ))ᶜ = {x | (ball (f x) ε ∩ u).Nonempty} := by
    simp [Set.ext_iff, Iic, Set.mem_compl_iff, Set.not_subset, Set.Nonempty]
  have heq : {x | (ball (f x) ε ∩ u).Nonempty} = f ⁻¹' thickening ε u := by
    ext x
    simp only [mem_setOf, mem_preimage, mem_thickening_iff, dist_comm (f x)]
    exact ⟨fun ⟨z, hz, hzu⟩ ↦ ⟨z, hzu, hz⟩, fun ⟨z, hzu, hz⟩ ↦ ⟨z, hz, hzu⟩⟩
  simpa [hfcomp, heq] using isOpen_thickening.preimage hf

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

lemma Continuous.hasOpenLowerSections_ball {f : α → β} (hf : Continuous f) (ε : ℝ) :
    HasOpenLowerSections (fun x ↦ Metric.ball (f x) ε) := by
  rw [hasOpenLowerSections_iff_isOpen]
  intro b
  have : {x | b ∈ ball (f x) ε} = f ⁻¹' ball b ε := by
    ext; simp [dist_comm]
  exact this ▸ isOpen_ball.preimage hf

lemma LowerHemicontinuous.hasOpenLowerSections_thickening {f : α → Set β}
    (hf : LowerHemicontinuous f) (ε : ℝ) :
    HasOpenLowerSections (fun x ↦ Metric.thickening ε (f x)) := by
  rw [hasOpenLowerSections_iff_isOpen]
  intro b
  have : {x | b ∈ thickening ε (f x)} = (f ⁻¹' (Iic (ball b ε)ᶜ))ᶜ := by
    ext; simp [Set.not_subset, mem_thickening_iff, dist_comm b]
  exact this ▸ lowerHemicontinuous_iff_isOpen_compl_preimage_Iic_compl.mp hf _ isOpen_ball

lemma LowerHemicontinuous.thickening {f : α → Set β} (hf : LowerHemicontinuous f) (ε : ℝ) :
  LowerHemicontinuous (fun x ↦ Metric.thickening ε (f x)) :=
  (hf.hasOpenLowerSections_thickening ε).lowerHemicontinuous

lemma UpperHemicontinuous.cthickening {f : α → Set β} (hf : UpperHemicontinuous f) (ε : ℝ) :
  UpperHemicontinuous (fun x ↦ Metric.cthickening ε (f x)) := sorry

end
