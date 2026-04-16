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

/-!
# Michael's selection theorem

This file proves Michael's selection theorem, that a lower hemicontinuous function with
convex closed values admits a continuous selection
-/

public section

variable {α β : Type*} [TopologicalSpace α] [ParacompactSpace α]
  [NormedAddCommGroup β] [NormedSpace ℝ β] [CompleteSpace β] [TopologicalSpace.SeparableSpace β]
  {f : α → Set β} (hf : LowerHemicontinuous f)

theorem michael (hfc : ∀ x, IsClosed (f x)) (hfv : ∀ x, Convex ℝ (f x)) :
    ∃ g : α → β, Continuous g := by
  -- Preliminary steps
  -- Step 1: Define a function F : α → β such that ∀ x, F x ∈ f x
  -- Step 2: For all ε > 0, write U ε x = {x' ∈ α | F(x') ∩ B(F x; ε)}
  -- Step 3: Note that U ε x is open (by lower hemicontinuity), nonempty, and a cover
  -- Step 4: Write a function h ε x ∈ U ε x for each ε and x
  -- Step 5: For each ε, choose a partition of unity φ ε subordinate to U ε
  -- Step 6: Write g ε x = ∑' x, (φ ε x) * (h ε x).
  -- Step 7: Show that this is well-defined (for each `x` it is a finite sum since φ is a
  --   partition of unity)
  -- Step 8: Show that g ε x ∈ F x for all ε and x since F x is convex closed and
  --   and φ ε is a partition of unity
  sorry

end
