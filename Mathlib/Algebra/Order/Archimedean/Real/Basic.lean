/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Floris van Doorn
-/
module

public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Algebra.Order.Archimedean.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Order.Interval.Set.Disjoint
public import Mathlib.Algebra.Order.Group.Pointwise.CompleteLattice
import Mathlib.Data.Int.LeastGreatest

/-!
# The real numbers are an Archimedean floor ring, and a conditionally complete linear order.

-/

@[expose] public section

assert_not_exists Finset

open scoped Pointwise
open CauSeq

namespace Real
variable {ι : Sort*} {f : ι → ℝ} {s : Set ℝ} {a : ℝ}

instance instArchimedean : Archimedean ℝ :=
  archimedean_iff_rat_le.2 fun x =>
    Real.ind_mk x fun f =>
      let ⟨M, _, H⟩ := f.bounded' 0
      ⟨M, mk_le_of_forall_le ⟨0, fun i _ => Rat.cast_le.2 <| le_of_lt (abs_lt.1 (H i)).2⟩⟩

noncomputable instance : FloorRing ℝ :=
  Archimedean.floorRing _

theorem isCauSeq_iff_lift {f : ℕ → ℚ} : IsCauSeq abs f ↔ IsCauSeq abs fun i => (f i : ℝ) where
  mp H ε ε0 :=
    let ⟨δ, δ0, δε⟩ := exists_pos_rat_lt ε0
    (H _ δ0).imp fun i hi j ij => by dsimp; exact lt_trans (mod_cast hi _ ij) δε
  mpr H ε ε0 :=
    (H _ (Rat.cast_pos.2 ε0)).imp fun i hi j ij => by dsimp at hi; exact mod_cast hi _ ij

theorem of_near (f : ℕ → ℚ) (x : ℝ) (h : ∀ ε > 0, ∃ i, ∀ j ≥ i, |(f j : ℝ) - x| < ε) :
    ∃ h', Real.mk ⟨f, h'⟩ = x :=
  ⟨isCauSeq_iff_lift.2 (CauSeq.of_near _ (const abs x) h),
    sub_eq_zero.1 <|
      abs_eq_zero.1 <|
        (eq_of_le_of_forall_lt_imp_le_of_dense (abs_nonneg _)) fun _ε ε0 =>
          mk_near_of_forall_near <| (h _ ε0).imp fun _i h j ij => le_of_lt (h j ij)⟩

theorem exists_isLUB (hne : s.Nonempty) (hbdd : BddAbove s) : ∃ x, IsLUB s x := by
  rcases hne, hbdd with ⟨⟨L, hL⟩, ⟨U, hU⟩⟩
  have : ∀ d : ℕ, BddAbove { m : ℤ | ∃ y ∈ s, (m : ℝ) ≤ y * d } := by
    obtain ⟨k, hk⟩ := exists_int_gt U
    refine fun d => ⟨k * d, fun z h => ?_⟩
    rcases h with ⟨y, yS, hy⟩
    refine Int.cast_le.1 (hy.trans ?_)
    push_cast
    gcongr
    exact (hU yS).trans hk.le
  choose f hf using fun d : ℕ =>
    Int.exists_greatest_of_bdd (this d) ⟨⌊L * d⌋, L, hL, Int.floor_le _⟩
  have hf₁ : ∀ n > 0, ∃ y ∈ s, ((f n / n : ℚ) : ℝ) ≤ y := fun n n0 =>
    let ⟨y, yS, hy⟩ := (hf n).1
    ⟨y, yS, by simpa using (div_le_iff₀ (Nat.cast_pos.2 n0 : (_ : ℝ) < _)).2 hy⟩
  have hf₂ : ∀ n > 0, ∀ y ∈ s, (y - ((n : ℕ) : ℝ)⁻¹) < (f n / n : ℚ) := by
    intro n n0 y yS
    have := (Int.sub_one_lt_floor _).trans_le (Int.cast_le.2 <| (hf n).2 _ ⟨y, yS, Int.floor_le _⟩)
    simp only [Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast, gt_iff_lt]
    rwa [lt_div_iff₀ (Nat.cast_pos.2 n0 : (_ : ℝ) < _), sub_mul, inv_mul_cancel₀]
    exact (Nat.cast_pos.2 n0).ne'
  have hg : IsCauSeq abs (fun n => f n / n : ℕ → ℚ) := by
    intro ε ε0
    suffices ∀ j ≥ ⌈ε⁻¹⌉₊, ∀ k ≥ ⌈ε⁻¹⌉₊, (f j / j - f k / k : ℚ) < ε by
      refine ⟨_, fun j ij => abs_lt.2 ⟨?_, this _ ij _ le_rfl⟩⟩
      rw [neg_lt, neg_sub]
      exact this _ le_rfl _ ij
    intro j ij k ik
    replace ij := le_trans (Nat.le_ceil _) (Nat.cast_le.2 ij)
    replace ik := le_trans (Nat.le_ceil _) (Nat.cast_le.2 ik)
    have j0 := Nat.cast_pos.1 ((inv_pos.2 ε0).trans_le ij)
    have k0 := Nat.cast_pos.1 ((inv_pos.2 ε0).trans_le ik)
    rcases hf₁ _ j0 with ⟨y, yS, hy⟩
    refine lt_of_lt_of_le ((Rat.cast_lt (K := ℝ)).1 ?_) ((inv_le_comm₀ ε0 (Nat.cast_pos.2 k0)).1 ik)
    simpa using sub_lt_iff_lt_add'.2 (lt_of_le_of_lt hy <| sub_lt_iff_lt_add.1 <| hf₂ _ k0 _ yS)
  let g : CauSeq ℚ abs := ⟨fun n => f n / n, hg⟩
  refine ⟨mk g, ⟨fun x xS => ?_, fun y h => ?_⟩⟩
  · refine le_of_forall_lt_imp_le_of_dense fun z xz => ?_
    obtain ⟨K, hK⟩ := exists_nat_gt (x - z)⁻¹
    refine le_mk_of_forall_le ⟨K, fun n nK => ?_⟩
    replace xz := sub_pos.2 xz
    replace hK := hK.le.trans (Nat.cast_le.2 nK)
    have n0 : 0 < n := Nat.cast_pos.1 ((inv_pos.2 xz).trans_le hK)
    refine le_trans ?_ (hf₂ _ n0 _ xS).le
    rwa [le_sub_comm, inv_le_comm₀ (Nat.cast_pos.2 n0 : (_ : ℝ) < _) xz]
  · exact
      mk_le_of_forall_le
        ⟨1, fun n n1 =>
          let ⟨x, xS, hx⟩ := hf₁ _ n1
          le_trans hx (h xS)⟩

/-- A nonempty, bounded below set of real numbers has a greatest lower bound. -/
theorem exists_isGLB (hne : s.Nonempty) (hbdd : BddBelow s) : ∃ x, IsGLB s x := by
  have hne' : (-s).Nonempty := Set.nonempty_neg.mpr hne
  have hbdd' : BddAbove (-s) := bddAbove_neg.mpr hbdd
  use -Classical.choose (Real.exists_isLUB hne' hbdd')
  rw [← isLUB_neg]
  exact Classical.choose_spec (Real.exists_isLUB hne' hbdd')

open scoped Classical in
noncomputable instance : SupSet ℝ :=
  ⟨fun s => if h : s.Nonempty ∧ BddAbove s then Classical.choose (exists_isLUB h.1 h.2) else 0⟩

open scoped Classical in
theorem sSup_def (s : Set ℝ) :
    sSup s = if h : s.Nonempty ∧ BddAbove s then Classical.choose (exists_isLUB h.1 h.2) else 0 :=
  rfl

protected theorem isLUB_sSup (h₁ : s.Nonempty) (h₂ : BddAbove s) : IsLUB s (sSup s) := by
  simp only [sSup_def, dite_eq_left (And.intro h₁ h₂)]
  apply Classical.choose_spec

noncomputable instance : InfSet ℝ :=
  ⟨fun s => -sSup (-s)⟩

theorem sInf_def (s : Set ℝ) : sInf s = -sSup (-s) := rfl

protected theorem isGLB_sInf (h₁ : s.Nonempty) (h₂ : BddBelow s) : IsGLB s (sInf s) := by
  rw [sInf_def, ← isLUB_neg', neg_neg]
  exact Real.isLUB_sSup h₁.neg h₂.neg

noncomputable instance : ConditionallyCompleteLinearOrder ℝ where
  __ := Real.linearOrder
  __ := Real.lattice
  isLUB_csSup _ := Real.isLUB_sSup
  isGLB_csInf _ := Real.isGLB_sInf
  csSup_of_not_bddAbove s hs := by simp [hs, sSup_def]
  csInf_of_not_bddBelow s hs := by simp [hs, sInf_def, sSup_def]

@[deprecated (since := "2026-08-17")] alias lt_sInf_add_pos := _root_.lt_sInf_add_pos
@[deprecated (since := "2026-08-17")] alias add_neg_lt_sSup := _root_.add_neg_lt_sSup
@[deprecated (since := "2026-08-17")]
alias sInf_le_iff := csInf_le_iff_forall_pos_lt_add
@[deprecated (since := "2026-08-17")]
alias le_sSup_iff := le_csSup_iff_forall_neg_add_lt

instance instSupSetEmptyZero : SupSetEmptyZero ℝ where
  sSup_empty := dite_eq_right <| by simp

@[deprecated (since := "2026-08-17")] alias sSup_empty := sSup_empty_eq_zero

theorem sInf_univ : sInf (@Set.univ ℝ) = 0 := by
  simp [sInf_def]

@[deprecated (since := "2026-08-17")] alias iSup_of_isEmpty := iSup_of_empty₀
@[deprecated (since := "2026-08-17")] alias iSup_const_zero := iSup_const_zero₀
@[deprecated (since := "2026-08-17")] alias sSup_of_not_bddAbove := csSup_of_not_bddAbove₀
@[deprecated (since := "2026-08-17")] alias iSup_of_not_bddAbove := ciSup_of_not_bddAbove₀

theorem sSup_univ : sSup (@Set.univ ℝ) = 0 := csSup_of_not_bddAbove₀ not_bddAbove_univ

instance instInfSetZeroEmpty : InfSetEmptyZero ℝ where
  sInf_empty := by simp [sInf_def]

@[deprecated (since := "2026-08-17")] alias sInf_empty := sInf_empty_eq_zero

@[deprecated (since := "2026-08-17")] alias iInf_of_isEmpty := iInf_of_empty₀
@[deprecated (since := "2026-08-17")] alias iInf_const_zero := iInf_const_zero₀
@[deprecated (since := "2026-08-17")] alias sInf_of_not_bddBelow := csInf_of_not_bddBelow₀
@[deprecated (since := "2026-08-17")] alias iInf_of_not_bddBelow := ciInf_of_not_bddBelow₀

@[deprecated (since := "2026-08-17")] alias sSup_neg := sSup_neg₀
@[deprecated (since := "2026-08-17")] alias sInf_neg := sInf_neg₀

@[deprecated (since := "2026-08-17")] protected alias sSup_le := sSup_le₀
@[deprecated (since := "2026-08-17")] protected alias iSup_le := iSup_le₀
@[deprecated (since := "2026-08-17")] protected alias le_sInf := le_sInf₀
@[deprecated (since := "2026-08-17")] protected alias le_iInf := le_iInf₀
@[deprecated (since := "2026-08-17")] alias sSup_nonpos := _root_.sSup_nonpos₀
@[deprecated (since := "2026-08-17")] alias iSup_nonpos := _root_.iSup_nonpos₀
@[deprecated (since := "2026-08-17")] alias sInf_nonneg := _root_.sInf_nonneg₀
@[deprecated (since := "2026-08-17")] alias iInf_nonneg := _root_.iInf_nonneg₀
@[deprecated (since := "2026-08-17")] alias sSup_nonneg' := _root_.sSup_nonneg_of_exists₀
@[deprecated (since := "2026-08-17")] alias iSup_nonneg' := _root_.iSup_nonneg_of_exists₀
@[deprecated (since := "2026-08-17")] alias sInf_nonpos' := _root_.sInf_nonpos_of_exists₀
@[deprecated (since := "2026-08-17")] alias iInf_nonpos' := _root_.iInf_nonpos_of_exists₀
@[deprecated (since := "2026-08-17")] alias sSup_nonneg := sSup_nonneg₀
@[deprecated (since := "2026-08-17")] alias iSup_nonneg := _root_.iSup_nonneg₀
@[deprecated (since := "2026-08-17")] alias sInf_nonpos := _root_.sInf_nonpos₀
@[deprecated (since := "2026-08-17")] alias iInf_nonpos := _root_.iInf_nonpos₀
@[deprecated (since := "2026-08-17")] alias sInf_le_sSup := sInf_le_sSup₀

lemma iSup_nonneg_of_nonnegHomClass {ι F α : Type*} [FunLike F α ℝ] [NonnegHomClass F α ℝ] (f : F)
    (g : ι → α) :
    0 ≤ ⨆ i, f (g i) :=
  _root_.iSup_nonneg₀ (fun i ↦ apply_nonneg f (g i))

theorem cauSeq_converges (f : CauSeq ℝ abs) : ∃ x, f ≈ const abs x := by
  let s := {x : ℝ | const abs x < f}
  have lb : ∃ x, x ∈ s := exists_lt f
  have ub' : ∀ x, f < const abs x → ∀ y ∈ s, y ≤ x := fun x h y yS =>
    le_of_lt <| const_lt.1 <| CauSeq.lt_trans yS h
  have ub : ∃ x, ∀ y ∈ s, y ≤ x := (exists_gt f).imp ub'
  refine ⟨sSup s, ((lt_total _ _).resolve_left fun h => ?_).resolve_right fun h => ?_⟩
  · rcases h with ⟨ε, ε0, i, ih⟩
    refine (csSup_le lb (ub' _ ?_)).not_gt (sub_lt_self _ (half_pos ε0))
    refine ⟨_, half_pos ε0, i, fun j ij => ?_⟩
    rw [sub_apply, const_apply, sub_right_comm, le_sub_iff_add_le, add_halves]
    exact ih _ ij
  · rcases h with ⟨ε, ε0, i, ih⟩
    refine (le_csSup ub ?_).not_gt ((lt_add_iff_pos_left _).2 (half_pos ε0))
    refine ⟨_, half_pos ε0, i, fun j ij => ?_⟩
    rw [sub_apply, const_apply, add_comm, ← sub_sub, le_sub_iff_add_le, add_halves]
    exact ih _ ij

instance : CauSeq.IsComplete ℝ abs :=
  ⟨cauSeq_converges⟩

open Set

theorem iInf_Ioi_eq_iInf_rat_gt {f : ℝ → ℝ} (x : ℝ) (hf : BddBelow (f '' Ioi x))
    (hf_mono : Monotone f) : ⨅ r : Ioi x, f r = ⨅ q : { q' : ℚ // x < q' }, f q := by
  refine le_antisymm ?_ ?_
  · have : Nonempty { r' : ℚ // x < ↑r' } := by
      obtain ⟨r, hrx⟩ := exists_rat_gt x
      exact ⟨⟨r, hrx⟩⟩
    refine le_ciInf fun r => ?_
    obtain ⟨y, hxy, hyr⟩ := exists_rat_btwn r.prop
    refine ciInf_set_le hf (hxy.trans ?_)
    exact_mod_cast hyr
  · refine le_ciInf fun q => ?_
    have hq := q.prop
    rw [mem_Ioi] at hq
    obtain ⟨y, hxy, hyq⟩ := exists_rat_btwn hq
    refine (ciInf_le ?_ ?_).trans ?_
    · refine ⟨hf.some, fun z => ?_⟩
      rintro ⟨u, rfl⟩
      suffices hfu : f u ∈ f '' Ioi x from hf.choose_spec hfu
      exact ⟨u, u.prop, rfl⟩
    · exact ⟨y, hxy⟩
    · refine hf_mono (le_trans ?_ hyq.le)
      norm_cast

theorem not_bddAbove_coe : ¬ (BddAbove <| range (fun (x : ℚ) ↦ (x : ℝ))) := by
  dsimp only [BddAbove, upperBounds]
  rw [Set.not_nonempty_iff_eq_empty]
  ext
  simpa using exists_rat_gt _

theorem not_bddBelow_coe : ¬ (BddBelow <| range (fun (x : ℚ) ↦ (x : ℝ))) := by
  dsimp only [BddBelow, lowerBounds]
  rw [Set.not_nonempty_iff_eq_empty]
  ext
  simpa using exists_rat_lt _

theorem iUnion_Iic_rat : ⋃ r : ℚ, Iic (r : ℝ) = univ := by
  exact iUnion_Iic_of_not_bddAbove_range not_bddAbove_coe

theorem iInter_Iic_rat : ⋂ r : ℚ, Iic (r : ℝ) = ∅ := by
  exact iInter_Iic_eq_empty_iff.mpr not_bddBelow_coe

/-- Exponentiation is eventually larger than linear growth. -/
lemma exists_natCast_add_one_lt_pow_of_one_lt (ha : 1 < a) : ∃ m : ℕ, (m + 1 : ℝ) < a ^ m := by
  obtain ⟨k, posk, hk⟩ : ∃ k : ℕ, 0 < k ∧ 1 / k + 1 < a := by
    contrapose! ha
    refine le_of_forall_lt_rat_imp_le ?_
    intro q hq
    refine (ha q.den (by positivity)).trans ?_
    rw [← le_sub_iff_add_le, div_le_iff₀ (by positivity), sub_mul, one_mul]
    norm_cast at hq ⊢
    rw [← q.num_div_den, one_lt_div (by positivity)] at hq
    rw [q.mul_den_eq_num]
    norm_cast at hq ⊢
    lia
  use 2 * k ^ 2
  calc
    ((2 * k ^ 2 : ℕ) + 1 : ℝ) ≤ 2 ^ (2 * k) := mod_cast Nat.two_mul_sq_add_one_le_two_pow_two_mul _
    _ = (1 / k * k + 1 : ℝ) ^ (2 * k) := by simp [posk.ne']; norm_num
    _ ≤ ((1 / k + 1) ^ k : ℝ) ^ (2 * k) := by gcongr; exact mul_add_one_le_add_one_pow (by simp) _
    _ = (1 / k + 1 : ℝ) ^ (2 * k ^ 2) := by rw [← pow_mul, mul_left_comm, sq]
    _ < a ^ (2 * k ^ 2) := by gcongr

lemma exists_nat_pos_inv_lt {b : ℝ} (hb : 0 < b) :
    ∃ (n : ℕ), 0 < n ∧ (n : ℝ)⁻¹ < b := by
  refine (exists_nat_gt b⁻¹).imp fun k hk ↦ ?_
  have := (inv_pos_of_pos hb).trans hk
  refine ⟨Nat.cast_pos.mp this, ?_⟩
  rwa [inv_lt_comm₀ this hb]

end Real
