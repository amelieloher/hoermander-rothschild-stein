-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.Frames
public import Mathlib.Data.Finset.Max

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators

namespace RothschildStein.G4

variable {ι : Type*} [Fintype ι] {n : ℕ}

/-- Frame weight, with integer values for signed scale deficits. -/
def frameWeight (w : ι → ℕ+) (B : Fin n → ι) : ℤ := ∑ i, ((w (B i) : ℕ) : ℤ)

/-- Suboptimality, expressed against each member of the finite
maximum instead of choosing an ordering of frames. -/
def IsSuboptimal (Z : ι → (Fin n → ℝ) → (Fin n → ℝ))
    (w : ι → ℕ+) (B : Fin n → ι) (x : Fin n → ℝ) (t r : ℝ) : Prop :=
  ∀ C : Fin n → ι, t * (|frameDet Z C x| * r ^ frameWeight w C) ≤
    |frameDet Z B x| * r ^ frameWeight w B

/-- Maximization provides a suboptimal frame
(BB Definition 9.27, p. 420). -/
theorem exists_suboptimal_frame (Z : ι → (Fin n → ℝ) → (Fin n → ℝ))
    (w : ι → ℕ+) {x : Fin n → ℝ} {t r : ℝ} (ht : t ≤ 1) (hr : 0 < r)
    (hspan : ∃ B : Fin n → ι, frameDet Z B x ≠ 0) :
    ∃ B, IsSuboptimal Z w B x t r := by
  classical
  obtain ⟨B₀, hB₀⟩ := hspan
  obtain ⟨B, hB, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun C : Fin n → ι => |frameDet Z C x| * r ^ frameWeight w C)
    ⟨B₀, Finset.mem_univ B₀⟩
  refine ⟨B, fun C => ?_⟩
  exact (mul_le_of_le_one_left (mul_nonneg (abs_nonneg _) (zpow_nonneg hr.le _)) ht).trans
    (hmax C (Finset.mem_univ C))

omit [Fintype ι] in
/-- Every suboptimal frame at a spanning point is nondegenerate
(BB Definition 9.27, p. 420). -/
theorem suboptimal_frame_ne_zero
    {Z : ι → (Fin n → ℝ) → (Fin n → ℝ)} {w : ι → ℕ+}
    {B : Fin n → ι} {x : Fin n → ℝ} {t r : ℝ} (ht : 0 < t) (hr : 0 < r)
    (hspan : ∃ C : Fin n → ι, frameDet Z C x ≠ 0) (hB : IsSuboptimal Z w B x t r) :
    frameDet Z B x ≠ 0 := by
  obtain ⟨C, hC⟩ := hspan
  have hpos := (mul_pos ht (mul_pos (abs_pos.mpr hC) (zpow_pos hr _))).trans_le (hB C)
  exact abs_pos.mp (pos_of_mul_pos_left hpos (zpow_nonneg hr.le _))

omit [Fintype ι] in
/-- Column replacement has precisely the single-factor deficit
(BB (9.26), p. 426). -/
theorem frameWeight_sub_update (w : ι → ℕ+) (B : Fin n → ι) (i : Fin n) (J : ι) :
    frameWeight w B - frameWeight w (Function.update B i J) =
      ((w (B i) : ℕ) : ℤ) - ((w J : ℕ) : ℤ) := by
  classical
  unfold frameWeight
  rw [← Finset.sum_sub_distrib]
  have h : (fun j : Fin n => ((w (B j) : ℕ) : ℤ) -
      ((w (Function.update B i J j) : ℕ) : ℤ)) =
      fun j => if j = i then ((w (B i) : ℕ) : ℤ) - ((w J : ℕ) : ℤ) else 0 := by
    funext j
    by_cases hj : j = i <;> simp [hj]
  rw [h]
  simp

omit [Fintype ι] in
/-- The sharp one-factor scale estimate at a suboptimal center
(BB Proposition 9.35, p. 426). -/
theorem frameCoefficient_le_of_suboptimal
    {Z : ι → (Fin n → ℝ) → (Fin n → ℝ)} {w : ι → ℕ+}
    {B : Fin n → ι} {x : Fin n → ℝ} {t r : ℝ} (ht : 0 < t) (hr : 0 < r)
    (hspan : ∃ C : Fin n → ι, frameDet Z C x ≠ 0) (hB : IsSuboptimal Z w B x t r)
    (J : ι) (i : Fin n) :
    |frameCoefficient Z B (Z J) i x| ≤
      t⁻¹ * r ^ (((w (B i) : ℕ) : ℤ) - ((w J : ℕ) : ℤ)) := by
  have hdet := suboptimal_frame_ne_zero ht hr hspan hB
  let C := Function.update B i J
  have hnum : |frameDet Z C x| ≤
      (t⁻¹ * r ^ (frameWeight w B - frameWeight w C)) * |frameDet Z B x| := by
    apply (mul_le_mul_iff_left₀ (mul_pos ht (zpow_pos hr (frameWeight w C)))).mp
    calc
      |frameDet Z C x| * (t * r ^ frameWeight w C) =
          t * (|frameDet Z C x| * r ^ frameWeight w C) := by ring
      _ ≤ |frameDet Z B x| * r ^ frameWeight w B := hB C
      _ = ((t⁻¹ * r ^ (frameWeight w B - frameWeight w C)) * |frameDet Z B x|) *
          (t * r ^ frameWeight w C) := by
        rw [zpow_sub₀ (ne_of_gt hr)]
        field_simp
  rw [frameCoefficient, abs_div, replacementDet_eq_update]
  apply (div_le_iff₀ (abs_pos.mpr hdet)).mpr
  simpa only [C, frameWeight_sub_update] using hnum

end RothschildStein.G4
