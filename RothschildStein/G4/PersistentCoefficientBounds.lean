-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.Suboptimality
public import RothschildStein.G4.BracketReduction

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators

namespace RothschildStein.G4

/-- The two determinant conclusions of persistence give the
sharp nearby-point Cramer bound, including signed weight deficits
(BB (9.34), p. 436; constant depending only on the displayed data). -/
theorem frameCoefficient_le_of_determinant_bounds {ι : Type*} {n : ℕ}
    {Z : ι → (Fin n → ℝ) → (Fin n → ℝ)} (w : ι → ℕ+)
    (B : Fin n → ι) {x y : Fin n → ℝ} {r D : ℝ} (hr : 0 < r) (hD : 0 ≤ D)
    (hBx : frameDet Z B x ≠ 0)
    (hhalf : |frameDet Z B x| / 2 ≤ |frameDet Z B y|)
    (hdet : ∀ C : Fin n → ι, |frameDet Z C y| ≤
      D * r ^ (frameWeight w B - frameWeight w C) * |frameDet Z B x|)
    (J : ι) (i : Fin n) :
    |frameCoefficient Z B (Z J) i y| ≤
      2 * D * r ^ (((w (B i) : ℕ) : ℤ) - ((w J : ℕ) : ℤ)) := by
  have hbase : 0 < |frameDet Z B x| := abs_pos.mpr hBx
  have hypos : 0 < |frameDet Z B y| := (half_pos hbase).trans_le hhalf
  rw [frameCoefficient, abs_div, replacementDet_eq_update]
  apply (div_le_iff₀ hypos).mpr
  have hc := hdet (Function.update B i J)
  rw [frameWeight_sub_update] at hc
  have hm : 0 ≤ D * r ^ (((w (B i) : ℕ) : ℤ) - ((w J : ℕ) : ℤ)) :=
    mul_nonneg hD (zpow_nonneg hr.le _)
  calc
    _ ≤ (D * r ^ (((w (B i) : ℕ) : ℤ) - ((w J : ℕ) : ℤ))) * |frameDet Z B x| := hc
    _ ≤ (D * r ^ (((w (B i) : ℕ) : ℤ) - ((w J : ℕ) : ℤ))) * (2 * |frameDet Z B y|) :=
      mul_le_mul_of_nonneg_left (by linarith) hm
    _ = _ := by ring

/-- A finite reduction with weight support at most `W` combines
sharp single-factor bounds with no extra inverse-suboptimality powers
(BB Corollary 9.40, pp. 436–437, entire-bracket reduction). -/
theorem weighted_sum_scale_bound {ι : Type*} [Fintype ι]
    (w : ι → ℕ+) (c a : ι → ℝ) {r M D : ℝ} {v W : ℕ}
    (hr : 0 < r) (hr1 : r ≤ 1) (hD : 0 ≤ D)
    (hc : ∑ J, |c J| ≤ M) (hsupport : ∀ J, W < (w J : ℕ) → c J = 0)
    (ha : ∀ J, |a J| ≤ D * r ^ ((v : ℤ) - ((w J : ℕ) : ℤ))) :
    |∑ J, c J * a J| ≤ M * D * r ^ ((v : ℤ) - (W : ℤ)) := by
  have hterm : ∀ J, |c J * a J| ≤ |c J| * (D * r ^ ((v : ℤ) - (W : ℤ))) := by
    intro J
    by_cases hj : W < (w J : ℕ)
    · rw [hsupport J hj, zero_mul, abs_zero, zero_mul]
    · have hw : (w J : ℕ) ≤ W := le_of_not_gt hj
      have hp := zpow_le_zpow_right_of_le_one₀ hr hr1
        (show (v : ℤ) - (W : ℤ) ≤ (v : ℤ) - ((w J : ℕ) : ℤ) by
          have hwi : ((w J : ℕ) : ℤ) ≤ (W : ℤ) := by exact_mod_cast hw
          omega)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left ((ha J).trans (mul_le_mul_of_nonneg_left hp hD)) (abs_nonneg _)
  calc
    _ ≤ ∑ J, |c J * a J| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ J, |c J| * (D * r ^ ((v : ℤ) - (W : ℤ))) := Finset.sum_le_sum (fun J _ => hterm J)
    _ = (∑ J, |c J|) * (D * r ^ ((v : ℤ) - (W : ℤ))) := (Finset.sum_mul _ _ _).symm
    _ ≤ M * (D * r ^ ((v : ℤ) - (W : ℤ))) :=
      mul_le_mul_of_nonneg_right hc (mul_nonneg hD (zpow_nonneg hr.le _))
    _ = _ := by ring

/-- Pointwise quantitative consequence of the actual
bracket reduction and the two persistence determinant estimates.
The finite reduction norm is explicit; its uniform coefficient-jet control
requires uniform coefficient-jet bounds
(BB Corollary 9.40, pp. 436–437). -/
theorem binary_frameCoefficient_le_of_determinant_bounds {k n s : ℕ}
    {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) {w : Fin (k + 1) → ℕ+}
    {X : Fin (k + 1) → (Fin n → ℝ) → (Fin n → ℝ)}
    (hX : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (X j) Ω)
    (hstep : bracketStepOn Ω w X s) (t : Hormander.Interface.LieWord k)
    (B : Fin n → ShortWord w s) (i : Fin n) {x y : Fin n → ℝ} (hy : y ∈ Ω)
    {r M D : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hD : 0 ≤ D)
    (hc : ∑ J : ShortWord w s, |binaryReductionCoefficient w X t J y| ≤ M)
    (hBx : frameDet (shortField w X) B x ≠ 0)
    (hhalf : |frameDet (shortField w X) B x| / 2 ≤ |frameDet (shortField w X) B y|)
    (hdet : ∀ C : Fin n → ShortWord w s, |frameDet (shortField w X) C y| ≤
      D * r ^ (frameWeight (shortWeight w) B - frameWeight (shortWeight w) C) *
        |frameDet (shortField w X) B x|) :
    |frameCoefficient (shortField w X) B (Hormander.lieWordEval X t) i y| ≤
      M * (2 * D) * r ^ (((wordWeight w (B i).val : ℕ) : ℤ) - (G1.binaryWeight w t : ℤ)) := by
  rw [binary_frameCoefficient_representation hΩ hX hstep t B i hy]
  apply weighted_sum_scale_bound (shortWeight w) _ _ hr hr1 (by positivity) hc
  · intro J hJ
    exact congrFun (binaryReductionCoefficient_eq_zero_of_weight_lt w X t J hJ) y
  · intro J
    exact frameCoefficient_le_of_determinant_bounds (shortWeight w) B hr hD hBx hhalf hdet J i

end RothschildStein.G4
