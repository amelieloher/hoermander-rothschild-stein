-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.TransportedBracketJets
public import RothschildStein.G4.TransportedSmoothness
public import RothschildStein.G3.TaylorRemainder

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators

namespace RothschildStein.G4

open MeasureTheory

/-- Exact integral Taylor remainder for the actual transported field,
with the next iterated adjoint bracket in the integrand
(BB Lemma 9.48, pp. 442–443; NSW p. 127). -/
theorem localFlow_transported_taylor_integral
    {N : ℕ} {Ω U : Set (Fin N → ℝ)} (hΩ : IsOpen Ω) (hU : IsOpen U)
    (Z Y : (Fin N → ℝ) → (Fin N → ℝ))
    (hZ : ContDiffOn ℝ (⊤ : ℕ∞) Z Ω) (hY : ContDiffOn ℝ (⊤ : ℕ∞) Y Ω)
    {τ : ℝ} (hτ : 0 < τ) (Φ : ((Fin N → ℝ) × ℝ) → (Fin N → ℝ))
    (hc : ContinuousOn Φ (U ×ˢ Ioo (-τ) τ))
    (hΦ : ∀ x ∈ U, Φ (x, 0) = x ∧ ∀ v ∈ Ioo (-τ) τ,
      HasDerivAt (fun w => Φ (x, w)) (Z (Φ (x, v))) v ∧ Φ (x, v) ∈ Ω)
    {x : Fin N → ℝ} (hx : x ∈ U) {T : Set ℝ} (hT : IsOpen T)
    (hTτ : T ⊆ Ioo (-τ) τ) (hend : ∀ s ∈ T, Φ (x, -s) ∈ U)
    (n : ℕ) {t : ℝ} (hsegment : ∀ r ∈ Icc (0 : ℝ) 1, r * t ∈ T)
 :
    (fderiv ℝ (fun y => Φ (y, t)) (Φ (x, -t))) (Y (Φ (x, -t))) =
      (∑ k ∈ Finset.range (n + 1), ((-1 : ℝ) ^ k * t ^ k / (k.factorial : ℝ)) •
        (((VectorField.lieBracket ℝ Z)^[k] Y) x)) +
      (n.factorial : ℝ)⁻¹ • ∫ r in 0..1,
        ((1 - r) ^ n * t ^ (n + 1) * (-1 : ℝ) ^ (n + 1)) •
          (fderiv ℝ (fun y => Φ (y, r * t)) (Φ (x, -(r * t))))
            (((VectorField.lieBracket ℝ Z)^[n + 1] Y) (Φ (x, -(r * t)))) := by
  let P : ℝ → Fin N → ℝ := fun s =>
    (fderiv ℝ (fun y => Φ (y, s)) (Φ (x, -s))) (Y (Φ (x, -s)))
  have hP := localFlow_transported_contDiffOn hΩ hU Z Y hZ hY hτ Φ hc hΦ hx hTτ hend
  have h₀ : (0 : ℝ) ∈ T := by simpa using hsegment 0 (by norm_num)
  have hj : ∀ k, iteratedDeriv k P 0 = (-1 : ℝ) ^ k •
      (((VectorField.lieBracket ℝ Z)^[k] Y) x) := by
    intro k
    dsimp only [P]
    rw [localFlow_transported_iteratedDeriv hΩ hU Z Y hZ hY hτ Φ hc hΦ hx hT hTτ hend k h₀]
    simp only [neg_zero, (hΦ x hx).1,
      RothschildStein.G1.localFlow_fderiv_zero hU Φ (fun y hy => (hΦ y hy).1) hx,
      ContinuousLinearMap.id_apply]
  have he := map_add_eq_sum_add_integral_iteratedFDeriv (f := P) (x := (0 : ℝ))
    (y := t) (n := n) (fun r hr => by
      simpa only [zero_add, smul_eq_mul] using
        (hP.contDiffAt (hT.mem_nhds (hsegment r hr))).of_le (by simp))
  simp only [zero_add, iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, hj, smul_smul] at he
  have hi : (∫ r in (0 : ℝ)..1, ((1 - r) ^ n * t ^ (n + 1)) • iteratedDeriv (n + 1) P (r * t)) =
      ∫ r in (0 : ℝ)..1, ((1 - r) ^ n * t ^ (n + 1) * (-1 : ℝ) ^ (n + 1)) •
        (fderiv ℝ (fun y => Φ (y, r * t)) (Φ (x, -(r * t))))
          (((VectorField.lieBracket ℝ Z)^[n + 1] Y) (Φ (x, -(r * t)))) := by
    apply intervalIntegral.integral_congr
    intro r hr
    have hr' : r ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le zero_le_one] using hr
    dsimp only [P]
    rw [localFlow_transported_iteratedDeriv hΩ hU Z Y hZ hY hτ Φ hc hΦ hx hT hTτ hend
      (n + 1) (hsegment r hr')]
    simp only [smul_smul, mul_assoc]
  simp only [smul_eq_mul] at he
  rw [hi] at he
  simpa only [P, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using he

end RothschildStein.G4
