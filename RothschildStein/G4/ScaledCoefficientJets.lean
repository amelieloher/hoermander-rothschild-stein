-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.AffineJetBounds

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace RothschildStein.G4

/-- Every joint parameter/initial-point jet of a coefficient scaled
by the base coefficient norm is bounded by that norm at the base point
(BB Lemma 9.48, pp. 441–443). -/
theorem norm_scaled_coefficient_jet_le {m : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (z : Fin m → ℝ) (i : Fin m) (x : E) (k : ℕ) :
    ‖iteratedFDeriv ℝ k (fun p : (Fin m → ℝ) × E => z i + ‖z‖ * p.1 i)
      (0, x)‖ ≤ ‖z‖ := by
  let L : ((Fin m → ℝ) × E) →L[ℝ] ℝ :=
    ‖z‖ • ((ContinuousLinearMap.proj i).comp (ContinuousLinearMap.fst ℝ _ _))
  have hL : ‖L‖ ≤ ‖z‖ := by
    apply ContinuousLinearMap.opNorm_le_bound L (norm_nonneg z)
    intro p
    change ‖‖z‖ * p.1 i‖ ≤ ‖z‖ * ‖p‖
    rw [norm_mul, norm_norm]
    exact mul_le_mul_of_nonneg_left
      ((norm_le_pi_norm p.1 i).trans (norm_fst_le p)) (norm_nonneg z)
  have hv : ‖z i + L (0, x)‖ ≤ ‖z‖ := by
    simpa [L] using norm_le_pi_norm z i
  exact norm_affine_jet_le L (z i) (0, x) k hv hL

/-- The scaled coefficient family is jointly smooth on parameter
and initial-point space (BB Lemma 9.48, pp. 441–443). -/
theorem scaled_coefficient_contDiff {m : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (z : Fin m → ℝ) (i : Fin m) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun p : (Fin m → ℝ) × E => z i + ‖z‖ * p.1 i) := by
  exact contDiff_const.add (contDiff_const.mul ((contDiff_apply ℝ ℝ i).comp contDiff_fst))

end RothschildStein.G4
