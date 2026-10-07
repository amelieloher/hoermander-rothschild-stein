-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.ParameterJetBounds
public import RothschildStein.G1.SmoothDependenceMain

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace RothschildStein.G4

/-- Positive jets of a continuous linear map are bounded by its
operator norm, including all higher zero jets (BB pp. 441–443). -/
theorem norm_positive_jet_clm_le {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (x : E) (k : ℕ) :
    ‖iteratedFDeriv ℝ (k + 1) L x‖ ≤ ‖L‖ := by
  have hh := L.norm_iteratedFDeriv_comp_left (f := (id : E → E)) (x := x)
    (contDiffAt_id (n := (⊤ : ℕ∞))) (n := k + 1) (by simp)
  simpa only [Function.comp_def, id_eq, mul_one] using
    hh.trans (mul_le_mul_of_nonneg_left (RothschildStein.G1.norm_iteratedFDeriv_id_le k x)
      (norm_nonneg L))

/-- Affine coefficient functions have a common bound on every jet
from their value and linear-part norm (BB pp. 441–443). -/
theorem norm_affine_jet_le {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L : E →L[ℝ] F) (c : F) (x : E) (k : ℕ) {C : ℝ}
    (hvalue : ‖c + L x‖ ≤ C) (hL : ‖L‖ ≤ C) :
    ‖iteratedFDeriv ℝ k (fun y => c + L y) x‖ ≤ C := by
  cases k with
  | zero => simpa only [norm_iteratedFDeriv_zero] using hvalue
  | succ k =>
    rw [fun_iteratedFDeriv_add_apply contDiffAt_const ((L.contDiff (n := k + 1)).contDiffAt),
      iteratedFDeriv_succ_const, Pi.zero_apply, zero_add]
    exact (norm_positive_jet_clm_le L x k).trans hL

end RothschildStein.G4
