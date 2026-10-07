-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.ParameterStateJetLift
public import RothschildStein.G4.AffineJetBounds
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace RothschildStein.G3

/-- Translation of the output does not change positive jets of the update. -/
theorem norm_parameterStateLift_positive_jet_le {A P : Type*}
    [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    (x : P) (f : A × P → P) (q : A × P) {n : ℕ} (hn : 1 ≤ n)
    (hf : ContDiffAt ℝ n f q) {B : ℝ} (hB : 1 ≤ B)
    (hjet : ‖iteratedFDeriv ℝ n f q‖ ≤ B) :
    ‖iteratedFDeriv ℝ n (parameterStateLift x f) q‖ ≤ B := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_comm 1 k] at hf hjet ⊢
  unfold parameterStateLift
  rw [iteratedFDeriv_prodMk contDiffAt_fst (hf.sub contDiffAt_const) le_rfl,
    ContinuousMultilinearMap.opNorm_prod]
  apply max_le
  · exact ((G4.norm_positive_jet_clm_le (ContinuousLinearMap.fst ℝ A P) q k).trans
      (ContinuousLinearMap.norm_fst_le ℝ A P)).trans hB
  · rw [fun_iteratedFDeriv_sub_apply hf contDiffAt_const,
      iteratedFDeriv_succ_const,Pi.zero_apply,sub_zero]
    exact hjet
end RothschildStein.G3
