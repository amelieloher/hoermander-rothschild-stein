-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.CompactAmbientJets
public import RothschildStein.G3.ModelProduct
public import RothschildStein.G3.ModelWords
public import RothschildStein.G3.LinearWordPolynomials
public import RothschildStein.G3.ExponentialFlowMaps
public import RothschildStein.G4.AffineJetBounds
@[expose] public section
noncomputable section
namespace RothschildStein.G3

/-- Fixing the initial state adds no positive parameter jet. -/
theorem norm_fixed_state_parameter_jet_le {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {f : E → F} {z : E} (hf : ContDiffAt ℝ (⊤ : ℕ∞) f z)
    (x : G) {n : ℕ} (hn : 1 ≤ n) {A : ℝ} (hA : 0 ≤ A)
    (hjet : ‖iteratedFDeriv ℝ n f z‖ ≤ A) :
    ‖iteratedFDeriv ℝ n (fun w => (f w,x)) z‖ ≤ A := by
  rw [iteratedFDeriv_prodMk hf (contDiffAt_const (n := (⊤ : ℕ∞))) (by simp),
    ContinuousMultilinearMap.opNorm_prod]
  apply max_le hjet
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_comm 1 k,iteratedFDeriv_succ_const]
  simpa only [Pi.zero_apply,norm_zero] using hA
end RothschildStein.G3
