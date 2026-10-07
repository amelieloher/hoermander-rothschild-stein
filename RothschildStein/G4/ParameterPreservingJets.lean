-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.AffineJetBounds

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace RothschildStein.G4

/-- Appending stationary parameters to a map preserves every
positive full jet bound at least one in the product norm
(BB Lemma 9.48, pp. 441–443). -/
theorem norm_parameter_preserving_map_jet_le {P E : Type*} {n : ℕ}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : P × E → E} {p : P × E} (hF : ContDiffAt ℝ (⊤ : ℕ∞) F p)
    (hn : 1 ≤ n) {M : ℝ} (hM : 1 ≤ M)
    (hjet : ‖iteratedFDeriv ℝ n F p‖ ≤ M) :
    ‖iteratedFDeriv ℝ n (fun q => (q.1, F q)) p‖ ≤ M := by
  rw [iteratedFDeriv_prodMk (contDiffAt_fst (n := (⊤ : ℕ∞))) hF (by simp),
    ContinuousMultilinearMap.opNorm_prod]
  apply max_le _ hjet
  cases n with
  | zero => omega
  | succ k =>
    exact (norm_positive_jet_clm_le (ContinuousLinearMap.fst ℝ P E) p k).trans
      ((ContinuousLinearMap.norm_fst_le ℝ P E).trans hM)

end RothschildStein.G4
