-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.MixedFlowJets

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace RothschildStein.G1

/-- Subtracting the initial-point linear map costs only its
operator norm in every positive displacement jet (BB pp. 3–4). -/
theorem norm_smooth_displacement_positive_jet_le {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} {x : E} (hf : ContDiffAt ℝ (⊤ : ℕ∞) f x)
    (L : E →L[ℝ] F) (n : ℕ) (hn : 1 ≤ n) {C : ℝ}
    (hjet : ‖iteratedFDeriv ℝ n f x‖ ≤ C) :
    ‖iteratedFDeriv ℝ n (fun y => f y - L y) x‖ ≤ C + ‖L‖ := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_comm 1 k]
  rw [fun_iteratedFDeriv_sub_apply (hf.of_le (by simp))
    ((L.contDiff (n := k + 1)).contDiffAt)]
  have hj' : ‖iteratedFDeriv ℝ (k + 1) f x‖ ≤ C := by
    rw [Nat.add_comm k 1]
    exact hjet
  exact (norm_sub_le _ _).trans (add_le_add hj'
    (RothschildStein.G4.norm_positive_jet_clm_le L x k))

end RothschildStein.G1
