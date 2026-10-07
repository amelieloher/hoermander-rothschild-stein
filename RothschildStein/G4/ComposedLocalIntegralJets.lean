-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.LocalIntegralSmoothness

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace RothschildStein.G4

universe u

/-- Full jets of an actual local integral composed with a smooth
endpoint map are controlled by integrand jets and endpoint jets. The open
integration domain is derived from compactness (BB pp. 441–443). -/
theorem norm_composed_local_interval_integral_jet_le {E P F : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {U : Set E} {S : Set (P × ℝ)} (hU : IsOpen U) (hS : IsOpen S)
    (G : P × ℝ → F) (hG : ContDiffOn ℝ (⊤ : ℕ∞) G S)
    (Q : E → P) (hQ : ContDiffOn ℝ (⊤ : ℕ∞) Q U)
    {x : E} (hx : x ∈ U) (hsegment : ∀ t ∈ Icc (0 : ℝ) 1, (Q x, t) ∈ S)
    (n : ℕ) {M D : ℝ}
    (hjet : ∀ t ∈ Icc (0 : ℝ) 1, ∀ j ≤ n,
      ‖iteratedFDeriv ℝ j (fun y => G (y, t)) (Q x)‖ ≤ M)
    (hQjet : ∀ j, 1 ≤ j → j ≤ n → ‖iteratedFDeriv ℝ j Q x‖ ≤ D ^ j) :
    ‖iteratedFDeriv ℝ n (fun y => ∫ t in (0 : ℝ)..1, G (Q y, t)) x‖ ≤
      n.factorial * M * D ^ n := by
  let T : Set P := {y | ∀ t ∈ Icc (0 : ℝ) 1, (y, t) ∈ S}
  have hT : IsOpen T := isOpen_parameter_segment_domain hS
  let V : Set E := U ∩ Q ⁻¹' T
  have hV : IsOpen V := hQ.continuousOn.isOpen_inter_preimage hU hT
  have hxV : x ∈ V := ⟨hx, hsegment⟩
  let f : P → F := fun y => ∫ t in (0 : ℝ)..1, G (y, t)
  have hf : ContDiffOn ℝ (⊤ : ℕ∞) f T :=
    local_interval_parameter_integral_contDiffOn hS G hG
  have hh := norm_iteratedFDerivWithin_comp_le hf (hQ.mono inter_subset_left)
    (n := n) (by simp) hT.uniqueDiffOn hV.uniqueDiffOn
    (fun y hy => hy.2) hxV (C := M) (D := D)
    (fun j hj => by
      rw [iteratedFDerivWithin_of_isOpen _ hT hsegment]
      exact norm_local_interval_integral_jet_le hS G hG (Q x) hsegment j
        (fun t ht => hjet t ht j hj))
    (fun j hj hjn => by
      rw [iteratedFDerivWithin_of_isOpen _ hV hxV]
      exact hQjet j hj hjn)
  change ‖iteratedFDerivWithin ℝ n (f ∘ Q) V x‖ ≤ _ at hh
  rw [iteratedFDerivWithin_of_isOpen _ hV hxV] at hh
  simpa only [Function.comp_def, f] using hh

end RothschildStein.G4
