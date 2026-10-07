-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.WeightedEulerInversion
public import RothschildStein.L1.WeightedFieldLinear
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace Filter
open scoped Topology BigOperators
namespace RothschildStein.L1

/-- The ordinary Euler operator with constant coefficient one. -/
def unitJetEulerOperator {N : ℕ} (R : (Fin N → ℝ) → (Fin N → ℝ))
    (u : Fin N → ℝ) : Fin N → ℝ :=
  R u + ∑ k, u k • VectorField.lieBracket ℝ (fun _ => Pi.single k 1) R u

/-- The coefficient-one operator is the coefficient-two operator minus
one copy of the original field. -/
theorem unitJetEulerOperator_eq_sub {N : ℕ}
    (R : (Fin N → ℝ) → (Fin N → ℝ)) :
    unitJetEulerOperator R = fun u => jetEulerOperator R u - R u := by
  funext u
  simp only [unitJetEulerOperator,jetEulerOperator,two_smul]
  abel

/-- Each ordinary jet is multiplied by one plus its degree, so the
coefficient-one Euler operator preserves the finite weight filtration. -/
theorem fieldJetClass_unitJetEulerOperator_iff {N q : ℕ}
    (Ω : Opens (Fin N → ℝ)) (h0 : (0 : Fin N → ℝ) ∈ Ω)
    (ω : Fin N → ℕ) (a : ℝ) (R : (Fin N → ℝ) → (Fin N → ℝ))
    (hR : ContDiffOn ℝ (⊤ : ℕ∞) R Ω) :
    fieldJetClass Ω ω a q (unitJetEulerOperator R) ↔ fieldJetClass Ω ω a q R := by
  have hU : ContDiffOn ℝ (⊤ : ℕ∞) (unitJetEulerOperator R) Ω := by
    rw [unitJetEulerOperator_eq_sub]
    exact (jetEulerOperator_contDiffOn Ω R hR).sub hR
  have he (k : Fin N) (J : List (Fin N)) :
      rsPartial J (fun u => unitJetEulerOperator R u k) 0 =
        (1 + (J.length : ℝ)) * rsPartial J (fun u => R u k) 0 := by
    let f := fun u => R u k
    have hf : ContDiffOn ℝ (⊤ : ℕ∞) f Ω := contDiffOn_pi.mp hR k
    have hg : (fun u => unitJetEulerOperator R u k) =ᶠ[𝓝 (0 : Fin N → ℝ)]
        (fun u => scalarJetEuler f u + -f u) :=
      Filter.Eventually.mono (Ω.isOpen.mem_nhds h0) (fun u hu => by
        rw [unitJetEulerOperator_eq_sub]
        change jetEulerOperator R u k - R u k = _
        rw [jetEulerOperator_coordinate R
          ((hR.contDiffAt (Ω.isOpen.mem_nhds hu)).differentiableAt (by simp)) k]
        rfl)
    rw [(rsPartial_eventuallyEq J hg).self_of_nhds,
      rsPartial_add_on Ω (scalarJetEuler f) (fun u => -f u)
        (scalarJetEuler_contDiffOn Ω f hf) hf.neg J h0,rsPartial_neg]
    rw [rsPartial_scalarJetEuler_zero Ω h0 f hf J]
    change (2 + (J.length : ℝ)) * rsPartial J f 0 + -rsPartial J f 0 = _
    ring
  constructor
  · intro h
    refine ⟨hR, ?_⟩
    intro k J hJ hw
    have hh := h.2 k J hJ hw
    rw [he k J] at hh
    exact (mul_eq_zero.mp hh).resolve_left (by positivity)
  · intro h
    refine ⟨hU, ?_⟩
    intro k J hJ hw
    rw [he k J,h.2 k J hJ hw,mul_zero]
end RothschildStein.L1
