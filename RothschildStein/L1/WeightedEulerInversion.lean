-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.ScalarEulerJets
public import RothschildStein.L1.PrefixDerivative
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace Filter
open scoped BigOperators Topology
namespace RothschildStein.L1

/-- BB's bracket expression is the ordinary Euler derivative of the field. -/
theorem jetEulerOperator_eq_fderiv {N : ℕ}
    (R : (Fin N → ℝ) → (Fin N → ℝ)) (u : Fin N → ℝ) :
    jetEulerOperator R u = (2 : ℝ) • R u + fderiv ℝ R u u := by
  have hu : (∑ j : Fin N, u j • Pi.single j (1 : ℝ)) = u := by
    ext i
    simp [Pi.single_apply]
  simp only [jetEulerOperator, VectorField.lieBracket, fderiv_const_apply, zero_apply, sub_zero]
  congr 1
  simpa only [map_sum, map_smul] using congrArg (fderiv ℝ R u) hu

/-- The vector Euler operator remains smooth throughout the actual domain. -/
theorem jetEulerOperator_contDiffOn {N : ℕ} (Ω : Opens (Fin N → ℝ))
    (R : (Fin N → ℝ) → (Fin N → ℝ)) (hR : ContDiffOn ℝ (⊤ : ℕ∞) R Ω) :
    ContDiffOn ℝ (⊤ : ℕ∞) (jetEulerOperator R) Ω := by
  have he : jetEulerOperator R = fun u => (2 : ℝ) • R u + fderiv ℝ R u u :=
    funext (jetEulerOperator_eq_fderiv R)
  rw [he]
  have hc : ContDiffOn ℝ (⊤ : ℕ∞) (fun _ : Fin N → ℝ => (2 : ℝ)) Ω := contDiffOn_const
  exact (hc.smul hR).add
    ((hR.fderiv_of_isOpen Ω.isOpen (by simp)).clm_apply contDiffOn_id)

/-- Each actual field coefficient has the scalar Euler expression. -/
theorem jetEulerOperator_coordinate {N : ℕ} (R : (Fin N → ℝ) → (Fin N → ℝ))
    {u : Fin N → ℝ} (hR : DifferentiableAt ℝ R u) (j : Fin N) :
    jetEulerOperator R u j = scalarJetEuler (fun y => R y j) u := by
  rw [jetEulerOperator_eq_fderiv]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, scalarJetEuler, fieldDerivative, id_eq,
    fderiv_coordinate_apply R hR j]

/-- The vector Euler operator preserves exactly
all forbidden finite weighted jets. No analytic inversion is used. -/
theorem fieldJetVanishing_jetEulerOperator_iff {N p : ℕ} (Ω : Opens (Fin N → ℝ))
    (h0 : (0 : Fin N → ℝ) ∈ Ω) (ω : Fin N → ℕ) (a : ℝ)
    (R : (Fin N → ℝ) → (Fin N → ℝ)) (hR : ContDiffOn ℝ (⊤ : ℕ∞) R Ω) :
    fieldJetVanishing ω a p (jetEulerOperator R) ↔ fieldJetVanishing ω a p R := by
  have he (j : Fin N) (J : List (Fin N)) :
      rsPartial J (fun u => jetEulerOperator R u j) 0 =
        rsPartial J (scalarJetEuler (fun u => R u j)) 0 := by
    have hg : (fun u => jetEulerOperator R u j) =ᶠ[𝓝 (0 : Fin N → ℝ)]
        scalarJetEuler (fun u => R u j) :=
      Filter.Eventually.mono (Ω.isOpen.mem_nhds h0) (fun u hu =>
        jetEulerOperator_coordinate R
          ((hR.contDiffAt (Ω.isOpen.mem_nhds hu)).differentiableAt (by simp)) j)
    exact (rsPartial_eventuallyEq J hg).self_of_nhds
  constructor
  · intro h j
    apply (scalarJetVanishing_scalarJetEuler_iff Ω h0 ω (a + ω j)
      (fun u => R u j) (contDiffOn_pi.mp hR j)).mp
    intro J hJ hw
    rw [← he j J]
    exact h j J hJ hw
  · intro h j
    have hj := (scalarJetVanishing_scalarJetEuler_iff Ω h0 ω (a + ω j)
      (fun u => R u j) (contDiffOn_pi.mp hR j)).mpr (h j)
    intro J hJ hw
    rw [he j J]
    exact hj J hJ hw

/-- The full smooth finite-weight class is invariant under Euler inversion. -/
theorem fieldJetClass_jetEulerOperator_iff {N p : ℕ} (Ω : Opens (Fin N → ℝ))
    (h0 : (0 : Fin N → ℝ) ∈ Ω) (ω : Fin N → ℕ) (a : ℝ)
    (R : (Fin N → ℝ) → (Fin N → ℝ)) (hR : ContDiffOn ℝ (⊤ : ℕ∞) R Ω) :
    fieldJetClass Ω ω a p (jetEulerOperator R) ↔ fieldJetClass Ω ω a p R := by
  exact and_congr (iff_of_true (jetEulerOperator_contDiffOn Ω R hR) hR)
    (fieldJetVanishing_jetEulerOperator_iff Ω h0 ω a R hR)
end RothschildStein.L1
