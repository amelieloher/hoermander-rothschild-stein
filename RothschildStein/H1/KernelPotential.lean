-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.KernelData

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
namespace RothschildStein.H1
variable {N q : ℕ} {G : HomogeneousGroup N} {H : StandingHypotheses G q}

/-- Smoothness of the potential in the potential notation
(BB Theorem 6.20(3), printed pp. 269–270). -/
theorem FundamentalKernel.potential_smooth (K : FundamentalKernel G H)
    (φ : TestFunction (⊤ : Opens (Fin N → ℝ)) ℝ (⊤ : ℕ∞)) :
    ContDiff ℝ (⊤ : ℕ∞) (G.potential K φ) := by
  have he : G.potential K φ = (fun x => ∫ y, K (G.mul (G.inv y) x) * φ y) := by
    funext x
    simp only [HomogeneousGroup.potential, mul_comm]
  rw [he]
  exact contDiff_fundamentalPotential G K.locallyIntegrable φ.contDiff φ.hasCompactSupport

/-- The potential is a right inverse, pointwise
(BB Theorem 6.20(3), printed p. 271). -/
theorem FundamentalKernel.potential_equation (K : FundamentalKernel G H)
    (φ : TestFunction (⊤ : Opens (Fin N → ℝ)) ℝ (⊤ : ℕ∞)) :
    sumSquaresWithDrift H.fields (G.potential K φ) = φ := by
  have he : G.potential K φ = (fun x => ∫ y, K (G.mul (G.inv y) x) * φ y) := by
    funext x
    simp only [HomogeneousGroup.potential, mul_comm]
  rw [he]
  exact H.fundamentalPotential_equation G K.locallyIntegrable K.fundamental φ.contDiff φ.hasCompactSupport

/-- Equation (11.2): the potential is a left inverse,
with absolute convergence of the integral (BB printed p. 539). -/
theorem FundamentalKernel.potential_twoSided (K : FundamentalKernel G H)
    (hQ : 2 < (G.homogeneousDimension : ℝ))
    (φ : TestFunction (⊤ : Opens (Fin N → ℝ)) ℝ (⊤ : ℕ∞)) (x : Fin N → ℝ) :
    Integrable (fun y => sumSquaresWithDrift H.fields φ y * K (G.mul (G.inv y) x)) ∧
    φ x = G.potential K (sumSquaresWithDrift H.fields φ) x := by
  let ψ := sumSquaresTest ⊤ H.fields (fun i => (H.fields_smooth G i).contDiffOn) φ
  have he : (ψ : (Fin N → ℝ) → ℝ) = sumSquaresWithDrift H.fields φ :=
    funext (sumSquaresTest_apply ⊤ H.fields (fun i => (H.fields_smooth G i).contDiffOn) φ)
  have hi := integrable_fundamentalPotential_second G K.locallyIntegrable
    (he ▸ ψ.contDiff.continuous) (he ▸ ψ.hasCompactSupport) x
  have hx := H.fundamental_twoSidedInverse G hQ K.locallyIntegrable K.smooth_off_zero
    K.homogeneous K.fundamental φ.contDiff φ.hasCompactSupport x
  constructor
  · simpa only [mul_comm] using hi
  · simpa only [HomogeneousGroup.potential, mul_comm] using hx.symm

end RothschildStein.H1
