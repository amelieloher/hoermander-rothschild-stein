-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.PolynomialSmoothTests
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.L1

/-- Bundling a polynomial sum is the sum of the actual smooth test functions. -/
theorem polynomialSmoothTest_add {N : ℕ} (Ω : Opens (Fin N → ℝ))
    (u v : MvPolynomial (Fin N) ℝ)
    (hu : ContDiff ℝ (⊤ : ℕ∞) (fun x => MvPolynomial.eval x u))
    (hv : ContDiff ℝ (⊤ : ℕ∞) (fun x => MvPolynomial.eval x v))
    (hsum : ContDiff ℝ (⊤ : ℕ∞) (fun x => MvPolynomial.eval x (u+v))) :
    polynomialSmoothTest Ω (u+v) hsum = polynomialSmoothTest Ω u hu + polynomialSmoothTest Ω v hv := by
  apply Subtype.ext
  funext x
  exact map_add (MvPolynomial.eval x) u v
end RothschildStein.L1
