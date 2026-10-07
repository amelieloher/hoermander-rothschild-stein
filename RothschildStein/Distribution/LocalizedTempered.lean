-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.Distribution.SchwartzComplexification
public import RothschildStein.Distribution.SobolevDuality
public import RothschildStein.S.SchwartzLocalization
public import Hormander.F.SchwartzTransport

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace SchwartzMap
open scoped CompactConvergenceCLM
namespace RothschildStein.Distribution
variable {N : ℕ}

/-- localize a distribution on real tests first,
then complexify the resulting continuous Schwartz functional. -/
def localizedTempered (U : Opens (Fin N → ℝ))
    (χ : TestFunction U ℝ (⊤ : ℕ∞)) (T : Distribution U ℂ (⊤ : ℕ∞)) :
    TemperedDistribution (Fin N → ℝ) ℂ :=
  complexifySchwartzFunctional (T.comp (S.schwartzCutoffTestCLM U χ))

/-- the actual localized complex distribution
pairs with the real and imaginary cutoff tests. -/
theorem localizedTempered_apply (U : Opens (Fin N → ℝ))
    (χ : TestFunction U ℝ (⊤ : ℕ∞)) (T : Distribution U ℂ (⊤ : ℕ∞))
    (φ : SchwartzMap (Fin N → ℝ) ℂ) :
    localizedTempered U χ T φ =
      T (S.schwartzCutoffTestCLM U χ (SchwartzMap.postcompCLM Complex.reCLM φ)) +
        Complex.I * T (S.schwartzCutoffTestCLM U χ (SchwartzMap.postcompCLM Complex.imCLM φ)) := rfl

/-- the localized distribution on
the existing Euclidean Fourier carrier, reusing F's transport. -/
def localizedTemperedEuclidean (U : Opens (Fin N → ℝ))
    (χ : TestFunction U ℝ (⊤ : ℕ∞)) (T : Distribution U ℂ (⊤ : ℕ∞)) :
    TemperedDistribution (Hormander.A.Carrier N) ℂ :=
  Hormander.F.temperedToEuclideanCLM N (localizedTempered U χ T)

end RothschildStein.Distribution
