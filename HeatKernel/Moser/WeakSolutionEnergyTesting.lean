-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.WeakSolutionScalarTests
public import HeatKernel.Moser.NonlinearAveragePairingLimits
public import HeatKernel.Form.PiecewiseEnergyComposition
public import HeatKernel.Form.ZeroBoundaryCompositionRepresentatives
public import HeatKernel.Bridge.ZeroBoundaryWeakCutoffTimeIdentity

/-! # Nonlinear tests of compatible zero-boundary energy curves -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped Topology NNReal
namespace HeatKernel

/-- A scalar test acts on the same zero-boundary graph as the positive spatial flux. -/
def WeakSolutionScalarTest.energyMap (T : WeakSolutionScalarTest) {N q : ℕ}
    (V : Opens (Fin N → ℝ)) (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) (z : zeroBoundaryGraph V X) : zeroBoundaryGraph V X :=
  ⟨piecewiseEnergyComposition X hX T.lipschitz T.map_zero
      T.exceptional T.countable_exceptional T.contDiffAt (zeroBoundaryEnergyInclusion V X z), by
    apply mem_zeroBoundaryGraph_of_lipschitz_composition V X hX
      (zeroBoundaryEnergyInclusion V X z) _ z.property T.lipschitz T.map_zero
    exact piecewiseEnergyComposition_fst_ae X hX T.lipschitz T.map_zero
      T.exceptional T.countable_exceptional T.contDiffAt _⟩

/-- The nonlinear test map is continuous in the full zero-boundary energy norm. -/
theorem WeakSolutionScalarTest.continuous_energyMap (T : WeakSolutionScalarTest) {N q : ℕ}
    (V : Opens (Fin N → ℝ)) (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) : Continuous (T.energyMap V X hX) :=
  ((continuous_piecewiseEnergyComposition X hX T.lipschitz T.map_zero
    T.exceptional T.countable_exceptional T.contDiffAt).comp
    (zeroBoundaryEnergyInclusion V X).continuous).subtype_val.subtype_mk _

/-- The scalar Lipschitz constant bounds the full zero-boundary test norm. -/
theorem WeakSolutionScalarTest.norm_energyMap_le (T : WeakSolutionScalarTest) {N q : ℕ}
    (V : Opens (Fin N → ℝ)) (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) (z : zeroBoundaryGraph V X) :
    ‖T.energyMap V X hX z‖ ≤ (T.bound : ℝ) * ‖z‖ :=
  norm_piecewiseEnergyComposition_le X hX T.lipschitz T.map_zero
    T.exceptional T.countable_exceptional T.contDiffAt (zeroBoundaryEnergyInclusion V X z)

end HeatKernel
