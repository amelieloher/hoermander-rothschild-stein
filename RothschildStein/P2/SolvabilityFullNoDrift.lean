-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.SolvabilityFullNoDriftHolder

/-!
# Local solvability without drift: `LocalSolvabilityNoDrift C` under the `LeftDifferentiation` hypothesis

Entry point for the `SolvabilityFullNoDrift*` modules. For a lifted no-drift chart `C` with the H1
fundamental kernel `Γ = K` of its no-drift model (and the frame data: symmetric smooth gauge, the H1 properties of `K`), the
statement `LocalSolvabilityNoDrift C` of local solvability (BB pp. 605-608, Prop 11.61), `L = ∑ Xᵢ²`, follows
from `LeftDifferentiation` for the standard frames of the chart
(`LeftDifferentiationOnStandardFramesNoDrift`):

* `localSolvability_lp_noDrift_of_leftDifferentiation` (`SolvabilityFullNoDriftSobolev`): for `1 < p < ∞`,
  `g ∈ L^p(U_R)` gives `v = P_R E_R f ∈ W^{2,p}_{X̃}(U_R)` with `L̃ v = g` a.e.;
* `rightParametrix_holder_interior_gain_noDrift` (`SolvabilityFullNoDriftHolder`):
  `P_R E_R f ∈ C^{2,α}_{X̃}(U_{R/2})` for Hölder `f`;
* `localSolvability_holder_noDrift_of_leftDifferentiation`: `g ∈ C^α_{X̃}(U_R)` gives
  `v ∈ C^{2,α}_{X̃}(U_{R/2})` with `L̃ v = g` at every point of `U_{R/2}`;
* `localSolvabilityNoDrift_of_leftDifferentiation`: both together, the statement `LocalSolvabilityNoDrift C`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped ENNReal NNReal Topology BigOperators Distributions
open RothschildStein.P1
namespace RothschildStein.P2

section Full

variable {n q s m : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : P1.LiftedChart (fun _ : Fin q => (1 : ℕ+)) s Ω hΩ X x₀ m}
  {hq : 0 < q} {ν₀ : G2.HomogeneousNorm C.G}
  (K : H1.FundamentalKernel C.G (C.noDriftModel hq ν₀))
  (hQ : 2 < (C.G.homogeneousDimension : ℝ))

/-- **Local solvability needed for smoothing, no drift, under the `LeftDifferentiation` hypothesis** (BB
pp. 605-608, Prop 11.61, (11.97)-(11.100)): the exact statement `LocalSolvabilityNoDrift C` for a lifted
no-drift chart `C` with the H1 kernel `Γ = K` of the no-drift model, a symmetric smooth gauge, the H1 properties of `K`
and `LeftDifferentiation` (left differentiation of type-`λ` operators) for the standard frames of the chart. -/
theorem localSolvabilityNoDrift_of_leftDifferentiation
    (hsymm : ∀ u, (C.noDriftModel hq ν₀).norm (-u) = (C.noDriftModel hq ν₀).norm u)
    (hsmooth : (C.noDriftModel hq ν₀).norm.Smooth) (hprops : H1.FundamentalKernelProperties K)
    (hLeftDiff : LeftDifferentiationOnStandardFramesNoDrift C K hQ) : LocalSolvabilityNoDrift C :=
  fun _ hξ₀ =>
    ⟨fun _ hp hpt => localSolvability_lp_noDrift_of_leftDifferentiation K hQ hsymm hsmooth hprops hLeftDiff hξ₀ hp hpt,
      fun _ hα hα1 => localSolvability_holder_noDrift_of_leftDifferentiation K hQ hsymm hsmooth hprops hLeftDiff hξ₀ hα hα1⟩

end Full

end RothschildStein.P2
