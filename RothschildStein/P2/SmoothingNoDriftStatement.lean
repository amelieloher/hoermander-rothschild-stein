-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.ParametrixKernelBoundsNoDriftSol
public import RothschildStein.Definitions.noDriftWeight
public import RothschildStein.Definitions.memHolderX
public import RothschildStein.Definitions.memSobolevX
public import RothschildStein.Definitions.hasWeakWordDeriv
public import RothschildStein.Definitions.hasIntrinsicWordDeriv

/-!
# Local solvability (statement), no drift

The no-drift counterpart of `RothschildStein.P2.LocalSolvability` (`SmoothingSolveEquation`): for the
operator `L = ∑ Xᵢ²` (alphabet `Fin q`, all weights one, `sumSquares`) and a lifted no-drift
chart `C : LiftedChart (fun _ : Fin q => 1) s Ω hΩ X x₀ m`.

* `weakNoDriftEquation V X v g` / `intrinsicNoDriftEquation V X v g`: the equation `L v = g`,
  `L = ∑ Xᵢ²`, for `v ∈ W^{2,p}` through the weak word derivatives `Xᵢ Xᵢ v` (a.e. on `V`),
  respectively for `v ∈ C^{2,α}` through the intrinsic word derivatives (pointwise on `V`), the
  form of the conclusion of the Hölder regularity theorem `rs3_no_drift_holder`.
* `LocalSolvabilityNoDrift C`: local solvability in the lifted no-drift chart:
  smoothing (BB pp. 605-608, Prop 11.61, (11.97)-(11.100)) in a lifted no-drift chart: for all
  sufficiently small balls `U_R = B̃(ξ₀, R)`, `g ∈ L^p(U_R)` has `v ∈ W^{2,p}_{X̃}(U_R)` with
  `L̃ v = g` a.e. and `g ∈ C^α_{X̃}(U_R)` has `v ∈ C^{2,α}_{X̃}(U_{R/2})` with `L̃ v = g` there.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped ENNReal NNReal Topology BigOperators Distributions
open RothschildStein.P1
namespace RothschildStein.P2

section Equations

variable {n q : ℕ}

/-- The weak no-drift equation `L v = g` on `V`, `L = ∑ Xᵢ²`: every `Xᵢ Xᵢ v` exists as a weak word
derivative on `V` and `∑ᵢ XᵢXᵢ v = g` almost everywhere on `V`. -/
def weakNoDriftEquation (V : Opens (Fin n → ℝ))
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)) (v g : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ gs : Fin q → (Fin n → ℝ) → ℝ,
    (∀ i : Fin q, hasWeakWordDeriv X V [i, i] v (gs i)) ∧
    ∀ᵐ x ∂(volume.restrict (V : Set (Fin n → ℝ))), (∑ i, gs i x) = g x

/-- The intrinsic no-drift equation `L v = g` on `V`: every `Xᵢ Xᵢ v` exists as an intrinsic
word derivative and `∑ᵢ XᵢXᵢ v = g` at every point of `V` (as in the no-drift Hölder regularity theorem). -/
def intrinsicNoDriftEquation (V : Opens (Fin n → ℝ))
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)) (v g : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ gs : Fin q → (Fin n → ℝ) → ℝ,
    (∀ i : Fin q, hasIntrinsicWordDeriv X V [i, i] v (gs i)) ∧
    ∀ x ∈ (V : Set (Fin n → ℝ)), (∑ i, gs i x) = g x

end Equations

section Statement

variable {n q s m : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}

/-- **Local solvability needed for smoothing, no drift** (BB pp. 605-608, Prop 11.61,
(11.97)-(11.100)), in a fixed lifted no-drift chart `C` (the statement of `LocalSolvability` with
`L = ∑ Xᵢ²`, `Fin q` fields of weight one). For every centre `ξ₀ ∈ U`:

* for `1 < p < ∞` there is `R₀ > 0` (depending only on the chart data and `p`) such that for every
  `0 < R < R₀`, on the open ball `U_R = B̃(ξ₀, R)` every `g ∈ L^p(U_R)` has a `v ∈ W^{2,p}_{X̃}(U_R)`
  (`memSobolevX`) with `L̃ v = g` almost everywhere (`weakNoDriftEquation`);
* for `0 < α < 1` there is `R₀ > 0` (depending only on the chart data and `α`) such that for every
  `0 < R < R₀`, every `g ∈ C^α_{X̃}(U_R)` (`memHolderX`, order `0`) has a
  `v ∈ C^{2,α}_{X̃}(U_{R/2})` (`memHolderX`, order `2`) with `L̃ v = g` on `U_{R/2}`
  (`intrinsicNoDriftEquation`).

The balls `U_R` are control balls of the lifted distance `d̃`; they are Euclidean open for small `R`,
and the statement quantifies over every open set `UR` equal to the ball. -/
def LocalSolvabilityNoDrift
    (C : P1.LiftedChart (fun _ : Fin q => (1 : ℕ+)) s Ω hΩ X x₀ m) : Prop :=
  ∀ ξ₀ ∈ C.U,
    (∀ p : ℝ≥0∞, 1 < p → p < ⊤ → ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, 0 < R → R < R₀ →
      ∀ UR : Opens (Fin (n + m) → ℝ), (UR : Set (Fin (n + m) → ℝ)) = C.noDriftBall ξ₀ R →
        ∀ g : (Fin (n + m) → ℝ) → ℝ, MemLp g p (volume.restrict (UR : Set (Fin (n + m) → ℝ))) →
          ∃ v : (Fin (n + m) → ℝ) → ℝ, memSobolevX noDriftWeight C.Xl UR 2 p v ∧
            weakNoDriftEquation UR C.Xl v g) ∧
    (∀ α : ℝ, 0 < α → α < 1 → ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, 0 < R → R < R₀ →
      ∀ UR UR' : Opens (Fin (n + m) → ℝ), (UR : Set (Fin (n + m) → ℝ)) = C.noDriftBall ξ₀ R →
        (UR' : Set (Fin (n + m) → ℝ)) = C.noDriftBall ξ₀ (R / 2) →
        ∀ g : (Fin (n + m) → ℝ) → ℝ, memHolderX noDriftWeight C.Xl C.dl UR 0 α g →
          ∃ v : (Fin (n + m) → ℝ) → ℝ, memHolderX noDriftWeight C.Xl C.dl UR' 2 α v ∧
            intrinsicNoDriftEquation UR' C.Xl v g)

end Statement

end RothschildStein.P2
