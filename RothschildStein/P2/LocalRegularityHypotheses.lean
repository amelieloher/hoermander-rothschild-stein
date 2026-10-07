-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.LocalRegularityLiftStatement
public import RothschildStein.P2.SolvabilityFullSobolev
public import RothschildStein.P2.SolvabilityFullNoDriftSobolev
public import RothschildStein.P2.TransferCover
public import RothschildStein.P2.SmoothingTheoremCover
public import RothschildStein.P2.SmoothingNoDriftCover

/-!
# Local regularity assembly: the operator and geometric hypotheses

The four local regularity roots (`rs3_no_drift_sobolev`, `rs3_no_drift_holder`, `rs3_drift_sobolev`,
`rs3_drift_holder`) are assembled in `LocalRegularityRoot*` from the hypotheses below,
expressed as hypotheses for the assembly theorems.

* `LiftApproximationDriftStatement`, `LiftApproximationNoDriftStatement` (`LocalRegularityLiftStatement`): the lifting statements.
* `LeftDifferentiationAllChartsDrift`, `LeftDifferentiationAllChartsNoDrift`: the hypothesis `LeftDifferentiation` (left
  differentiation of type-`λ` operators) for every standard frame of every lifted chart of a system
  with `3 ≤ n` (and `0 < q`, as in the statements; the padded system has
  `n ≥ 3`, so the model has `Q ≥ n ≥ 3`, the homogeneous-dimension condition,
  `LiftedChart.two_lt_homogeneousDimension`), with every H1 fundamental kernel `K` of the model
  (`LeftDifferentiationOnStandardFrames`). The local solvability theorem is *not* a hypothesis: `LocalSolvabilityAllChartsDrift`,
  `LocalSolvabilityAllChartsNoDrift` (`LocalSolvability`/`LocalSolvabilityNoDrift` for every chart) follow from
  these through `localSolvability_of_leftDifferentiation`, `localSolvabilityNoDrift_of_leftDifferentiation`
  (`localSolvabilityAllChartsDrift_of_leftDifferentiation`, `localSolvabilityAllChartsNoDrift_of_leftDifferentiation` in `LocalRegularitySolvability`).
* `LocalDoublingAllChartsDrift`, `LocalDoublingAllChartsNoDrift` (local doubling): `OriginalLocalDoubling` on the projected
  neighborhood of every lifted chart (`3 ≤ n`; the fields smooth on `Ω` with the rank condition; the
  single doubling interface).
* `LiftedBaseSobolevAllChartsDrift` and `LiftedBaseHolderAllChartsDrift`: the lifted base estimates
  (`LiftedBaseSobolevEstimate`, `LiftedBaseHolderEstimate`) at the smooth homogeneous norm of every
  drift chart (`3 ≤ n`).
* `HigherSobolevRegularityNoDrift` and `HigherHolderRegularityNoDrift`: higher regularity without drift on the
  original domain, `Ω' ⋐ Ω'' ⋐ Ω` (`3 ≤ n`).

`DriftSobolevHypotheses`, `DriftHolderHypotheses`, `NoDriftSobolevHypotheses`,
`NoDriftHolderHypotheses` are the hypothesis bundles of the four roots.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped ENNReal NNReal Topology BigOperators
open RothschildStein.P1
namespace RothschildStein.P2

/-- The hypothesis `LeftDifferentiation` (left differentiation of type-`λ` operators; BB
Prop 11.14 left half) for every standard frame of every lifted drift chart over a system with
`3 ≤ n` and `0 < q`, with every H1 fundamental kernel `K` of the drift model of the chart at the
smooth homogeneous norm of the chart group (`LeftDifferentiationOnStandardFrames`). By
`localSolvability_of_leftDifferentiation` it is all that the local solvability theorem needs. -/
def LeftDifferentiationAllChartsDrift : Prop :=
  ∀ {n q s m : ℕ} (hn : 3 ≤ n) (hq : 0 < q) {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
    {X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
    (C : P1.LiftedChart driftWeight s Ω hΩ X x₀ m)
    (K : H1.FundamentalKernel C.G (C.driftModel hq (G2.smoothNorm C.G))),
    LeftDifferentiationOnStandardFrames C K (C.two_lt_homogeneousDimension hn)

/-- The hypothesis `LeftDifferentiation` for every standard frame of every lifted no-drift
chart over a system with `3 ≤ n` (`q` arbitrary; the no-drift model needs `0 < q` as a chart
alphabet), with every H1 fundamental kernel `K` of the no-drift model of the chart at the smooth
homogeneous norm of the chart group (`LeftDifferentiationOnStandardFramesNoDrift`). -/
def LeftDifferentiationAllChartsNoDrift : Prop :=
  ∀ {n q s m : ℕ} (hn : 3 ≤ n) (hq : 0 < q) {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
    {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
    (C : P1.LiftedChart noDriftWeight s Ω hΩ X x₀ m)
    (K : H1.FundamentalKernel C.G (C.noDriftModel hq (G2.smoothNorm C.G))),
    LeftDifferentiationOnStandardFramesNoDrift C K (C.two_lt_homogeneousDimension hn)

/-- Local solvability for smoothing with drift (BB pp. 605-608, Prop 11.61) in every lifted
drift chart over a system with `3 ≤ n` and `0 < q` (a drift letter and at least one diffusion): `LocalSolvability C`
for every chart `C`. This is *derived* (`localSolvabilityAllChartsDrift_of_leftDifferentiation`), not a hypothesis of
the roots. -/
def LocalSolvabilityAllChartsDrift : Prop :=
  ∀ {n q s m : ℕ}, 3 ≤ n → 0 < q → ∀ {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
    {X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
    (C : P1.LiftedChart driftWeight s Ω hΩ X x₀ m), LocalSolvability C

/-- Local solvability for smoothing without drift (BB pp. 605-608, Prop 11.61) in every
lifted no-drift chart over a system with `3 ≤ n` (and `0 < q`): `LocalSolvabilityNoDrift C` for every
chart `C`. Derived (`localSolvabilityAllChartsNoDrift_of_leftDifferentiation`), not a hypothesis of the roots. -/
def LocalSolvabilityAllChartsNoDrift : Prop :=
  ∀ {n q s m : ℕ}, 3 ≤ n → 0 < q → ∀ {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
    {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
    (C : P1.LiftedChart noDriftWeight s Ω hΩ X x₀ m), LocalSolvabilityNoDrift C

/-- The original compact-centre local doubling on the projected neighborhood `π(U)` of every
lifted drift chart over a system with `3 ≤ n` and `0 < q` whose fields are smooth on `Ω` and satisfy
the rank condition on `Ω` (BB pp. 400, 405, Thms 9.1, 9.12). This is the single doubling interface. -/
def LocalDoublingAllChartsDrift : Prop :=
  ∀ {n q s m : ℕ}, 3 ≤ n → 0 < q → ∀ {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
    {X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ},
    (∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω) → bracketSpansOn Ω X →
    ∀ (C : P1.LiftedChart driftWeight s Ω hΩ X x₀ m),
    OriginalLocalDoubling Ω driftWeight X (basePoint '' C.U)

/-- The original compact-centre local doubling on the projected neighborhood `π(U)` of every
lifted no-drift chart over a system with `3 ≤ n` whose fields are smooth on `Ω` and satisfy the rank
condition on `Ω` (BB pp. 400, 405, Thms 9.1, 9.12). This is the single doubling interface. -/
def LocalDoublingAllChartsNoDrift : Prop :=
  ∀ {n q s m : ℕ}, 3 ≤ n → ∀ {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
    {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ},
    (∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω) → bracketSpansOn Ω X →
    ∀ (C : P1.LiftedChart noDriftWeight s Ω hΩ X x₀ m),
    OriginalLocalDoubling Ω noDriftWeight X (basePoint '' C.U)

/-- The lifted base Sobolev estimate, drift allowed (BB pp. 585-587, Thms 11.42-11.43,
(11.69)-(11.72)): for every lifted drift chart over a system with `3 ≤ n`, `0 < q` and every `1 < p < ∞`,
`LiftedBaseSobolevEstimate` at the smooth homogeneous norm of the chart group. -/
def LiftedBaseSobolevAllChartsDrift : Prop :=
  ∀ {n q s m : ℕ}, 3 ≤ n → 0 < q → ∀ {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
    {X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
    (C : P1.LiftedChart driftWeight s Ω hΩ X x₀ m) {p : ℝ≥0∞}, 1 < p → p < ⊤ →
    LiftedBaseSobolevEstimate C (G2.smoothNorm C.G) (driftOpWords q) p

/-- The lifted base Hölder estimate, drift allowed (BB pp. 600-602, Thms 11.57-11.58,
(11.92)-(11.93)): for every lifted drift chart over a system with `3 ≤ n`, `0 < q` and every `0 < α < 1`,
`LiftedBaseHolderEstimate` at the smooth homogeneous norm of the chart group. -/
def LiftedBaseHolderAllChartsDrift : Prop :=
  ∀ {n q s m : ℕ}, 3 ≤ n → 0 < q → ∀ {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
    {X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
    (C : P1.LiftedChart driftWeight s Ω hΩ X x₀ m) {α : ℝ}, 0 < α → α < 1 →
    LiftedBaseHolderEstimate C (G2.smoothNorm C.G) (driftOpWords q) α

/-- Higher Sobolev regularity, no drift (BB pp. 588-591, Thm 11.45, Props 11.46-11.47): for
`Ω' ⋐ Ω'' ⋐ Ω` (compact closures), fields smooth on `Ω` with the rank condition at every point,
`k ≥ 0` and `1 < p < ∞` there is `C = C(X, Ω', Ω'', p, k)` such that every `u ∈ W^{2,p}_X(Ω'')` with
`L u = f ∈ W^{k,p}_X(Ω'')` (weak word derivatives `X_i X_i u`, `f = ∑ᵢ X_i X_i u` a.e.) lies in
`W^{k+2,p}_X(Ω')` and `‖u‖_{W^{k+2,p}(Ω')} ≤ C (‖f‖_{W^{k,p}(Ω'')} + ‖u‖_{L^p(Ω'')})`. Stated for
systems with `3 ≤ n`. -/
def HigherSobolevRegularityNoDrift : Prop :=
  ∀ {n q : ℕ}, 3 ≤ n → ∀ (Ω Ω' Ω'' : Opens (Fin n → ℝ))
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (_hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (_hspan : bracketSpansOn (Ω : Set (Fin n → ℝ)) X),
    IsCompact (closure (Ω' : Set (Fin n → ℝ))) →
    closure (Ω' : Set (Fin n → ℝ)) ⊆ (Ω'' : Set (Fin n → ℝ)) →
    IsCompact (closure (Ω'' : Set (Fin n → ℝ))) →
    closure (Ω'' : Set (Fin n → ℝ)) ⊆ (Ω : Set (Fin n → ℝ)) →
    ∀ (k : ℕ) (p : ℝ≥0∞), 1 < p → p < ⊤ →
    ∃ C : ℝ, 0 < C ∧ ∀ u f : (Fin n → ℝ) → ℝ,
      memSobolevX noDriftWeight X Ω'' 2 p u →
      HasWeakOperatorValue X Ω'' (noDriftOpWords q) u f →
      memSobolevX noDriftWeight X Ω'' k p f →
      memSobolevX noDriftWeight X Ω' (k + 2) p u ∧
        sobolevXENorm noDriftWeight X Ω' (k + 2) p u ≤
          ENNReal.ofReal C *
            (sobolevXENorm noDriftWeight X Ω'' k p f +
              eLpNorm u p (volume.restrict (Ω'' : Set (Fin n → ℝ))))

/-- Higher Hölder regularity, no drift (BB pp. 603-604, Thms 11.59-11.60,
(11.94)-(11.96)): for `Ω' ⋐ Ω'' ⋐ Ω`, fields smooth on `Ω` with the rank condition, `k ≥ 0` and
`0 < α < 1` there is `C = C(X, Ω', Ω'', α, k)` such that every `u ∈ C^{2,α}_X(Ω'')` with
`L u = f ∈ C^{k,α}_X(Ω'')` (intrinsic word derivatives `X_i X_i u`, `f = ∑ᵢ X_i X_i u` pointwise)
lies in `C^{k+2,α}_X(Ω')` and
`‖u‖_{C^{k+2,α}(Ω')} ≤ C (‖f‖_{C^{k,α}(Ω'')} + ‖u‖_{L^∞(Ω'')})`, the Hölder seminorms taken for
the control distance of `Ω`. Stated for systems with `3 ≤ n`. -/
def HigherHolderRegularityNoDrift : Prop :=
  ∀ {n q : ℕ}, 3 ≤ n → ∀ (Ω Ω' Ω'' : Opens (Fin n → ℝ))
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (_hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (_hspan : bracketSpansOn (Ω : Set (Fin n → ℝ)) X),
    IsCompact (closure (Ω' : Set (Fin n → ℝ))) →
    closure (Ω' : Set (Fin n → ℝ)) ⊆ (Ω'' : Set (Fin n → ℝ)) →
    IsCompact (closure (Ω'' : Set (Fin n → ℝ))) →
    closure (Ω'' : Set (Fin n → ℝ)) ⊆ (Ω : Set (Fin n → ℝ)) →
    ∀ (k : ℕ) (α : ℝ), 0 < α → α < 1 →
    ∃ C : ℝ, 0 < C ∧ ∀ u f : (Fin n → ℝ) → ℝ,
      memHolderX noDriftWeight X (controlDistance (Ω : Set (Fin n → ℝ)) noDriftWeight X)
        Ω'' 2 α u →
      HasIntrinsicOperatorValue X Ω'' (noDriftOpWords q) u f →
      memHolderX noDriftWeight X (controlDistance (Ω : Set (Fin n → ℝ)) noDriftWeight X)
        Ω'' k α f →
      memHolderX noDriftWeight X (controlDistance (Ω : Set (Fin n → ℝ)) noDriftWeight X)
          Ω' (k + 2) α u ∧
        holderXENorm noDriftWeight X (controlDistance (Ω : Set (Fin n → ℝ)) noDriftWeight X)
            Ω' (k + 2) α u ≤
          ENNReal.ofReal C *
            (holderXENorm noDriftWeight X (controlDistance (Ω : Set (Fin n → ℝ)) noDriftWeight X)
                Ω'' k α f +
              eLpNorm u ⊤ (volume.restrict (Ω'' : Set (Fin n → ℝ))))

/-- The hypotheses of `rs3_drift_sobolev` (BB Thm 11.2, `L^p`, `k = 0`): the lifting theorem (drift),
left differentiation (`LeftDifferentiation`, through which local solvability holds) and the base Sobolev estimate. -/
structure DriftSobolevHypotheses : Prop where
  liftApproximation : LiftApproximationDriftStatement
  leftDifferentiation : LeftDifferentiationAllChartsDrift
  lifted : LiftedBaseSobolevAllChartsDrift

/-- The hypotheses of `rs3_drift_holder` (BB Thm 11.2, Hölder, `k = 0`): the lifting theorem (drift),
left differentiation (`LeftDifferentiation`, through which local solvability holds), the local doubling property and the base Hölder estimate. -/
structure DriftHolderHypotheses : Prop where
  liftApproximation : LiftApproximationDriftStatement
  leftDifferentiation : LeftDifferentiationAllChartsDrift
  doubling : LocalDoublingAllChartsDrift
  lifted : LiftedBaseHolderAllChartsDrift

/-- The hypotheses of `rs3_no_drift_sobolev` (BB Thm 11.1, `L^p`, all `k`): the lifting theorem (no
drift), left differentiation (`LeftDifferentiation`, through which local solvability holds) and the higher Sobolev estimate. -/
structure NoDriftSobolevHypotheses : Prop where
  liftApproximation : LiftApproximationNoDriftStatement
  leftDifferentiation : LeftDifferentiationAllChartsNoDrift
  higher : HigherSobolevRegularityNoDrift

/-- The hypotheses of `rs3_no_drift_holder` (BB Thm 11.1, Hölder, all `k`): the lifting theorem (no
drift), left differentiation (`LeftDifferentiation`, through which local solvability holds), the local doubling property and the higher Hölder estimate. -/
structure NoDriftHolderHypotheses : Prop where
  liftApproximation : LiftApproximationNoDriftStatement
  leftDifferentiation : LeftDifferentiationAllChartsNoDrift
  doubling : LocalDoublingAllChartsNoDrift
  higher : HigherHolderRegularityNoDrift

end RothschildStein.P2
