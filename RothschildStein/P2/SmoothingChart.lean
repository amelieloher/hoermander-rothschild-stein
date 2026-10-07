-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.Smoothing
public import RothschildStein.P2.NormTransfer

/-!
# The fiber test map and adjoint intertwining in a lifted chart

For a lifted chart `C` (`RothschildStein.P1.LiftedChart`) the `fiber_average` field over the whole
chart neighborhood `U` supplies the continuous fiber integration `J : C_c^∞(U) → C_c^∞(Ω)`
(`Jφ(x) = ∫ φ(x, t) dt`), bundled as a `FiberIntegration`. The lifted distribution of
`T ∈ 𝒟'(Ω)` is `T̃ = T ∘ J ∈ 𝒟'(U)`, and `L T = f` on `Ω` gives `L̃ T̃ = f̃ = f ∘ π` on `U`
(BB pp. 608-609, (11.101)).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped ENNReal Topology BigOperators Distributions CompactConvergenceCLM
open RothschildStein.P1
namespace RothschildStein.P2
variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}

/-- The chart neighborhood `U` as an open set of `ℝⁿ⁺ᵐ`. -/
def liftedChartOpens (C : LiftedChart w s Ω hΩ X x₀ m) : Opens (Fin (n + m) → ℝ) :=
  ⟨C.U, C.isOpen_U⟩

/-- The base domain `Ω` as an open set of `ℝⁿ`. -/
def liftedChartBaseOpens (_C : LiftedChart w s Ω hΩ X x₀ m) : Opens (Fin n → ℝ) :=
  ⟨Ω, hΩ⟩

/-- The chart neighborhood lies in the lifted domain `O`. -/
theorem liftedChart_subset_O (C : LiftedChart w s Ω hΩ X x₀ m) : C.U ⊆ C.O := fun _ hξ =>
  C.closure_U_subset (subset_closure hξ)

/-- Points of the chart neighborhood project into `Ω`. -/
theorem liftedChart_basePoint_mem (C : LiftedChart w s Ω hΩ X x₀ m) {ξ : Fin (n + m) → ℝ}
    (hξ : ξ ∈ C.U) : basePoint ξ ∈ Ω :=
  (liftedChart_subset_O C) hξ

/-- The lifted fields are smooth on the chart neighborhood. -/
theorem liftedChart_contDiffOn_lift (C : LiftedChart w s Ω hΩ X x₀ m) (i : Fin k) :
    ContDiffOn ℝ (⊤ : ℕ∞) (C.Xl i) ((liftedChartOpens C) : Set (Fin (n + m) → ℝ)) :=
  (C.lift_smooth i).mono (liftedChart_subset_O C)

/-- The fibers of the (bounded) chart neighborhood have bounded volume. -/
theorem liftedChart_fiberVolume_bounded (C : LiftedChart w s Ω hΩ X x₀ m) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ z, fiberVolume C.U z ≤ ENNReal.ofReal c := by
  have hK : IsCompact (tailPoint '' closure C.U : Set (Fin m → ℝ)) :=
    C.isCompact_closure_U.image continuous_tailPoint
  refine ⟨(volume (tailPoint '' closure C.U : Set (Fin m → ℝ))).toReal, ENNReal.toReal_nonneg,
    fun z => ?_⟩
  rw [ENNReal.ofReal_toReal hK.measure_lt_top.ne]
  refine measure_mono ?_
  intro t ht
  exact ⟨joinPoint z t, subset_closure ht, tailPoint_joinPoint z t⟩

/-- The fiber setting of the chart neighborhood over `Ω`. -/
theorem liftedChartFiberSetting (C : LiftedChart w s Ω hΩ X x₀ m) :
    FiberSetting (liftedChartOpens C) (liftedChartBaseOpens C) :=
  liftedChart_fiberSetting C (liftedChartOpens C) (liftedChartBaseOpens C) subset_rfl (fun _ hξ => (liftedChart_basePoint_mem C) hξ)
    (liftedChart_fiberVolume_bounded C)

/-- The continuous fiber integration `J : C_c^∞(U) → C_c^∞(Ω)`,
`J φ (x) = ∫ φ(x, t) dt`, of a lifted chart: the `fiber_average` field over the whole neighborhood
`U` (BB p. 608, (11.101); p. 584). -/
def liftedChartFiberIntegration (C : LiftedChart w s Ω hΩ X x₀ m) :
    FiberIntegration (liftedChartOpens C) (liftedChartBaseOpens C) where
  setting := (liftedChartFiberSetting C)
  J := (C.fiber_average (liftedChartOpens C) rfl).choose
  J_apply := (C.fiber_average (liftedChartOpens C) rfl).choose_spec

/-- The lifted distribution `T̃ = T ∘ J` on `U` of a distribution `T` on
`Ω`. -/
def liftedChartLift (C : LiftedChart w s Ω hΩ X x₀ m)
    (T : Distribution (liftedChartBaseOpens C) ℝ (⊤ : ℕ∞)) : Distribution (liftedChartOpens C) ℝ (⊤ : ℕ∞) :=
  (liftedChartFiberIntegration C).lift T

/-- The lift of a regular distribution is the regular distribution of `f ∘ π`. -/
theorem liftedChartLift_ofFun (C : LiftedChart w s Ω hΩ X x₀ m)
    {f : (Fin n → ℝ) → ℝ} (hf : LocallyIntegrableOn f (Ω : Set (Fin n → ℝ)) volume) :
    liftedChartLift C (Distribution.ofFun (liftedChartBaseOpens C) f volume (⊤ : ℕ∞)) =
      Distribution.ofFun (liftedChartOpens C) (fun ξ => f (basePoint ξ)) volume (⊤ : ℕ∞) :=
  (liftedChartFiberIntegration C).lift_ofFun hf

/-- In a lifted chart, `L T = f` on `Ω` implies `L̃ T̃ = f̃` on `U`,
`f̃ = f ∘ π` (no drift; BB p. 609, (11.101)). -/
theorem liftedChart_hasDistributionEquation_lift {q : ℕ} {w : Fin q → ℕ+}
    {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)} (C : LiftedChart w s Ω hΩ X x₀ m)
    {T : Distribution (liftedChartBaseOpens C) ℝ (⊤ : ℕ∞)} {f : (Fin n → ℝ) → ℝ}
    (h : hasDistributionEquation (liftedChartBaseOpens C) X (liftedChart_contDiffOn_base C) T f) :
    hasDistributionEquation (liftedChartOpens C) C.Xl (liftedChart_contDiffOn_lift C) (liftedChartLift C T)
      (fun ξ => f (basePoint ξ)) :=
  (liftedChartFiberIntegration C).hasDistributionEquation_lift X C.P (liftedChart_contDiffOn_lift C) (liftedChart_contDiffOn_base C) h

/-- The same with drift: `L = ∑ Xᵢ² + X₀`, fields `Fin (q + 1)`. -/
theorem liftedChart_hasDistributionEquationWithDrift_lift {q : ℕ} {w : Fin (q + 1) → ℕ+}
    {X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ)} (C : LiftedChart w s Ω hΩ X x₀ m)
    {T : Distribution (liftedChartBaseOpens C) ℝ (⊤ : ℕ∞)} {f : (Fin n → ℝ) → ℝ}
    (h : hasDistributionEquationWithDrift (liftedChartBaseOpens C) X (liftedChart_contDiffOn_base C) T f) :
    hasDistributionEquationWithDrift (liftedChartOpens C) C.Xl (liftedChart_contDiffOn_lift C) (liftedChartLift C T)
      (fun ξ => f (basePoint ξ)) :=
  (liftedChartFiberIntegration C).hasDistributionEquationWithDrift_lift X C.P (liftedChart_contDiffOn_lift C)
    (liftedChart_contDiffOn_base C) h

end RothschildStein.P2
