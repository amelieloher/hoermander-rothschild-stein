-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.Gauge
public import RothschildStein.G2.BallTopology
public import RothschildStein.G2.DilationMeasure
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
namespace RothschildStein.H1
variable {N : ℕ} {G : HomogeneousGroup N}

/-- Closed gauge shell; its positive-radius boundaries are null
when converting to the open-shell cancellation property (BB p. 274). -/
def gaugeShell (ν : (Fin N → ℝ) → ℝ) (r R : ℝ) : Set (Fin N → ℝ) :=
  {x | r ≤ ν x ∧ ν x ≤ R}

/-- The normalization uses the shell from 1 to e, so the
coefficient multiplying log(R/r) is exactly this integral (BB (6.38)). -/
def homogeneousShellMean (ν f : (Fin N → ℝ) → ℝ) : ℝ :=
  ∫ x in gaugeShell ν 1 (Real.exp 1), f x

/-- Cancellation is an integral over every positive shell;
no unweighted surface-measure cancellation is asserted. -/
def HasVanishingShellIntegrals (ν f : (Fin N → ℝ) → ℝ) : Prop :=
  ∀ r R : ℝ, 0 < r → r < R → (∫ x in gaugeShell ν r R, f x) = 0

/-- Gauge shells are measurable without regularity of their
boundary (BB p. 274). -/
theorem measurableSet_gaugeShell {ν : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    (r R : ℝ) : MeasurableSet (gaugeShell ν r R) :=
  ((isClosed_le continuous_const hν.1).inter (isClosed_le hν.1 continuous_const)).measurableSet

/-- Closed shells are compact for every homogeneous gauge
(BB pp. 274–275; properness of homogeneous gauge balls). -/
theorem isCompact_gaugeShell {ν : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    (r R : ℝ) : IsCompact (gaugeShell ν r R) := by
  exact (G2.isCompact_gauge_le hν R).inter_left (isClosed_le continuous_const hν.1)

/-- A positive inner radius keeps the shell away from the
origin, independently of the kernel's assigned value there. -/
theorem gaugeShell_subset_punctured {ν : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    {r R : ℝ} (hr : 0 < r) : gaugeShell ν r R ⊆ {(0 : Fin N → ℝ)}ᶜ := by
  intro x hx
  change x ≠ 0
  intro he
  subst x
  have hz : ν 0 = 0 := (hν.2.2.1 0).mpr rfl
  have hb : r ≤ ν 0 := hx.1
  rw [hz] at hb
  exact (not_le.mpr hr) hb

/-- Punctured continuity suffices for absolute integrability on
every compact positive shell (BB Prop 6.26, p. 274). -/
theorem integrableOn_gaugeShell {ν f : (Fin N → ℝ) → ℝ}
    (hν : G.IsHomogeneousGauge ν) (hf : ContinuousOn f {(0 : Fin N → ℝ)}ᶜ)
    {r R : ℝ} (hr : 0 < r) : IntegrableOn f (gaugeShell ν r R) volume :=
  (hf.mono (gaugeShell_subset_punctured hν hr)).integrableOn_compact (isCompact_gaugeShell hν r R)

end RothschildStein.H1
