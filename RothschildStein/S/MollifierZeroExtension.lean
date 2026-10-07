-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.MollifierConvergence
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory Filter
open scoped Topology ENNReal
namespace RothschildStein.S
variable {n : ℕ} {p : ℝ≥0∞} {Ω : Set (Fin n → ℝ)}

/-- Zero extension identifies the local and global Lp norms
(BB Lemma 2.8, p. 72; domain convention). -/
theorem eLpNorm_zeroExtension (hΩ : MeasurableSet Ω) (f : (Fin n → ℝ) → ℝ) :
    eLpNorm (Ω.indicator f) p volume = eLpNorm f p (volume.restrict Ω) :=
  eLpNorm_indicator_eq_eLpNorm_restrict hΩ

/-- Local Lp data extend by zero to global Lp data
(BB Lemma 2.8, p. 72; domain convention). -/
theorem memLp_zeroExtension_iff (hΩ : MeasurableSet Ω) (f : (Fin n → ℝ) → ℝ) :
    MemLp (Ω.indicator f) p volume ↔ MemLp f p (volume.restrict Ω) :=
  memLp_indicator_iff_restrict hΩ

end RothschildStein.S
