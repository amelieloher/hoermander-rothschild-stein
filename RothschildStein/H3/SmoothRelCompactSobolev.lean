-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.ClassicalWords
public import RothschildStein.S.Sobolev
public import Mathlib.MeasureTheory.Function.LpSpace.Indicator

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory TopologicalSpace
open scoped ENNReal

/-- A function continuous on a compact neighborhood has every local
Lp exponent on the relatively compact open subset. -/
theorem memLp_of_continuousOn_relCompact {n : ℕ}
    (Ω U : Opens (Fin n → ℝ)) (hK : IsCompact (closure (U : Set (Fin n → ℝ))))
    (hKΩ : closure (U : Set (Fin n → ℝ)) ⊆ Ω)
    {f : (Fin n → ℝ) → ℝ} (hf : ContinuousOn f (Ω : Set (Fin n → ℝ)))
    (p : ℝ≥0∞) : MemLp f p (volume.restrict (U : Set (Fin n → ℝ))) := by
  let K := closure (U : Set (Fin n → ℝ))
  have : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  have hc : ContinuousOn f K := hf.mono hKΩ
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn hc
  have hl : MemLp f p (volume.restrict K) :=
    MemLp.of_bound (hc.aestronglyMeasurable hK.measurableSet) C (by
      filter_upwards [ae_restrict_mem hK.measurableSet] with x hx
      exact hC x hx)
  exact hl.mono_measure (Measure.restrict_mono_set volume subset_closure)

/-- a smooth homogeneous remainder belongs to every
weighted Sobolev class on each relatively compact open subset. -/
theorem memSobolevX_of_contDiffOn_relCompact {n m : ℕ}
    (Ω U : Opens (Fin n → ℝ)) (hK : IsCompact (closure (U : Set (Fin n → ℝ))))
    (hKΩ : closure (U : Set (Fin n → ℝ)) ⊆ Ω)
    (w : Fin m → ℕ+) (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (k : ℕ) (p : ℝ≥0∞) (f : (Fin n → ℝ) → ℝ)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (Ω : Set (Fin n → ℝ))) :
    memSobolevX w X U k p f := by
  have hUΩ : (U : Set (Fin n → ℝ)) ⊆ Ω := subset_closure.trans hKΩ
  refine ⟨memLp_of_continuousOn_relCompact Ω U hK hKΩ hf.continuousOn p, ?_⟩
  intro I _
  exact ⟨wordDerivative X I f,
    S.hasWeakWordDeriv_classical U X (fun i => (hX i).mono hUΩ) I f (hf.mono hUΩ),
    memLp_of_continuousOn_relCompact Ω U hK hKΩ
      (S.contDiffOn_wordDerivative Ω X hX I f hf).continuousOn p⟩

end RothschildStein.H3
