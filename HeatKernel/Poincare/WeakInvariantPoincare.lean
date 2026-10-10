-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Poincare.WeakGroupApproximation
public import HeatKernel.Poincare.CompactLp
public import HeatKernel.Poincare.FiniteGradientIntegrability
public import HeatKernel.Poincare.LpInequalityLimit

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set Filter MeasureTheory TopologicalSpace RothschildStein
open scoped ENNReal Topology BigOperators
namespace HeatKernel

/-- A smooth Poincaré inequality extends to weak invariant derivatives on every
measurable set contained in a compact interior subset, with the same coefficient. -/
theorem weak_invariant_poincare_of_smooth_bound
    {N q : ℕ} (G : HomogeneousGroup N) (Ω : Opens (Fin N → ℝ))
    {D K : Set (Fin N → ℝ)} (hK : IsCompact K)
    (hDK : D ⊆ K) (hKΩ : K ⊆ Ω) (v : Fin q → (Fin N → ℝ))
    {p : ℝ} (hp : 1 ≤ p) {C : ℝ≥0∞} (hC : C ≠ ⊤)
    (hPI : ∀ u : (Fin N → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) u →
      eLpNorm (fun x => u x - ⨍ y in D, u y) (ENNReal.ofReal p) (volume.restrict D) ≤
        C * eLpNorm (fun x => Real.sqrt (∑ j, fieldDerivative (G2.leftField G (v j)) u x ^ 2))
          (ENNReal.ofReal p) (volume.restrict D))
    {f : (Fin N → ℝ) → ℝ} {g : Fin q → (Fin N → ℝ) → ℝ}
    (hf : MemLp f (ENNReal.ofReal p) (volume.restrict (Ω : Set (Fin N → ℝ))))
    (hg : ∀ j, MemLp (g j) (ENNReal.ofReal p) (volume.restrict (Ω : Set (Fin N → ℝ))))
    (hw : ∀ j, hasWeakWordDeriv (fun _ : Fin 1 => G2.leftField G (v j)) Ω [0] f (g j)) :
    eLpNorm (fun x => f x - ⨍ y in D, f y) (ENNReal.ofReal p) (volume.restrict D) ≤
      C * eLpNorm (fun x => Real.sqrt (∑ j, g j x ^ 2))
        (ENNReal.ofReal p) (volume.restrict D) := by
  let _ : IsFiniteMeasure (volume.restrict D) := isFiniteMeasure_restrict.mpr
    ((measure_mono hDK).trans_lt hK.measure_lt_top).ne
  obtain ⟨u, hu, huf, hug⟩ := exists_smooth_weak_group_approximation G (G2.smoothNorm G)
    Ω hK hKΩ v hp hf hg hw
  let du := fun j n => fieldDerivative (G2.leftField G (v j)) (u n)
  have hdu : ∀ j n, Continuous (du j n) := by
    intro j n
    exact ((hu n).continuous_fderiv (by simp)).clm_apply (G2.contDiff_leftField G (v j)).continuous
  have hum : ∀ n, MemLp (u n) (ENNReal.ofReal p) (volume.restrict D) := fun n =>
    (memLp_restrict_compact_of_continuousOn hK (hu n).continuous.continuousOn _).mono_measure
      (Measure.restrict_mono hDK le_rfl)
  have hdum : ∀ j n, MemLp (du j n) (ENNReal.ofReal p) (volume.restrict D) := fun j n =>
    (memLp_restrict_compact_of_continuousOn hK (hdu j n).continuousOn _).mono_measure
      (Measure.restrict_mono hDK le_rfl)
  have hgm : ∀ j, MemLp (g j) (ENNReal.ofReal p) (volume.restrict D) := fun j =>
    (hg j).mono_measure (Measure.restrict_mono (hDK.trans hKΩ) le_rfl)
  have hfm : MemLp f (ENNReal.ofReal p) (volume.restrict D) :=
    hf.mono_measure (Measure.restrict_mono (hDK.trans hKΩ) le_rfl)
  have hdulim : ∀ j, Tendsto (fun n => eLpNorm (du j n - g j)
      (ENNReal.ofReal p) (volume.restrict D)) atTop (𝓝 0) := fun j =>
    tendsto_eLpNorm_sub_restrict_of_subset hDK (hug j)
  have hpE : 1 ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp
  exact eLpNorm_mean_oscillation_le_mul_of_strong_limits hp hum
    (fun n => memLp_finite_gradient_length (fun j => hdum j n)) hfm
    (memLp_finite_gradient_length hgm)
    (tendsto_eLpNorm_sub_restrict_of_subset hDK huf)
    (tendsto_eLpNorm_finite_gradient_length hpE
      (fun j n => (hdum j n).aestronglyMeasurable)
      (fun j => (hgm j).aestronglyMeasurable) hdulim)
    hC (Eventually.of_forall (fun n => hPI (u n) (hu n)))

end HeatKernel
