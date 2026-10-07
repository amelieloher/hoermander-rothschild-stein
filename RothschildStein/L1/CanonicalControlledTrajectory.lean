-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.CanonicalChartData
public import RothschildStein.G4.ConstantControl
public import Mathlib.Analysis.Calculus.Deriv.Comp
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric MeasureTheory Filter
open scoped BigOperators
namespace RothschildStein.L1.CanonicalFrameChartData

/-- The actual canonical coefficient/time rescaling is an
absolutely continuous unit-time curve with exactly the canonical
coefficients in its ODE. -/
theorem exists_canonical_controlled_trajectory_of_parameters {N : ℕ}
    {Ω : Set (Fin N → ℝ)} {Y : Fin N → (Fin N → ℝ) → (Fin N → ℝ)}
    {x : Fin N → ℝ} (C : CanonicalFrameChartData Ω Y x)
    {η u : Fin N → ℝ} (hq : (C.time⁻¹ • u,η) ∈ ball (0,x) C.initialRadius) :
    ∃ γ : ℝ → (Fin N → ℝ), AbsolutelyContinuousOnInterval γ 0 1 ∧
      MapsTo γ (Icc 0 1) Ω ∧ γ 0 = η ∧
      γ 1 = canonicalFrameMap C.time C.flow (η,u) ∧
      ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt γ (∑ i, u i • Y i (γ t)) t := by
  let q := (C.time⁻¹ • u,η)
  let γ := fun t : ℝ => C.flow (q,C.time*t)
  have ht : ∀ t ∈ Icc (0 : ℝ) 1, C.time*t ∈ Ioo (-C.timeRadius) C.timeRadius := by
    intro t ht
    have ht₀ := mul_nonneg C.time_pos.le ht.1
    have ht₁ := mul_le_mul_of_nonneg_left ht.2 C.time_pos.le
    constructor <;> linarith [C.timeRadius_pos,C.time_lt]
  have hγ : ContDiffOn ℝ (⊤ : ℕ∞) γ (Icc (0 : ℝ) 1) :=
    C.flow_smooth.comp (contDiffOn_const.prodMk (contDiffOn_const.mul contDiffOn_id))
      (fun t h => ⟨hq,ht t h⟩)
  have hd : ∀ t ∈ Icc (0 : ℝ) 1, HasDerivAt γ (∑ i, u i • Y i (γ t)) t := by
    intro t h
    have hi : HasDerivAt (fun v : ℝ => C.time*v) C.time t :=
      by simpa using (hasDerivAt_id t).const_mul C.time
    have hh := ((C.flow_ode q hq).2 (C.time*t) (ht t h)).1.scomp t hi
    have he : C.time • frameCoefficientField Y (q.1,γ t) =
        ∑ i, u i • Y i (γ t) := by
      dsimp [frameCoefficientField,q]
      simp only [Finset.smul_sum,smul_smul]
      congr 1
      funext i
      rw [← mul_assoc,mul_inv_cancel₀ C.time_pos.ne',one_mul]
    exact he ▸ hh
  refine ⟨γ, ?_, ?_, ?_, ?_, hd⟩
  · apply ContDiffOn.absolutelyContinuousOnInterval
    simpa only [uIcc_of_le zero_le_one] using hγ.of_le (by simp : (1 : WithTop ℕ∞) ≤ (⊤ : ℕ∞))
  · intro t h
    exact ((C.flow_ode q hq).2 (C.time*t) (ht t h)).2
  · simpa only [γ,mul_zero] using (C.flow_ode q hq).1
  · simp only [γ,canonicalFrameMap,q,mul_one]

end RothschildStein.L1.CanonicalFrameChartData
