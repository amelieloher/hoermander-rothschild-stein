-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.ControlledReparam
public import Mathlib.Analysis.Real.Sqrt

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators ENNReal

namespace RothschildStein.G1

/-- A C¹ generator arc on the normalized interval is a controlled curve
whenever its constant speed fits the generator's weighted parameter
(BB Rem 1.34, pp. 18–19; Rem 1.40, p. 22). -/
theorem isControlledCurve_generatorArc {m n : ℕ} {Ω : Set (Fin n → ℝ)}
    {w : Fin m → ℕ+} {X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)}
    {γ : ℝ → (Fin n → ℝ)} (hs : ContDiffOn ℝ 1 γ (Icc 0 1))
    (hrange : MapsTo γ (Icc 0 1) Ω) (i : Fin m) {t δ : ℝ} (hδ : 0 < δ)
    (hd : ∀ v ∈ Icc 0 1, HasDerivAt γ (t • X i (γ v)) v)
    (hcost : |t| ≤ δ ^ (w i : ℕ)) : isControlledCurve Ω w X δ γ := by
  classical
  obtain ⟨K, hK⟩ := hs.exists_lipschitzOnWith one_ne_zero (convex_Icc 0 1) isCompact_Icc
  have hac : AbsolutelyContinuousOnInterval γ 0 1 :=
    (show LipschitzOnWith K γ (uIcc 0 1) by simpa only [uIcc_of_le zero_le_one] using hK).absolutelyContinuousOnInterval
  refine ⟨hδ, hac, hrange,
    fun j _ => if j = i then t else 0, fun j => aemeasurable_const, ?_⟩
  apply ae_restrict_of_forall_mem measurableSet_Icc
  intro v hv
  refine ⟨fun j => ?_, ?_⟩
  · by_cases h : j = i
    · simpa only [h, ite_true] using hcost
    · simp only [ite_eq_right h, abs_zero]; positivity
  · simpa only [ite_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_eq_left] using hd v hv

end RothschildStein.G1
