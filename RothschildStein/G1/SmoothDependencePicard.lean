-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.SmoothDependenceLinearFamily

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric Filter Function ODE MeasureTheory
open scoped Topology NNReal

namespace RothschildStein.G1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Extend a continuous curve constantly beyond the endpoints of its interval. -/
def extendedCurve {T : ℝ} (hT : 0 ≤ T) (γ : C(Icc (-T) T, E)) : ℝ → E :=
  fun t => γ (projIcc (-T) T (by linarith) t)

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- Constant endpoint extension is continuous. -/
theorem extendedCurve_continuous {T : ℝ} (hT : 0 ≤ T) (γ : C(Icc (-T) T, E)) :
    Continuous (extendedCurve hT γ) := γ.continuous.comp continuous_projIcc

omit [NormedSpace ℝ E] [CompleteSpace E] in
/-- Endpoint extension agrees with the original curve on its interval. -/
theorem extendedCurve_apply {T : ℝ} (hT : 0 ≤ T) (γ : C(Icc (-T) T, E))
    {t : ℝ} (ht : t ∈ Icc (-T) T) : extendedCurve hT γ t = γ ⟨t, ht⟩ := by
  simp only [extendedCurve, projIcc_of_mem _ ht]

/-- The linear Picard map on all continuous curves. No a priori bound on
curve values is imposed, so the time interval can be arbitrarily long. -/
def linearPicard {T : ℝ} (hT : 0 ≤ T) (A : ℝ → E →L[ℝ] E)
    (hc : ContinuousOn A (Icc (-T) T)) (w₀ : E) : C(Icc (-T) T, E) → C(Icc (-T) T, E) :=
  fun γ =>
    { toFun := fun t => picard (fun s w => A s w) 0 w₀ (extendedCurve hT γ) t
      continuous_toFun := by
        have hf : ContinuousOn (fun p : ℝ × E => A p.1 p.2) (Icc (-T) T ×ˢ univ) :=
          (hc.comp continuous_fst.continuousOn (fun _ hp => hp.1)).clm_apply continuous_snd.continuousOn
        have hd : ∀ t ∈ Icc (-T) T,
            HasDerivWithinAt (picard (fun s w => A s w) 0 w₀ (extendedCurve hT γ))
              (A t (extendedCurve hT γ t)) (Icc (-T) T) t :=
          fun t ht => hasDerivWithinAt_picard_Icc (by constructor <;> linarith) hf
            (extendedCurve_continuous hT γ).continuousOn (fun _ _ => mem_univ _) w₀ ht
        exact continuousOn_iff_continuous_domRestrict.mp (HasDerivWithinAt.continuousOn hd) }

/-- Evaluation of the linear Picard operator. -/
theorem linearPicard_apply {T : ℝ} (hT : 0 ≤ T) (A : ℝ → E →L[ℝ] E)
    (hc : ContinuousOn A (Icc (-T) T)) (w₀ : E) (γ : C(Icc (-T) T, E))
    (t : Icc (-T) T) :
    linearPicard hT A hc w₀ γ t = w₀ + ∫ s in (0 : ℝ)..t.1, A s (extendedCurve hT γ s) := rfl

omit [CompleteSpace E] in
/-- The integrand in every Picard iterate is integrable on
all subintervals (BB Proposition 1.2, p. 3). -/
theorem linearPicard_integrable {T : ℝ} (hT : 0 ≤ T) (A : ℝ → E →L[ℝ] E)
    (hc : ContinuousOn A (Icc (-T) T)) (γ : C(Icc (-T) T, E))
    (t : Icc (-T) T) : IntervalIntegrable (fun s => A s (extendedCurve hT γ s)) volume 0 t.1 :=
  ((hc.clm_apply (extendedCurve_continuous hT γ).continuousOn).mono
    (uIcc_subset_Icc (by constructor <;> linarith) t.property)).intervalIntegrable

end RothschildStein.G1
