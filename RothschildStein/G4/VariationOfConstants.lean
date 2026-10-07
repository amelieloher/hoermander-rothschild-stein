-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.LocalFlows
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.Deriv.Mul

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory

namespace RothschildStein.G4

/-- Multiplying the inhomogeneous variational equation by an
inverse fundamental matrix cancels the homogeneous term exactly.
The oriented formula works for both signs of endpoint time
(BB Lemma 9.48, pp. 441–442). -/
theorem variation_of_constants {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (A D : ℝ → E →L[ℝ] E)
    (F v : ℝ → E) (J : E →L[ℝ] E) (t : ℝ)
    (hA : ∀ s ∈ uIcc 0 t, HasDerivAt A (-(A s).comp (D s)) s)
    (hv : ∀ s ∈ uIcc 0 t, HasDerivAt v (D s (v s) + F s) s)
    (hF : ContinuousOn F (uIcc 0 t)) (hzero : v 0 = 0)
    (hinv : J.comp (A t) = ContinuousLinearMap.id ℝ E) :
    v t = J (∫ s in 0..t, A s (F s)) := by
  have hd : ∀ s ∈ uIcc 0 t, HasDerivAt (fun s => A s (v s)) (A s (F s)) s := by
    intro s hs
    simpa only [neg_apply, ContinuousLinearMap.comp_apply, map_add, neg_add_cancel_left] using
      (hA s hs).clm_apply (hv s hs)
  have hc : ContinuousOn (fun s => A s (F s)) (uIcc 0 t) := by
    intro s hs
    exact ((hA s hs).continuousAt.continuousWithinAt.clm_apply (hF s hs))
  have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt hd hc.intervalIntegrable
  rw [hzero, map_zero, sub_zero] at heq
  have hi := congrArg (fun L : E →L[ℝ] E => L (v t)) hinv
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at hi
  rw [← hi, ← heq]

/-- The same formula is the transported forcing integral once
the actual flow transition derivative is identified with J composed with
the inverse fundamental matrix (BB Lemma 9.48, pp. 441–442). -/
theorem transported_variation_of_constants {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (A D T : ℝ → E →L[ℝ] E)
    (F v : ℝ → E) (J : E →L[ℝ] E) (t : ℝ)
    (hA : ∀ s ∈ uIcc 0 t, HasDerivAt A (-(A s).comp (D s)) s)
    (hv : ∀ s ∈ uIcc 0 t, HasDerivAt v (D s (v s) + F s) s)
    (hF : ContinuousOn F (uIcc 0 t)) (hzero : v 0 = 0)
    (hinv : J.comp (A t) = ContinuousLinearMap.id ℝ E)
    (htransition : ∀ s ∈ uIcc 0 t, J.comp (A s) = T s) :
    v t = ∫ s in 0..t, T s (F s) := by
  have hc : ContinuousOn (fun s => A s (F s)) (uIcc 0 t) := by
    intro s hs
    exact (hA s hs).continuousAt.continuousWithinAt.clm_apply (hF s hs)
  rw [variation_of_constants A D F v J t hA hv hF hzero hinv,
    ← J.intervalIntegral_comp_comm hc.intervalIntegrable]
  apply intervalIntegral.integral_congr
  intro s hs
  exact congrArg (fun L : E →L[ℝ] E => L (F s)) (htransition s hs)

end RothschildStein.G4
