-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Function.LpSpace.Complete

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped Topology ENNReal
namespace RothschildStein.S
variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Translations act isometrically on coordinate Lp spaces
(BB Lemma 2.8, p. 72; translation). -/
def lpTranslate (f : Lp ℝ p (volume : Measure (Fin n → ℝ))) (w : Fin n → ℝ) :
    Lp ℝ p (volume : Measure (Fin n → ℝ)) :=
  Lp.compMeasurePreserving (fun x => x+w)
    (measurePreserving_add_right volume w) f

/-- Finite-p translation is continuous in the displacement
(BB Lemma 2.8, p. 72; translation). -/
theorem continuous_lpTranslate (hp : p ≠ ⊤)
    (f : Lp ℝ p (volume : Measure (Fin n → ℝ))) : Continuous (lpTranslate f) := by
  have hc : Continuous (fun w : Fin n → ℝ =>
      (⟨fun x => x+w,continuous_id.add continuous_const⟩ : C(Fin n → ℝ,Fin n → ℝ))) :=
    ContinuousMap.continuous_of_continuous_uncurry _ (continuous_snd.add continuous_fst)
  exact continuous_const.compMeasurePreservingLp hc
    (fun w => measurePreserving_add_right volume w) hp

omit [Fact (1 ≤ p)] in
/-- Translation by zero fixes the a.e. function class
(BB Lemma 2.8, p. 72). -/
theorem lpTranslate_zero (f : Lp ℝ p (volume : Measure (Fin n → ℝ))) :
    lpTranslate f 0 = f := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving f
    (measurePreserving_add_right volume (0 : Fin n → ℝ))] with x hx
  simpa only [lpTranslate,Function.comp_apply,add_zero] using hx

/-- The Lp translation increment tends to zero
(BB Lemma 2.8, p. 72; translation). -/
theorem tendsto_translation_increment (hp : p ≠ ⊤)
    (f : Lp ℝ p (volume : Measure (Fin n → ℝ))) :
    Tendsto (fun w : Fin n → ℝ =>
      eLpNorm (fun x => f (x+w)-f x) p volume) (𝓝 0) (𝓝 0) := by
  have ht := (continuous_lpTranslate hp f).tendsto 0
  rw [lpTranslate_zero] at ht
  have hd := tendsto_iff_edist_tendsto_0.mp ht
  apply hd.congr
  intro w
  rw [edist_eq_enorm_sub,Lp.enorm_def]
  apply eLpNorm_congr_ae
  filter_upwards [Lp.coeFn_sub (lpTranslate f w) f,
    Lp.coeFn_compMeasurePreserving f (measurePreserving_add_right volume w)] with x hs ht
  exact hs.trans (congrArg (· - f x) ht)

end RothschildStein.S
