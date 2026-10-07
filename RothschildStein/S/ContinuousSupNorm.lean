-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.MollifierZeroExtension
public import Mathlib.MeasureTheory.Measure.OpenPos

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped ENNReal
namespace RothschildStein.S
variable {n : ℕ}

/-- Continuous functions on an open Euclidean domain have
pointwise supremum equal to their exact L-infinity seminorm, including
empty domains (BB Def 2.13, p. 81; pointwise representative). -/
theorem eLpNorm_top_eq_iSup_of_continuousOn
    (Ω : Opens (Fin n → ℝ)) {f : (Fin n → ℝ) → ℝ}
    (hf : ContinuousOn f (Ω : Set (Fin n → ℝ))) :
    eLpNorm f ⊤ (volume.restrict (Ω : Set (Fin n → ℝ))) =
      ⨆ x : Ω, ENNReal.ofReal |f x.val| := by
  let h := (Ω : Set (Fin n → ℝ)).indicator f
  have hm : AEStronglyMeasurable h volume :=
    (aestronglyMeasurable_indicator_iff Ω.isOpen.measurableSet).mpr
      (hf.aestronglyMeasurable Ω.isOpen.measurableSet)
  have he : (⨆ x : Fin n → ℝ, ‖h x‖ₑ) = essSup (fun x => ‖h x‖ₑ) volume := by
    apply iSup_eq_essSup
    intro x a hx
    have hxo : x ∈ (Ω : Set (Fin n → ℝ)) := by
      by_contra hn
      simp only [h,indicator_of_notMem hn,enorm_zero,not_lt_zero] at hx
    have hs : {y | a < ‖h y‖ₑ} = (Ω : Set (Fin n → ℝ)) ∩ {y | a < ‖f y‖ₑ} := by
      ext y
      change (a < ‖h y‖ₑ) ↔ (y ∈ (Ω : Set (Fin n → ℝ)) ∧ a < ‖f y‖ₑ)
      by_cases hy : y ∈ (Ω : Set (Fin n → ℝ))
      · simp only [h,indicator_of_mem hy,hy,true_and]
      · simp only [h,indicator_of_notMem hy,enorm_zero,not_lt_zero,hy,false_and]
    rw [hs]
    exact (hf.enorm.isOpen_inter_preimage Ω.isOpen isOpen_Ioi).measure_ne_zero volume
      ⟨x,hxo,by
        change a < ‖f x‖ₑ
        simpa only [h,indicator_of_mem hxo] using! hx⟩
  rw [← eLpNorm_zeroExtension Ω.isOpen.measurableSet f,
    eLpNorm_exponent_top hm]
  change essSup (fun x => ‖h x‖ₑ) volume = _
  rw [← he]
  apply le_antisymm
  · apply iSup_le
    intro x
    by_cases hx : x ∈ (Ω : Set (Fin n → ℝ))
    · simpa only [h,indicator_of_mem hx,← ofReal_norm,Real.norm_eq_abs] using!
        le_iSup (fun z : Ω => ENNReal.ofReal |f z.val|) ⟨x,hx⟩
    · simp only [h,indicator_of_notMem hx,enorm_zero,zero_le]
  · apply iSup_le
    intro x
    simpa only [h,indicator_of_mem x.property,← ofReal_norm,Real.norm_eq_abs] using!
      le_iSup (fun z : Fin n → ℝ => ‖h z‖ₑ) x.val

end RothschildStein.S
