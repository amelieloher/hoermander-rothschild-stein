-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.RadialExpansionBound
public import RothschildStein.H3.RadialBoundConstants
public import RothschildStein.H3.PlateauWords
public import RothschildStein.H3.WordTranslation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.H3

/-- All ordered derivative words of the actual smooth gauge
 cutoff have uniform inverse-gap bounds. One constant per word suffices
 for all centers and radii; drift counts twice. -/
theorem exists_cutoff_all_word_constants {n q : ℕ} (G : HomogeneousGroup n)
    (H : H1.StandingHypotheses G q) (ν : G2.HomogeneousNorm G) (hν : ν.Smooth) :
    ∃ C : List (Fin (q+1)) → ℝ, (∀ I, 0 < C I) ∧
      ∀ I, I ≠ [] → ∀ x₀ : Fin n → ℝ, ∀ t s : ℝ,
        0 < t → t < s → s/2 ≤ t → ∀ x : Fin n → ℝ,
        |wordDerivative H.fields I (smoothQuasiballCutoff G ν x₀ t s) x| ≤
          C I/(s-t)^(H1.differentialWordWeight I) := by
  obtain ⟨κ,hκ,hprofile⟩ := exists_profile_word_constants
  obtain ⟨M,hM,hgauge⟩ := exists_gauge_word_constants G H ν hν
  let C : List (Fin (q+1)) → ℝ := fun I => radialWordBoundConstant κ M I+1
  have hC : ∀ I, 0 < C I := fun I =>
    add_pos_of_nonneg_of_pos (radialWordBoundConstant_nonneg κ M hκ hM I) (by norm_num)
  refine ⟨C,hC,?_⟩
  intro I hI x₀ t s ht hts hhalf x
  have he := congrFun (wordDerivative_smoothQuasiballCutoff G ν hν H.fields
    (H.fields_smooth G) H.invariant I x₀ ht hts) x
  simp only [Function.comp_apply] at he
  rw [he]
  let y := G.mul (G.inv x₀) x
  change |wordDerivative H.fields I (quasiballProfile t s ∘ ν) y| ≤ C I/(s-t)^_
  by_cases hbelow : ν y < t
  · rw [radialProfile_wordDerivative_zero_below G ν H.fields I hI hts hbelow,abs_zero]
    exact div_nonneg (hC I).le (pow_nonneg (sub_nonneg.mpr hts.le) _)
  · have hty : t ≤ ν y := le_of_not_gt hbelow
    have hy : y ≠ 0 := by
      intro hz
      rw [hz,(ν.gauge.2.2.1 0).mpr rfl] at hty
      exact (not_le.mpr ht) hty
    have ha : 0 < s-t := sub_pos.mpr hts
    have hav : s-t ≤ ν y := by linarith
    have hb := wordDerivative_radial_gap_bound H.fields (H.fields_smooth G) hν
      (quasiballProfile_contDiff t s) driftWeight κ M hκ hM I hy ha hav
      (fun K => hgauge K y hy)
      (fun term hterm => hprofile term.1 (radialWordTerms_profile_pos driftWeight I hI hterm)
        t s hts (ν y))
    have hc : radialWordBoundConstant κ M I ≤ C I := by
      exact le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)
    have hb' := hb.trans (mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg ha.le _))
    simpa only [drift_wordWeight_eq,Real.rpow_neg ha.le,Real.rpow_natCast,div_eq_mul_inv] using hb'

end RothschildStein.H3
