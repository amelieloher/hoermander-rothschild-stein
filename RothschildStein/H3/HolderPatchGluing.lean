-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.HolderSpaces

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set Metric
open scoped ENNReal NNReal
namespace RothschildStein.H3
variable {X ι : Type*} [MetricSpace X]

/-- A cover with a positive pair radius glues actual Hölder
bounds. Short pairs lie in one patch; long pairs use the supremum.
This is the Lebesgue-number repair of BB (2.23), p. 389. -/
theorem holder_patch_gluing {E : Set X} {P : ι → Set X} {f : X → ℝ}
    {α : ℝ≥0} {M ell : ℝ} (hM : 0 ≤ M) (hell : 0 < ell)
    (hcover : ∀ x ∈ E, ∃ i, x ∈ P i)
    (hpairs : ∀ x ∈ E, ∀ y ∈ E, dist x y < ell → ∃ i, x ∈ P i ∧ y ∈ P i)
    (hn : ∀ i, H2.boundedHolderNorm α (P i) f ≤ ENNReal.ofReal M) :
    H2.boundedHolderNorm α E f ≤
      ENNReal.ofReal ((1 + 2 / ell ^ (α : ℝ)) * M + M) := by
  have hfinite (i : ι) : H2.BoundedHolder α (P i) f :=
    (hn i).trans_lt ENNReal.ofReal_lt_top
  have hs (i : ι) : (H2.holderSup (P i) f).toReal ≤ M := by
    have he : H2.holderSup (P i) f ≤ ENNReal.ofReal M :=
      (le_add_right le_rfl).trans (hn i)
    simpa only [ENNReal.toReal_ofReal hM] using ENNReal.toReal_mono ENNReal.ofReal_ne_top he
  have hh (i : ι) : (H2.holderSemi α (P i) f).toReal ≤ M := by
    have he : H2.holderSemi α (P i) f ≤ ENNReal.ofReal M :=
      (le_add_left le_rfl).trans (hn i)
    simpa only [ENNReal.toReal_ofReal hM] using ENNReal.toReal_mono ENNReal.ofReal_ne_top he
  have hsup : ∀ x ∈ E, |f x| ≤ M := by
    intro x hx
    obtain ⟨i, hi⟩ := hcover x hx
    exact (H2.abs_le_holderSup (hfinite i).parts.1 hi).trans (hs i)
  have hsemi : ∀ x ∈ E, ∀ y ∈ E, |f x - f y| ≤
      ((1 + 2 / ell ^ (α : ℝ)) * M) * dist x y ^ (α : ℝ) := by
    intro x hx y hy
    by_cases hd : dist x y < ell
    · obtain ⟨i, hi, hj⟩ := hpairs x hx y hy hd
      have hb := H2.sub_le_holderSemi (hfinite i).parts.2 hi hj
      have hcoef : M ≤ (1 + 2 / ell ^ (α : ℝ)) * M := by
        nlinarith [div_nonneg (by norm_num : (0 : ℝ) ≤ 2) (Real.rpow_nonneg hell.le (α : ℝ))]
      exact hb.trans (mul_le_mul_of_nonneg_right ((hh i).trans hcoef)
        (Real.rpow_nonneg dist_nonneg (α : ℝ)))
    · have hpow : ell ^ (α : ℝ) ≤ dist x y ^ (α : ℝ) :=
        Real.rpow_le_rpow hell.le (le_of_not_gt hd) α.coe_nonneg
      have hc : 2 * M ≤ (2 / ell ^ (α : ℝ) * M) * dist x y ^ (α : ℝ) := by
        have hb := mul_le_mul_of_nonneg_left hpow
          (mul_nonneg (by positivity : 0 ≤ 2 / ell ^ (α : ℝ)) hM)
        have hp := (Real.rpow_pos_of_pos hell (α : ℝ)).ne'
        calc
          _ = (2 / ell ^ (α : ℝ) * M) * ell ^ (α : ℝ) := by field_simp
          _ ≤ _ := hb
      have hab : |f x - f y| ≤ 2 * M := by
        have ha := abs_add_le (f x) (-f y)
        rw [← sub_eq_add_neg, abs_neg] at ha
        linarith [hsup x hx, hsup y hy]
      exact hab.trans (hc.trans (by nlinarith [Real.rpow_nonneg (dist_nonneg (x := x) (y := y)) (α : ℝ)]))
  have hcoef : 0 ≤ (1 + 2 / ell ^ (α : ℝ)) * M := by positivity
  have hb := add_le_add (H2.holderSup_le_of_bound hsup)
    (H2.holderSemi_le_of_bound hcoef hsemi)
  exact hb.trans_eq (by rw [← ENNReal.ofReal_add hM hcoef]; congr 1; ring)

end RothschildStein.H3
