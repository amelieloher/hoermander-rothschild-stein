-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.QuasiRootBounds
public import RothschildStein.G3.FiniteTopology
@[expose] public section
noncomputable section
open Set Metric
open scoped BigOperators
namespace RothschildStein.G3

theorem contDiff_quasiExponentialLogAt_coefficients {a s : ℕ} {p : Fin a → ℕ+}
    (I : List (Fin a)) : ContDiff ℝ (⊤ : ℕ∞)
      (fun t => ((quasiExponentialLogAt (s := s) (p := p) t I).val : WordCoefficients a s p)) := by
  apply contDiff_pi.mpr
  intro J
  exact (contDiff_id.pow (wordWeight p J.val)).mul contDiff_const

/-- Root parameters remain in a numerical interval for bounded coefficients. -/
theorem quasiCorrection_root_le_max {a : ℕ} (p : Fin a → ℕ+) (I : List (Fin a))
    (hne : I ≠ []) {b B : ℝ} (hb : |b| ≤ B) :
    |b| ^ ((wordWeight p I : ℝ)⁻¹) ≤ max 1 B := by
  have hk : 1 ≤ wordWeight p I := by
    have hl := List.length_pos_iff.mpr hne
    have hw := length_le_weight p I
    omega
  have hkR : (1 : ℝ) ≤ wordWeight p I := by exact_mod_cast hk
  have hi : 0 ≤ (wordWeight p I : ℝ)⁻¹ := by positivity
  by_cases hsmall : |b| ≤ 1
  · exact (Real.rpow_le_one (abs_nonneg b) hsmall hi).trans (le_max_left _ _)
  · have hh := Real.rpow_le_rpow_of_exponent_le (le_of_lt (lt_of_not_ge hsmall))
        (show (wordWeight p I : ℝ)⁻¹ ≤ 1 by exact inv_le_one_of_one_le₀ hkR)
    rw [Real.rpow_one] at hh
    exact hh.trans (hb.trans (le_max_right _ _))

/-- All bounded-word corrections have a common finite numerical norm bound. -/
theorem exists_quasiCorrection_norm_bound {a s : ℕ} {p : Fin a → ℕ+} (B : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ I : BoundedWord a s p, I.val ≠ [] →
      ∀ b : ℝ, |b| ≤ B →
        ‖(signedQuasiCorrection (s := s) (p := p) b I.val).val‖ ≤ C := by
  classical
  have hex : ∀ I : BoundedWord a s p, ∃ C : ℝ, ∀ t ∈ Icc (0 : ℝ) (max 1 B),
      ‖((quasiExponentialLogAt (s := s) (p := p) t I.val).val : WordCoefficients a s p)‖ ≤ C := by
    intro I
    obtain ⟨C,hC⟩ := ((isCompact_Icc : IsCompact (Icc (0 : ℝ) (max 1 B))).image
      (contDiff_quasiExponentialLogAt_coefficients I.val).continuous).isBounded.exists_norm_le
    exact ⟨C,fun t ht => hC _ (mem_image_of_mem _ ht)⟩
  choose C hC using hex
  let D := 1+∑ I : BoundedWord a s p, |C I|
  refine ⟨D,by dsimp [D]; positivity,?_⟩
  intro I hne b hb
  have ht : |b| ^ ((wordWeight p I.val : ℝ)⁻¹) ∈ Icc (0 : ℝ) (max 1 B) :=
    ⟨Real.rpow_nonneg (abs_nonneg b) _,quasiCorrection_root_le_max p I.val hne hb⟩
  have he := hC I _ ht
  have hsum : |C I| ≤ ∑ J : BoundedWord a s p, |C J| :=
    Finset.single_le_sum (fun J _ => abs_nonneg (C J)) (Finset.mem_univ I)
  have hbound := (he.trans (le_abs_self _)).trans hsum
  unfold signedQuasiCorrection
  split
  · exact hbound.trans (by dsimp [D]; linarith)
  · change ‖-((quasiExponentialLogAt (s := s) (p := p)
        (|b| ^ ((wordWeight p I.val : ℝ)⁻¹)) I.val).val : WordCoefficients a s p)‖ ≤ D
    rw [norm_neg]
    exact hbound.trans (by dsimp [D]; linarith)
end RothschildStein.G3
