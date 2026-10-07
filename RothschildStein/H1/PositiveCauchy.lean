-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Topology.Instances.RealVectorSpace
public import Mathlib.Topology.MetricSpace.Pseudo.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set
namespace RothschildStein.H1

/-- A continuous additive function on the nonnegative half-line
is linear. This supplies the scalar argument behind BB (6.39), p. 274. -/
theorem nonneg_additive_eq_mul {f : ℝ → ℝ} (hzero : f 0 = 0)
    (hadd : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → f (a + b) = f a + f b)
    (hcont : ContinuousWithinAt f (Ici 0) 0) :
    ∀ t : ℝ, 0 ≤ t → f t = t * f 1 := by
  let F : ℝ → ℝ := fun x => if 0 ≤ x then f x else -f (-x)
  have mixed (a b : ℝ) (ha : 0 ≤ a) (hb : ¬0 ≤ b) : F (a + b) = F a + F b := by
    have hb' : 0 ≤ -b := by linarith
    by_cases hs : 0 ≤ a + b
    · have hh := hadd (a + b) (-b) hs hb'
      have he : a + b + -b = a := by ring
      rw [he] at hh
      simp only [F, ite_eq_left hs, ite_eq_left ha, ite_eq_right hb]
      linarith
    · have hns : 0 ≤ -(a + b) := by linarith
      have hh := hadd a (-(a + b)) ha hns
      have he : a + -(a + b) = -b := by ring
      rw [he] at hh
      simp only [F, ite_eq_right hs, ite_eq_left ha, ite_eq_right hb]
      linarith
  let A : ℝ →+ ℝ :=
    { toFun := F
      map_zero' := by simp only [F, le_refl, ite_true, hzero]
      map_add' := by
        intro a b
        by_cases ha : 0 ≤ a
        · by_cases hb : 0 ≤ b
          · simp only [F, ite_eq_left ha, ite_eq_left hb, ite_eq_left (add_nonneg ha hb)]
            exact hadd a b ha hb
          · exact mixed a b ha hb
        · by_cases hb : 0 ≤ b
          · simpa only [add_comm] using mixed b a hb ha
          · have hs : ¬0 ≤ a + b := by linarith
            have hh := hadd (-a) (-b) (by linarith) (by linarith)
            have he : -(a + b) = -a + -b := by ring
            simp only [F, ite_eq_right ha, ite_eq_right hb, ite_eq_right hs, he, hh]
            ring }
  have hA0 : ContinuousAt A 0 := by
    apply Metric.continuousAt_iff.mpr
    intro ε hε
    obtain ⟨δ, hδ, hh⟩ := Metric.continuousWithinAt_iff.mp hcont ε hε
    refine ⟨δ, hδ, ?_⟩
    intro x hx
    have h := hh (abs_nonneg x) (by simpa only [dist_zero_right, Real.norm_eq_abs, abs_abs] using hx)
    rw [hzero] at h
    change dist (F x) (F 0) < ε
    by_cases hp : 0 ≤ x
    · simpa only [F, ite_eq_left hp, le_refl, ite_true, hzero, abs_of_nonneg hp] using h
    · simpa only [F, ite_eq_right hp, le_refl, ite_true, hzero, abs_of_neg (lt_of_not_ge hp),
        dist_zero_right, Real.norm_eq_abs, abs_neg] using h
  have hAc : Continuous A := continuous_of_continuousAt_zero A hA0
  have hl := map_real_smul A hAc
  intro t ht
  have he := hl t (1 : ℝ)
  change F (t * 1) = t * F 1 at he
  simpa only [mul_one, F, ite_eq_left ht, ite_eq_left (by norm_num : (0 : ℝ) ≤ 1)] using he

end RothschildStein.H1
