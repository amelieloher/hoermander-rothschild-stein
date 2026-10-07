-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.SmoothDependenceError

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology

namespace RothschildStein.G1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Compare linear equations with nearby coefficients.
The forcing is controlled by the coefficient difference times a bound on the
comparison solution (BB Proposition 1.2, p. 3). -/
theorem norm_linear_difference_le
    {A B : E →L[ℝ] E} {u v : E} {K ε R : ℝ}
    (hA : ‖A‖ ≤ K) (hAB : ‖A - B‖ ≤ ε) (hv : ‖v‖ ≤ R) (hε : 0 ≤ ε) :
    ‖A u - B v‖ ≤ K * ‖u - v‖ + ε * R := by
  have heq : A u - B v = A (u - v) + (A - B) v := by
    simp only [map_sub, sub_apply]
    abel
  rw [heq]
  exact (norm_add_le _ _).trans (add_le_add
    (((A.le_opNorm _).trans (mul_le_mul_of_nonneg_right hA (norm_nonneg _))))
    (((A - B).le_opNorm _).trans (mul_le_mul hAB hv (norm_nonneg _) hε)))

/-- Grönwall comparison for solutions of continuous linear
systems, including both signs of time (BB Proposition 1.2, p. 3). -/
theorem linear_curve_comparison_bound
    {A B : ℝ → E →L[ℝ] E} {W V : ℝ → E} {t K ε R : ℝ}
    (hε : 0 ≤ ε)
    (hW : ∀ v ∈ uIcc 0 t, HasDerivAt W (A v (W v)) v)
    (hV : ∀ v ∈ uIcc 0 t, HasDerivAt V (B v (V v)) v)
    (hinit : W 0 = V 0)
    (hA : ∀ v ∈ uIcc 0 t, ‖A v‖ ≤ K)
    (hAB : ∀ v ∈ uIcc 0 t, ‖A v - B v‖ ≤ ε)
    (hbound : ∀ v ∈ uIcc 0 t, ‖V v‖ ≤ R) :
    ‖W t - V t‖ ≤ gronwallBound 0 K (ε * R) |t| := by
  have hder : ∀ v ∈ uIcc 0 t,
      HasDerivAt (fun s => W s - V s) (A v (W v) - B v (V v)) v :=
    fun v hv => (hW v hv).sub (hV v hv)
  have hb : ∀ v ∈ uIcc 0 t,
      ‖A v (W v) - B v (V v)‖ ≤ K * ‖W v - V v‖ + ε * R :=
    fun v hv => norm_linear_difference_le (hA v hv) (hAB v hv) (hbound v hv) hε
  rcases le_total 0 t with ht | ht
  · have hs : Icc 0 t = uIcc 0 t := (uIcc_of_le ht).symm
    have he := norm_le_gronwallBound_of_norm_deriv_right_le (δ := 0) (K := K) (ε := ε * R)
      (fun v hv => (hder v (hs ▸ hv)).continuousAt.continuousWithinAt)
      (fun v hv => (hder v (hs ▸ Ico_subset_Icc_self hv)).hasDerivWithinAt)
      (by simp [hinit]) (fun v hv => hb v (hs ▸ Ico_subset_Icc_self hv)) t ⟨ht, le_rfl⟩
    simpa only [sub_zero, abs_of_nonneg ht] using he
  · have hs : ∀ v ∈ Icc 0 (-t), -v ∈ uIcc 0 t := by
      intro v hv
      rw [uIcc_of_ge ht]
      constructor <;> linarith [hv.1, hv.2]
    have hd : ∀ v ∈ Icc 0 (-t),
        HasDerivAt (fun s => W (-s) - V (-s)) (-(A (-v) (W (-v)) - B (-v) (V (-v)))) v := by
      intro v hv
      simpa only [Function.comp_def, neg_one_smul] using
        (hder (-v) (hs v hv)).scomp v (hasDerivAt_neg v)
    have he := norm_le_gronwallBound_of_norm_deriv_right_le (δ := 0) (K := K) (ε := ε * R)
      (fun v hv => (hd v hv).continuousAt.continuousWithinAt)
      (fun v hv => (hd v (Ico_subset_Icc_self hv)).hasDerivWithinAt)
      (by simp [hinit])
      (fun v hv => by simpa only [norm_neg] using hb (-v) (hs v (Ico_subset_Icc_self hv)))
      (-t) ⟨by linarith, le_rfl⟩
    simpa only [sub_zero, neg_neg, abs_of_nonpos ht] using he

end RothschildStein.G1
