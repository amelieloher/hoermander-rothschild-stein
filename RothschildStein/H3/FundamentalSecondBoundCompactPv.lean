-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.ConvolutionFormulas
public import RothschildStein.H3.DriftWeightTwoCases
public import RothschildStein.H3.DriftWordNormBound
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory
open scoped ENNReal BigOperators

/-- the actual smooth fundamental potential has the complete
global weight-two estimate from principal-value Lp bounds. Drift follows
from Lv=f; compact support is required of the source, not the potential. -/
theorem fundamental_second_bound_of_compact_principalValue_bounds {n q : ℕ}
    (G : HomogeneousGroup n) (H : H1.StandingHypotheses G q)
    (K : H1.FundamentalKernel G H) (hQ : 2 < (G.homogeneousDimension : ℝ))
    (p : ℝ≥0∞) (hp : 1 ≤ p) (M : ℝ) (hM : 0 ≤ M)
    (hLp : ∀ i j : Fin q, ∀ f : (Fin n → ℝ) → ℝ, ContDiff ℝ 1 f → HasCompactSupport f →
      eLpNorm (H1.principalValueConvolution G H.norm
        (fieldDerivative (H.fields i.succ) (fieldDerivative (H.fields j.succ) K)) f) p volume ≤
          ENNReal.ofReal M*eLpNorm f p volume) :
    ∃ C₉ : ℝ, 0 < C₉ ∧ ∀ f : (Fin n → ℝ) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
      ∀ I : List (Fin (q+1)), wordWeight driftWeight I = 2 →
        eLpNorm (wordDerivative H.fields I (G2.groupConvolution G f K)) p volume ≤
          ENNReal.ofReal C₉*eLpNorm f p volume := by
  classical
  obtain ⟨c,_,hform⟩ := convolution_formulas_of_fundamental_kernel G H K hQ
  let B : ℝ := ∑ i : Fin q, ∑ j : Fin q, |c i j|
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _))
  have hc : ∀ i j, |c i j| ≤ B := by
    intro i j
    exact (Finset.single_le_sum (f := fun l : Fin q => |c i l|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun l : Fin q => ∑ t : Fin q, |c l t|)
        (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (Finset.mem_univ i))
  have hMB : 0 ≤ M+B := add_nonneg hM hB
  have hq : 0 ≤ (q : ℝ) := Nat.cast_nonneg _
  have hqMB := mul_nonneg hq hMB
  refine ⟨(q+1 : ℝ)*(M+B+1), by positivity, ?_⟩
  intro f hf hsf I hI
  obtain ⟨_,heq,_,_,hsecond,_,_,_⟩ := hform f hf hsf
  have hhor : ∀ i j : Fin q,
      eLpNorm (wordDerivative H.fields [i.succ,j.succ] (G2.groupConvolution G f K)) p volume ≤
        ENNReal.ofReal (M+B)*eLpNorm f p volume := by
    intro i j
    simp only [wordDerivative]
    rw [hsecond i j]
    have hs : eLpNorm (fun x => c i j*f x) p volume ≤ ENNReal.ofReal B*eLpNorm f p volume := by
      change eLpNorm (c i j • f) p volume ≤ _
      rw [eLpNorm_const_smul, Real.enorm_eq_ofReal_abs]
      exact mul_le_mul' (ENNReal.ofReal_le_ofReal (hc i j)) le_rfl
    calc
      _ ≤ eLpNorm (H1.principalValueConvolution G H.norm
          (fieldDerivative (H.fields i.succ) (fieldDerivative (H.fields j.succ) K)) f) p volume+
          eLpNorm (fun x => c i j*f x) p volume := eLpNorm_add_le hp
      _ ≤ ENNReal.ofReal M*eLpNorm f p volume+ENNReal.ofReal B*eLpNorm f p volume :=
        add_le_add (hLp i j f (hf.of_le (by simp)) hsf) hs
      _ = _ := by rw [ENNReal.ofReal_add hM hB, add_mul]
  rcases drift_word_weight_two I hI with hz | ⟨i,j,hij⟩
  · subst I
    have hd := drift_word_norm_le_of_horizontal_squares H.fields (G2.groupConvolution G f K) p hp hMB
      (fun i => by rw [heq]; exact hhor i i)
    rw [heq] at hd
    exact hd.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal (by nlinarith)) le_rfl)
  · subst I
    exact (hhor i j).trans (mul_le_mul' (ENNReal.ofReal_le_ofReal (by nlinarith)) le_rfl)

end RothschildStein.H3
