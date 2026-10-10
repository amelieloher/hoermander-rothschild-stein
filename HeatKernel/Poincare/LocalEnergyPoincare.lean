-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Poincare.LocalSymmetricTruncation
public import HeatKernel.Poincare.TruncatedGradientBounds
public import HeatKernel.Poincare.TruncationPoincareLimit
public import HeatKernel.Poincare.WeakBallPoincare

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set Filter MeasureTheory TopologicalSpace RothschildStein
open scoped ENNReal Topology BigOperators
namespace HeatKernel

/-- The same-ball horizontal Poincaré inequality holds for local energy functions
with only L¹ values and an Lp horizontal gradient, including p = 1. -/
theorem exists_uniform_local_energy_poincare_constant {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    {κ p : ℝ} (hκ : 240 < κ) (k : ℕ) (hk : 0 < k)
    (hscale : 2 * κ + 22 ≤ (k : ℝ)) (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (x : Fin N → ℝ) (r : ℝ), 0 < r →
      ∀ (f : (Fin N → ℝ) → ℝ) (g : Fin q → (Fin N → ℝ) → ℝ),
        MemLocalEnergy ⟨horizontalBall (G.horizontalFields hq) x r,
          isOpen_horizontalBall G hq hqpos hspan x r⟩ (G.horizontalFields hq) f →
        IntegrableOn f (horizontalBall (G.horizontalFields hq) x r) →
        MemLp (fun y => Real.sqrt (∑ i, g i y ^ 2)) (ENNReal.ofReal p)
          (volume.restrict (horizontalBall (G.horizontalFields hq) x r)) →
        (∀ i, hasWeakWordDeriv (G.horizontalFields hq)
          ⟨horizontalBall (G.horizontalFields hq) x r,
            isOpen_horizontalBall G hq hqpos hspan x r⟩ [i] f (g i)) →
        eLpNorm (fun y => f y - ⨍ z in horizontalBall (G.horizontalFields hq) x r, f z)
          (ENNReal.ofReal p) (volume.restrict (horizontalBall (G.horizontalFields hq) x r)) ≤
          ENNReal.ofReal (C * r) * eLpNorm (fun y => Real.sqrt (∑ i, g i y ^ 2))
            (ENNReal.ofReal p) (volume.restrict (horizontalBall (G.horizontalFields hq) x r)) := by
  obtain ⟨C, hC, hPI⟩ := exists_uniform_weak_horizontalPoincare_ball_constant
    G hq hqpos hspan hw hκ k hk hscale hp
  refine ⟨C, hC, ?_⟩
  intro x r hr f g hf hfi hg hfg
  let B := horizontalBall (G.horizontalFields hq) x r
  let U : Opens (Fin N → ℝ) := ⟨B, isOpen_horizontalBall G hq hqpos hspan x r⟩
  let _ : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.mpr
    (volume_horizontalBall_lt_top G hq hqpos hspan hw x hr.le).ne
  apply eLpNorm_mean_oscillation_le_of_symmetric_truncations hfi
  intro n
  let F := fun y => max (-(n : ℝ)) (min (f y) n)
  let H := fun i y => if |f y| ≤ (n : ℝ) then g i y else 0
  have ht := hf.symmetric_truncation U (G.horizontalFields hq)
    (G.horizontalFields_contDiff hq) hfg (Nat.cast_nonneg n)
  have hFm : MemLp F (ENNReal.ofReal p) (volume.restrict B) := by
    apply MemLp.of_bound (aestronglyMeasurable_symmetric_truncation hf.1 n) n
    exact Eventually.of_forall fun y => by
      simpa only [Real.norm_eq_abs] using abs_symmetric_truncation_le_level (Nat.cast_nonneg n) (f y)
  have hHm : ∀ i, MemLp (H i) (ENNReal.ofReal p) (volume.restrict B) := by
    intro i
    apply hg.mono' (ht.2 i).2.1.aestronglyMeasurable
    exact Eventually.of_forall fun y => by
      split_ifs
      · simpa only [Real.norm_eq_abs] using abs_le_finite_gradient_length (fun j => g j y) i
      · simpa only [norm_zero] using Real.sqrt_nonneg (∑ j, g j y ^ 2)
  have h := hPI x r hr F H hFm hHm ht.2
  have hgrad : eLpNorm (fun y => Real.sqrt (∑ i, H i y ^ 2)) (ENNReal.ofReal p)
      (volume.restrict B) ≤ eLpNorm (fun y => Real.sqrt (∑ i, g i y ^ 2))
        (ENNReal.ofReal p) (volume.restrict B) := by
    apply eLpNorm_mono_ae (memLp_finite_gradient_length hHm).aestronglyMeasurable
    exact Eventually.of_forall fun y => by
      simp only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
      exact finite_gradient_length_ite_le (fun i => g i y) (|f y| ≤ (n : ℝ))
  exact h.trans (mul_le_mul_right hgrad _)

end HeatKernel
