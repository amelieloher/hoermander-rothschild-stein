-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Poincare.WeakHorizontalPoincare
public import HeatKernel.Poincare.IncreasingSetPoincare
public import HeatKernel.Poincare.BallExhaustion

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set Filter MeasureTheory TopologicalSpace RothschildStein
open scoped ENNReal Topology BigOperators
namespace HeatKernel

/-- The same-ball horizontal Poincaré inequality holds for weak horizontal Lp data on
the open ball itself, with the uniform smooth coefficient. -/
theorem exists_uniform_weak_horizontalPoincare_ball_constant
    {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    {κ p : ℝ} (hκ : 240 < κ) (k : ℕ) (hk : 0 < k)
    (hscale : 2 * κ + 22 ≤ (k : ℝ)) (hp : 1 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (x : Fin N → ℝ) (r : ℝ), 0 < r →
      ∀ (f : (Fin N → ℝ) → ℝ) (g : Fin q → (Fin N → ℝ) → ℝ),
        MemLp f (ENNReal.ofReal p) (volume.restrict (horizontalBall (G.horizontalFields hq) x r)) →
        (∀ i, MemLp (g i) (ENNReal.ofReal p)
          (volume.restrict (horizontalBall (G.horizontalFields hq) x r))) →
        (∀ i, hasWeakWordDeriv (G.horizontalFields hq)
          ⟨horizontalBall (G.horizontalFields hq) x r, isOpen_horizontalBall G hq hqpos hspan x r⟩
          [i] f (g i)) →
        eLpNorm (fun y => f y - ⨍ z in horizontalBall (G.horizontalFields hq) x r, f z)
          (ENNReal.ofReal p) (volume.restrict (horizontalBall (G.horizontalFields hq) x r)) ≤
          ENNReal.ofReal (C * r) * eLpNorm (fun y => Real.sqrt (∑ i, g i y ^ 2))
            (ENNReal.ofReal p) (volume.restrict (horizontalBall (G.horizontalFields hq) x r)) := by
  obtain ⟨C, hC, hPI⟩ := exists_uniform_weak_horizontalPoincare_neighborhood_constant
    G hq hqpos hspan hw hκ k hk hscale hp
  refine ⟨C, hC, ?_⟩
  intro x r hr f g hf hg hfg
  let B := horizontalBall (G.horizontalFields hq) x r
  let Ω : Opens (Fin N → ℝ) := ⟨B, isOpen_horizontalBall G hq hqpos hspan x r⟩
  let _ : IsFiniteMeasure (volume.restrict B) := isFiniteMeasure_restrict.mpr
    (volume_horizontalBall_lt_top G hq hqpos hspan hw x hr.le).ne
  obtain ⟨s, hs, hmono, hlim⟩ := exists_increasing_positive_radii hr
  let A := fun n => horizontalBall (G.horizontalFields hq) x (s n)
  have hAM : ∀ n, MeasurableSet (A n) := fun n =>
    (isOpen_horizontalBall G hq hqpos hspan x (s n)).measurableSet
  have hAmono : Monotone A := fun m n hmn y hy =>
    lt_of_lt_of_le hy (ENNReal.ofReal_le_ofReal (hmono hmn))
  have hAU : (⋃ n, A n) = B :=
    iUnion_horizontalBall_eq_of_tendsto (G.horizontalFields hq) x (fun n => (hs n).2.le) hlim
  have hclosure : ∀ n, closure (A n) ⊆ Ω := fun n =>
    closure_horizontalBall_subset_of_radius_lt G hq hqpos hspan x (hs n).2
  have hAB : ∀ n, A n ⊆ B := fun n => subset_closure.trans (hclosure n)
  have hpE : 1 ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp
  apply eLpNorm_mean_oscillation_le_of_increasing_sets hAM hAmono hAU
    (volume_horizontalBall_lt_top G hq hqpos hspan hw x hr.le).ne
    (volume_horizontalBall_pos G hq hqpos hspan x hr).ne' (MemLp.integrable hpE hf)
  intro n
  have hh := hPI x (s n) (hs n).1 Ω (hclosure n) f g hf hg hfg
  have hcoeff : ENNReal.ofReal (C * s n) ≤ ENNReal.ofReal (C * r) :=
    ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hs n).2.le hC.le)
  have hgrad := eLpNorm_mono_measure (fun y => Real.sqrt (∑ i, g i y ^ 2))
    (Measure.restrict_mono (μ := volume) (hAB n) le_rfl) (p := ENNReal.ofReal p)
  exact hh.trans ((mul_le_mul_left hcoeff _).trans (mul_le_mul_right hgrad _))

end HeatKernel
