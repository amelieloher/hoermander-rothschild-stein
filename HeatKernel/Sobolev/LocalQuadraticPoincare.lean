-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Poincare.LocalEnergyPoincare
public import HeatKernel.Sobolev.QuadraticPoincareConversion
import Mathlib.Tactic
import all Mathlib.Basic.Real.Basic

/-! Uniform same-ball quadratic estimates for local horizontal energy functions. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace RothschildStein
open scoped ENNReal BigOperators
namespace HeatKernel

/-- The local horizontal energy domain satisfies a uniform same-ball quadratic
Poincaré estimate with the literal spatial average. -/
theorem exists_uniform_local_energy_quadratic_poincare_constant {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1) :
    ∃ P : ℝ, 0 < P ∧ ∀ (x : Fin N → ℝ) (r : ℝ), 0 < r →
      ∀ (f : (Fin N → ℝ) → ℝ) (g : Fin q → (Fin N → ℝ) → ℝ),
      MemLocalEnergy ⟨horizontalBall (G.horizontalFields hq) x r,
        isOpen_horizontalBall G hq hqpos hspan x r⟩ (G.horizontalFields hq) f →
      IntegrableOn f (horizontalBall (G.horizontalFields hq) x r) →
      MemLp (fun y => Real.sqrt (∑ i, g i y ^ 2)) 2
        (volume.restrict (horizontalBall (G.horizontalFields hq) x r)) →
      (∀ i, hasWeakWordDeriv (G.horizontalFields hq)
        ⟨horizontalBall (G.horizontalFields hq) x r,
          isOpen_horizontalBall G hq hqpos hspan x r⟩ [i] f (g i)) →
      (∫⁻ y in horizontalBall (G.horizontalFields hq) x r,
        ENNReal.ofReal ((f y - ⨍ z in horizontalBall (G.horizontalFields hq) x r, f z) ^ 2)) ≤
      ENNReal.ofReal P * ENNReal.ofReal r ^ 2 *
        ∫⁻ y in horizontalBall (G.horizontalFields hq) x r, ENNReal.ofReal (∑ i, g i y ^ 2) := by
  obtain ⟨C, hC, hPI⟩ := exists_uniform_local_energy_poincare_constant G hq hqpos hspan hw
    (κ := 1000) (p := 2) (by norm_num) 2030 (by norm_num) (by norm_num) (by norm_num)
  refine ⟨C ^ 2, sq_pos_of_pos hC, ?_⟩
  intro x r hr f g hf hfi hg hfg
  have hg' : MemLp (fun y => Real.sqrt (∑ i, g i y ^ 2)) (ENNReal.ofReal 2)
      (volume.restrict (horizontalBall (G.horizontalFields hq) x r)) := by
    simpa using hg
  have h := Sobolev.lintegral_sq_le_of_eLpNorm_two_le
    (f := fun y => f y - ⨍ z in horizontalBall (G.horizontalFields hq) x r, f z)
    (by simpa only [Pi.sub_def] using hfi.aestronglyMeasurable.sub aestronglyMeasurable_const) hg.aestronglyMeasurable hC.le
    (by simpa using hPI x r hr f g hf hfi hg' hfg)
  simpa only [Pi.sub_apply, Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg (g i _)))] using h

end HeatKernel
