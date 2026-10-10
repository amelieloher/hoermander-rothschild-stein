-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.ContinuouslyDifferentiableComposition
public import HeatKernel.Form.EnergyLimits

/-!
# Limits of continuously differentiable contractions

Pointwise limits of continuously differentiable scalar contractions preserve the energy
domain and do not increase energy, provided the approximating contractions vanish at zero.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter TopologicalSpace
open scoped ENNReal NNReal Topology

namespace HeatKernel

/-- A scalar contraction represented by pointwise C¹ contraction approximants acts on the
closed energy domain without increasing energy. -/
theorem exists_energyGraph_comp_of_contDiff_approximation {N q : ℕ}
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (v : energyGraph (N := N) ⊤ X) {η : ℝ → ℝ} {a : ℕ → ℝ → ℝ}
    (hη : LipschitzWith 1 η) (hzero : η 0 = 0)
    (ha : ∀ n, ContDiff ℝ 1 (a n)) (ha0 : ∀ n, a n 0 = 0)
    (hab : ∀ n s, ‖deriv (a n) s‖ ≤ 1)
    (hat : ∀ s, Tendsto (fun n => a n s) atTop (𝓝 (η s))) :
    ∃ z : energyGraph (N := N) ⊤ X,
      energyInclusion ⊤ X z = hη.compLp hzero (energyInclusion ⊤ X v) ∧
      horizontalEnergy ⊤ X z z ≤ horizontalEnergy ⊤ X v v := by
  let U : Opens (Fin N → ℝ) := ⊤
  let μ := volume.restrict (U : Set (Fin N → ℝ))
  have hLip : ∀ n, LipschitzWith 1 (a n) := fun n =>
    lipschitzWith_of_nnnorm_deriv_le ((ha n).differentiable (by simp))
      (fun s => by exact_mod_cast hab n s)
  have hanorm : ∀ n s, ‖a n s‖ ≤ ‖s‖ := by
    intro n s
    simpa only [ha0, dist_zero_right, NNReal.coe_one, one_mul] using (hLip n).dist_le_mul s 0
  have hηnorm : ∀ s, ‖η s‖ ≤ ‖s‖ := by
    intro s
    simpa only [hzero, dist_zero_right, NNReal.coe_one, one_mul] using hη.dist_le_mul s 0
  choose w hwf hwg hwe using fun n =>
    exists_energyGraph_comp_contDiff_one_energy_le X hX v (ha n) (ha0 n)
      (C := 1) (by simpa using hab n)
  have hwf' : ∀ n, (w n : GradientSpace U q).fst =ᵐ[μ]
      fun x => a n ((v : GradientSpace U q).fst x) := by
    simpa only [μ, U, Opens.coe_top, Measure.restrict_univ] using hwf
  have hfnorm : ∀ n, ‖energyInclusion U X (w n)‖ ≤ ‖energyInclusion U X v‖ := by
    intro n
    apply Lp.norm_le_norm_of_ae_le
    filter_upwards [hwf' n] with x hx
    exact hx ▸ hanorm n ((v : GradientSpace U q).fst x)
  have hgnorm : ∀ n, ‖energyGradient U X (w n)‖ ≤ ‖energyGradient U X v‖ := by
    intro n
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    have H := hwe n
    simpa only [NNReal.coe_one, one_pow, one_mul, horizontalEnergy,
      real_inner_self_eq_norm_sq] using H
  have hlim : Tendsto (fun n => energyInclusion U X (w n)) atTop
      (𝓝 (hη.compLp hzero (energyInclusion U X v))) := by
    apply tendsto_L2_of_representatives hwf' (hη.coeFn_compLp hzero _)
    apply tendsto_eLpNorm_two_zero_of_dominated
      (fun n => ((hLip n).continuous.comp_aestronglyMeasurable
        (Lp.memLp (v : GradientSpace U q).fst).aestronglyMeasurable).sub
        (hη.continuous.comp_aestronglyMeasurable
          (Lp.memLp (v : GradientSpace U q).fst).aestronglyMeasurable))
      ((Lp.memLp (v : GradientSpace U q).fst).norm.const_mul 2)
    · intro n
      apply Eventually.of_forall
      intro x
      simp only [Pi.sub_apply, Real.norm_of_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
        (norm_nonneg ((v : GradientSpace U q).fst x)))]
      calc
        ‖a n ((v : GradientSpace U q).fst x) - η ((v : GradientSpace U q).fst x)‖
            ≤ ‖a n ((v : GradientSpace U q).fst x)‖ + ‖η ((v : GradientSpace U q).fst x)‖ :=
              norm_sub_le _ _
        _ ≤ 2 * ‖(v : GradientSpace U q).fst x‖ := by
          linarith [hanorm n ((v : GradientSpace U q).fst x), hηnorm ((v : GradientSpace U q).fst x)]
    · exact Eventually.of_forall fun x => by
        simpa only [Pi.sub_apply, sub_self] using
          (hat ((v : GradientSpace U q).fst x)).sub_const (η ((v : GradientSpace U q).fst x))
  obtain ⟨z, hz, hzg⟩ := exists_energyGraph_limit_of_bounds U X w
    (norm_nonneg _) (norm_nonneg _) hfnorm hgnorm hlim
  refine ⟨z, hz, ?_⟩
  simpa only [horizontalEnergy, real_inner_self_eq_norm_sq] using
    (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr hzg

end HeatKernel
