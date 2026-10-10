-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Semigroup.GeneratorMultipliers
public import HeatKernel.Semigroup.BoundedHeatOperators

/-! # Strong convergence of the generator error

Uniform boundedness and a weighted estimate extend convergence from the resolvent range
to the whole Hilbert space.
-/

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology
namespace HeatKernel
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The bounded error operator in the resolvent-range difference quotient. -/
def generatorErrorOperator (R : E →L[ℂ] E) (t : ℝ) : E →L[ℂ] E :=
  cfc (generatorMultiplierError t) R

theorem norm_generatorErrorOperator_le (R : E →L[ℂ] E)
    (hspec : spectrum ℝ R ⊆ Icc (0 : ℝ) 1) {t : ℝ} (ht : 0 < t) :
    ‖generatorErrorOperator R t‖ ≤ 1 := by
  apply norm_cfc_le zero_le_one
  intro r hr
  have h := generatorMultiplierError_mem_Icc ht (hspec hr)
  simpa only [Real.norm_eq_abs, abs_of_nonneg h.1] using h.2

theorem norm_generatorErrorOperator_mul_le (R : E →L[ℂ] E) (hR : IsSelfAdjoint R)
    (hspec : spectrum ℝ R ⊆ Icc (0 : ℝ) 1) {t : ℝ} (ht : 0 < t) :
    ‖generatorErrorOperator R t * R‖ ≤ t := by
  unfold generatorErrorOperator
  conv_lhs => arg 1; arg 2; rw [← cfc_id' ℝ R hR]
  rw [← cfc_mul (generatorMultiplierError t) (fun r : ℝ => r) R
    (continuous_generatorMultiplierError t).continuousOn continuous_id.continuousOn]
  apply norm_cfc_le ht.le
  intro r hr
  have hr' := hspec hr
  have he := (generatorMultiplierError_mem_Icc ht hr').1
  simpa only [Real.norm_eq_abs, abs_mul, abs_of_nonneg he, abs_of_nonneg hr'.1, mul_comm]
    using weighted_generatorMultiplierError_le ht hr'

theorem tendsto_generatorErrorOperator_apply_of_denseRange (R : E →L[ℂ] E)
    (hR : IsSelfAdjoint R) (hspec : spectrum ℝ R ⊆ Icc (0 : ℝ) 1)
    (hdense : DenseRange R) (x : E) :
    Tendsto (fun t : ℝ => generatorErrorOperator R t x) (𝓝[>] 0) (𝓝 0) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨y, hy⟩ := hdense.exists_dist_lt x (show 0 < ε / 2 by positivity)
  refine ⟨ε / (2 * (‖y‖ + 1)), by positivity, ?_⟩
  intro t ht hdist
  have ht' : 0 < t := ht
  have hsmall : t * ‖y‖ < ε / 2 := by
    rw [Real.dist_eq, sub_zero, abs_of_pos ht'] at hdist
    have hprod := (lt_div_iff₀ (show 0 < 2 * (‖y‖ + 1) by positivity)).mp hdist
    nlinarith [norm_nonneg y]
  rw [dist_zero_right]
  have hdecomp : generatorErrorOperator R t x =
      generatorErrorOperator R t (x - R y) + (generatorErrorOperator R t * R) y := by
    rw [map_sub, mul_apply_eq_comp]
    abel
  rw [hdecomp]
  calc
    _ ≤ ‖generatorErrorOperator R t (x - R y)‖ + ‖(generatorErrorOperator R t * R) y‖ := norm_add_le _ _
    _ ≤ ‖x - R y‖ + t * ‖y‖ := by
      apply add_le_add
      · exact ((generatorErrorOperator R t).le_opNorm _).trans
          (by simpa using (mul_le_mul_of_nonneg_right (norm_generatorErrorOperator_le R hspec ht')
            (norm_nonneg (x - R y))))
      · exact ((generatorErrorOperator R t * R).le_opNorm y).trans
          (mul_le_mul_of_nonneg_right (norm_generatorErrorOperator_mul_le R hR hspec ht') (norm_nonneg y))
    _ < ε := by rw [← dist_eq_norm]; linarith

end HeatKernel
