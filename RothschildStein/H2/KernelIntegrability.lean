-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.IntegralDefs
public import Mathlib.MeasureTheory.Integral.Lebesgue.Map
public import Mathlib.MeasureTheory.Integral.IntegrableOn

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal NNReal

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

omit [MetricSpace X] [BorelSpace X] in
/-- Measurability on the input domain suffices for absolute convergence. -/
theorem integrableOn_of_subtype_lintegral {μ : Measure X} {G : Set X} {g : X → ℝ}
    (hG : MeasurableSet G) (hm : AEStronglyMeasurable (fun y : G => g y) (μ.comap Subtype.val))
    (hi : (∫⁻ y in G, ENNReal.ofReal |g y| ∂μ) < ⊤) : IntegrableOn g G μ := by
  rw [integrableOn_iff_comap_subtypeVal hG]
  refine ⟨hm, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  simp only [Function.comp_def, ← ofReal_norm, Real.norm_eq_abs]
  rw [lintegral_subtype_comap hG (fun y => ENNReal.ofReal |g y|)]
  exact hi

omit [BorelSpace X] in
/-- A measurable product kernel is measurable in each fixed first variable. -/
theorem KernelClass.measurable_slice {μ : Measure X} {G : Set X} {β ν A S : ℝ}
    {K : X → X → ℝ} (hK : KernelClass μ G β ν A S K) {x : X} (hx : x ∈ G) :
    Measurable (fun y : G => K x y) :=
  hK.measurable.comp ((measurable_const (a := (⟨x, hx⟩ : G))).prodMk measurable_id)

/-- Hölder functions with positive exponent are measurable on their domain. -/
theorem BoundedHolder.measurable_subtype {δ : ℝ≥0} {G : Set X} {f : X → ℝ}
    (hf : BoundedHolder δ G f) (hδ : 0 < δ) : Measurable (fun y : G => f y) :=
  ((eHolderNorm_lt_top.mp hf.parts.2).holderWith.continuous hδ).measurable

omit [BorelSpace X] in
/-- The real radial weight agrees with its nonnegative
Lebesgue-integral form on positive finite-volume balls. -/
theorem ofReal_kernelWeight {μ : Measure X} {ν : ℝ} {x y : X}
    (hv : volumeAt μ x y ≠ 0) (hvt : volumeAt μ x y ≠ ⊤) :
    ENNReal.ofReal (kernelWeight μ ν x y) =
      ENNReal.ofReal (dist x y ^ ν) * (volumeAt μ x y)⁻¹ := by
  unfold kernelWeight
  rw [ENNReal.ofReal_div_of_pos (ENNReal.toReal_pos hv hvt), ENNReal.ofReal_toReal hvt,
    div_eq_mul_inv]

/-- Supported radial domination gives an explicit L1 bound.
BB Lemma 7.5 and Theorems 7.12, 7.14, pp. 297, 302, 305. -/
theorem DoublingPatch.lintegral_abs_le_inner (P : DoublingPatch X) {x : X} (hx : x ∈ P.S)
    {G : Set X} (hG : MeasurableSet G) {r α C : ℝ} (hr : 0 < r) (hrρ : r ≤ 6 * P.ρ)
    (hα : 0 < α) (hC : 0 ≤ C) {g : X → ℝ}
    (hsupp : ∀ y ∈ G, r ≤ dist x y → g y = 0)
    (hb : ∀ᵐ y ∂P.μ.restrict G, x ≠ y → |g y| ≤ C * kernelWeight P.μ α x y) :
    (∫⁻ y in G, ENNReal.ofReal |g y| ∂P.μ) ≤
      ENNReal.ofReal (C * volumeIntegralConstant P.C_D α * r ^ α) := by
  classical
  let w : X → ℝ≥0∞ := fun y => ENNReal.ofReal (dist x y ^ α) * (volumeAt P.μ x y)⁻¹
  have hae : ∀ᵐ y ∂P.μ, x ≠ y := by
    apply ae_iff.mpr
    have hs : {y : X | ¬ x ≠ y} = {x} := by
      ext y
      simp only [mem_ofPred_eq, not_ne_iff, mem_singleton_iff]
      exact eq_comm
    rw [hs]
    exact P.noAtoms x
  have hdom : ∀ᵐ y ∂P.μ, G.indicator (fun y => ENNReal.ofReal |g y|) y ≤
      (ball x r \ {x}).indicator (fun y => ENNReal.ofReal C * w y) y := by
    filter_upwards [hae, (ae_restrict_iff' hG).mp hb] with y hxy hb
    by_cases hy : y ∈ G
    swap
    · simp only [indicator_of_notMem hy, zero_le]
    by_cases hd : dist x y < r
    swap
    · simp only [indicator_of_mem hy, hsupp y hy (le_of_not_gt hd), abs_zero,
        ENNReal.ofReal_zero, zero_le]
    have hyB : y ∈ ball x r \ {x} :=
      ⟨by simpa only [mem_ball, dist_comm] using hd, by simpa only [mem_singleton_iff, eq_comm] using hxy⟩
    rw [indicator_of_mem hy, indicator_of_mem hyB]
    have hv := P.doubling x hx (dist x y) (dist_pos.mpr hxy) (hd.le.trans hrρ)
    have he := ENNReal.ofReal_le_ofReal (hb hy hxy)
    rw [ENNReal.ofReal_mul hC, ofReal_kernelWeight hv.1.ne' hv.2.1.ne] at he
    exact he
  calc
    _ = ∫⁻ y, G.indicator (fun y => ENNReal.ofReal |g y|) y ∂P.μ := (lintegral_indicator hG _).symm
    _ ≤ ∫⁻ y, (ball x r \ {x}).indicator (fun y => ENNReal.ofReal C * w y) y ∂P.μ := lintegral_mono_ae hdom
    _ = ENNReal.ofReal C * ∫⁻ y in ball x r \ {x}, w y ∂P.μ := by
      rw [lintegral_indicator (isOpen_ball.measurableSet.diff (measurableSet_singleton x)),
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal C * ENNReal.ofReal (volumeIntegralConstant P.C_D α * r ^ α) :=
      mul_le_mul_right (P.inner_volume_integral hx hα hr hrρ) _
    _ = _ := by rw [← ENNReal.ofReal_mul hC]; congr 1; ring

end RothschildStein.H2
