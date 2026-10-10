-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.MeasureTheory.Integral.Prod

/-!
# Representatives of integrals of L²-valued functions

Integration of a Bochner integrable L²-valued curve agrees almost everywhere with integration
of jointly measurable representatives. Local integration is a bounded linear map, obtained as
the adjoint of the inclusion of constant functions supported in a set of finite measure.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter

namespace HeatKernel

variable {α E : Type*} [MeasurableSpace α] {μ : Measure α}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The bounded linear inclusion of vectors as functions constant on a set of finite measure. -/
def indicatorConstL2 {s : Set α} (hs : MeasurableSet s) (hμs : μ s ≠ ⊤) :
    E →L[ℝ] Lp E 2 μ :=
  LinearMap.mkContinuous
    { toFun := indicatorConstLp 2 hs hμs
      map_add' := fun x y => (indicatorConstLp_add (p := 2) (hs := hs) (hμs := hμs) (c := x) (c' := y)).symm
      map_smul' := by
        intro c x
        apply Lp.ext
        filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hμs) (c := c • x),
          indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hμs) (c := x),
          Lp.coeFn_smul c (indicatorConstLp 2 hs hμs x)] with a hc hx hadd
        simp only [hc, hadd, hx, RingHom.id_apply, Pi.smul_apply]
        by_cases ha : a ∈ s <;> simp [ha] }
    (μ.real s ^ (1 / (2 : ℝ))) (by
      intro x
      change ‖indicatorConstLp 2 hs hμs x‖ ≤ _
      rw [norm_indicatorConstLp (by norm_num) (by norm_num)]
      norm_num [mul_comm])

/-- Integration over a set of finite measure is a bounded linear map on Bochner L². -/
def setIntegralL2 {s : Set α} (hs : MeasurableSet s) (hμs : μ s ≠ ⊤) :
    Lp E 2 μ →L[ℝ] E := (indicatorConstL2 hs hμs).adjoint

/-- The local integration map is the usual set integral of a representative. -/
theorem setIntegralL2_apply {s : Set α} (hs : MeasurableSet s) (hμs : μ s ≠ ⊤)
    (u : Lp E 2 μ) : setIntegralL2 hs hμs u = ∫ a in s, u a ∂μ := by
  apply ext_inner_left ℝ
  intro x
  rw [setIntegralL2, ContinuousLinearMap.adjoint_inner_right]
  change inner ℝ (indicatorConstLp 2 hs hμs x) u = _
  exact L2.inner_indicatorConstLp_eq_inner_setIntegral ℝ hs hμs x u

omit [InnerProductSpace ℝ E] [CompleteSpace E] in
/-- The integral of the norm on a finite-measure set is bounded by a constant times the L² norm. -/
theorem integral_norm_le_setIntegralL2_norm {s : Set α} (hs : MeasurableSet s)
    (hμs : μ s ≠ ⊤) (u : Lp E 2 μ) :
    (∫ a in s, ‖u a‖ ∂μ) ≤ ‖setIntegralL2 (E := ℝ) hs hμs‖ * ‖u‖ := by
  let v : Lp ℝ 2 μ := (Lp.memLp u).norm.toLp (fun a => ‖u a‖)
  have hv : ‖v‖ = ‖u‖ := by
    rw [Lp.norm_def, eLpNorm_congr_ae (Lp.memLp u).norm.coeFn_toLp, eLpNorm_norm _ (Lp.aestronglyMeasurable u)]
    rfl
  have hint : setIntegralL2 hs hμs v = ∫ a in s, ‖u a‖ ∂μ := by
    rw [setIntegralL2_apply]
    exact integral_congr_ae ((Lp.memLp u).norm.coeFn_toLp.restrict (s := s))
  calc
    _ ≤ ‖∫ a in s, ‖u a‖ ∂μ‖ := le_abs_self _
    _ ≤ ‖setIntegralL2 (E := ℝ) hs hμs‖ * ‖v‖ := by
      rw [← hint]
      exact (setIntegralL2 hs hμs).le_opNorm v
    _ = _ := by rw [hv]

/-- An integral of L²-valued functions is represented by the pointwise Bochner integral
whenever jointly strongly measurable representatives are given. -/
theorem integral_L2_ae_eq_integral {β : Type*} [MeasurableSpace β] {ν : Measure β}
    [SigmaFinite μ] [SFinite ν] {F : β → Lp E 2 μ} (hF : Integrable F ν)
    {f : β → α → E} (hf : StronglyMeasurable (Function.uncurry f))
    (hrep : ∀ᵐ b ∂ν, F b =ᵐ[μ] f b) :
    (∫ b, F b ∂ν) =ᵐ[μ] fun a => ∫ b, f b a ∂ν := by
  have hprod (s : Set α) (hs : MeasurableSet s) (hμs : μ s < ⊤) :
      Integrable (Function.uncurry f) (ν.prod (μ.restrict (s := s))) := by
    have hm : AEStronglyMeasurable (Function.uncurry f) (ν.prod (μ.restrict (s := s))) :=
      hf.aestronglyMeasurable
    apply (integrable_prod_iff hm).mpr
    constructor
    · filter_upwards [hrep] with b hb
      exact (integrableOn_Lp_of_measure_ne_top (F b) (by norm_num) hμs.ne).congr
        (hb.restrict (s := s))
    · apply (hF.norm.const_mul ‖setIntegralL2 (E := ℝ) hs hμs.ne‖).mono'
        hm.norm.integral_prod_right'
      filter_upwards [hrep] with b hb
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      change (∫ a in s, ‖f b a‖ ∂μ) ≤ _
      have heq : (fun a => ‖F b a‖) =ᵐ[μ.restrict s] (fun a => ‖f b a‖) :=
        (hb.restrict (s := s)).fun_comp norm
      rw [← integral_congr_ae heq]
      exact integral_norm_le_setIntegralL2_norm hs hμs.ne (F b)
  apply ae_eq_of_forall_setIntegral_eq_of_sigmaFinite
  · intro s _ hμs
    exact integrableOn_Lp_of_measure_ne_top _ (by norm_num) hμs.ne
  · intro s hs hμs
    exact (hprod s hs hμs).integral_prod_right
  · intro s hs hμs
    rw [← setIntegralL2_apply hs hμs.ne, ← (setIntegralL2 hs hμs.ne).integral_comp_comm hF]
    calc
      _ = ∫ b, ∫ a in s, f b a ∂μ ∂ν := by
        apply integral_congr_ae
        filter_upwards [hrep] with b hb
        rw [setIntegralL2_apply]
        exact integral_congr_ae (hb.restrict (s := s))
      _ = ∫ a in s, ∫ b, f b a ∂ν ∂μ := integral_integral_swap (hprod s hs hμs)

end HeatKernel
