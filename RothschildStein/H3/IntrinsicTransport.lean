-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.IntrinsicCurveExistence
public import RothschildStein.S.IntrinsicUniqueness
public import Mathlib.Analysis.Calculus.Deriv.Comp

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set Filter TopologicalSpace
open scoped Topology
namespace RothschildStein.H3
variable {N : ℕ}

/-- curve transport. A smooth coordinate map with tangent
covariance transports an integral curve after rescaling its time parameter.
This argument applies before any differentiability of the scalar input. -/
theorem integralCurve_scaled_transport
    (φ : (Fin N → ℝ) → (Fin N → ℝ))
    (X Y : (Fin N → ℝ) → (Fin N → ℝ)) {c : ℝ} (hc : c ≠ 0)
    (hφ : Differentiable ℝ φ)
    (hcov : ∀ x, fderiv ℝ φ x (X x) = c • Y (φ x))
    {γ : ℝ → (Fin N → ℝ)} (hγ : IsIntegralCurveAt γ (fun _ => X) 0) :
    IsIntegralCurveAt (fun t => φ (γ (c⁻¹ * t))) (fun _ => Y) 0 := by
  have ht : Tendsto (fun t : ℝ => c⁻¹ * t) (𝓝 0) (𝓝 0) := by
    simpa using (show Continuous (fun t : ℝ => c⁻¹ * t) from
      continuous_const.mul continuous_id).continuousAt (x := (0 : ℝ)) |>.tendsto
  filter_upwards [ht.eventually hγ] with t hgt
  have hd := (hφ (γ (c⁻¹ * t))).hasFDerivAt.comp_hasDerivAt t
    (hgt.scomp t ((hasDerivAt_id t).const_mul c⁻¹))
  simpa only [smul_smul, ContinuousLinearMap.map_smul, hcov,
    inv_mul_cancel₀ hc, one_smul, mul_one, Function.comp_def] using hd

/-- missing intrinsic step. Pullback along a smooth coordinate
map multiplies the fixed intrinsic derivative by its tangent covariance
factor. Neither the scalar input nor its derivative is assumed classically
smooth (BB p. 339; source gap in the intrinsic scaling application). -/
theorem hasIntrinsicDeriv_scaled_pullback
    (Ω : Opens (Fin N → ℝ))
    (φ : (Fin N → ℝ) → (Fin N → ℝ))
    (X Y : (Fin N → ℝ) → (Fin N → ℝ)) {c : ℝ} (hc : c ≠ 0)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hX : ContDiff ℝ (⊤ : ℕ∞) X)
    (hcov : ∀ x, fderiv ℝ φ x (X x) = c • Y (φ x))
    {f g : (Fin N → ℝ) → ℝ} (hf : hasIntrinsicDeriv Ω Y f g) :
    hasIntrinsicDeriv ⟨φ ⁻¹' (Ω : Set (Fin N → ℝ)),
      Ω.isOpen.preimage hφ.continuous⟩ X (f ∘ φ) (fun x => c * g (φ x)) := by
  let V : Opens (Fin N → ℝ) := ⟨φ ⁻¹' (Ω : Set (Fin N → ℝ)),
    Ω.isOpen.preimage hφ.continuous⟩
  intro x hx
  refine ⟨S.exists_intrinsic_integral_curve V X hX.contDiffOn hx, ?_⟩
  intro γ hzero hγ hmem
  have ht : Tendsto (fun t : ℝ => c⁻¹ * t) (𝓝 0) (𝓝 0) := by
    simpa using (show Continuous (fun t : ℝ => c⁻¹ * t) from
      continuous_const.mul continuous_id).continuousAt (x := (0 : ℝ)) |>.tendsto
  have hδ := integralCurve_scaled_transport φ X Y hc
    (hφ.differentiable (by simp)) hcov hγ
  have hd := (hf (φ x) hx).2 (fun t => φ (γ (c⁻¹ * t)))
    (by simp only [mul_zero, hzero]) hδ (ht.eventually hmem)
  have hd0 : HasDerivAt (fun t => f (φ (γ (c⁻¹ * t)))) (g (φ x))
      (c * (0 : ℝ)) := by simpa only [mul_zero] using hd
  have he := hd0.comp 0 ((hasDerivAt_id (0 : ℝ)).const_mul c)
  convert he using 1
  · funext t
    simp only [Function.comp_apply, inv_mul_cancel_left₀ hc]
  · simp only [mul_one, mul_comm]

/-- Constant scalar multiplication preserves the exact fixed
intrinsic derivative predicate, including its curve existence certificate. -/
theorem hasIntrinsicDeriv_const_mul
    (Ω : Opens (Fin N → ℝ)) (X : (Fin N → ℝ) → (Fin N → ℝ))
    {f g : (Fin N → ℝ) → ℝ} (hf : hasIntrinsicDeriv Ω X f g) (a : ℝ) :
    hasIntrinsicDeriv Ω X (fun x => a * f x) (fun x => a * g x) := by
  intro x hx
  exact ⟨(hf x hx).1, fun γ hzero hγ hmem =>
    ((hf x hx).2 γ hzero hγ hmem).const_mul a⟩

end RothschildStein.H3
