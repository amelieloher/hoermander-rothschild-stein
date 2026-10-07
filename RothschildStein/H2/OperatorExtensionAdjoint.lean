-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.OperatorLpExtension
public import Mathlib.MeasureTheory.Function.Holder

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace RothschildStein.H2
variable {X : Type*} [MeasurableSpace X]

/-- L² adjointness extends to the actual conjugate Lᵖ spaces
by continuity of the Hölder pairing and density of Lᵖ ∩ L²
(BB p. 326). -/
theorem operator_extensions_adjoint (μ : Measure X) [IsFiniteMeasure μ]
    {p q : ℝ} (hpq : p.HolderConjugate q)
    [Fact (1 ≤ ENNReal.ofReal p)] [Fact (1 ≤ ENNReal.ofReal q)]
    (T Ts : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ)
    (Tp : Lp ℝ (ENNReal.ofReal p) μ →L[ℝ] Lp ℝ (ENNReal.ofReal p) μ)
    (Tsq : Lp ℝ (ENNReal.ofReal q) μ →L[ℝ] Lp ℝ (ENNReal.ofReal q) μ)
    (hadj : ∀ v w : Lp ℝ 2 μ, (∫ x, (T v) x * w x ∂μ) = ∫ x, v x * (Ts w) x ∂μ)
    (hTp : ∀ v : lpL2Intersection μ (ENNReal.ofReal p),
      (fun x => (Tp (v : Lp ℝ (ENNReal.ofReal p) μ)) x) =ᵐ[μ]
        fun x => (T (lpL2ToL2 μ (ENNReal.ofReal p) v)) x)
    (hTsq : ∀ w : lpL2Intersection μ (ENNReal.ofReal q),
      (fun x => (Tsq (w : Lp ℝ (ENNReal.ofReal q) μ)) x) =ᵐ[μ]
        fun x => (Ts (lpL2ToL2 μ (ENNReal.ofReal q) w)) x) :
    ∀ f : Lp ℝ (ENNReal.ofReal p) μ, ∀ g : Lp ℝ (ENNReal.ofReal q) μ,
      (∫ x, (Tp f) x * g x ∂μ) = ∫ x, f x * (Tsq g) x ∂μ := by
  let : ENNReal.HolderConjugate (ENNReal.ofReal p) (ENNReal.ofReal q) :=
    ⟨by simpa using hpq.inv_add_inv_ennreal⟩
  let B := (ContinuousLinearMap.mul ℝ ℝ).lpPairing μ (ENNReal.ofReal p) (ENNReal.ofReal q)
  have heq : ∀ v : lpL2Intersection μ (ENNReal.ofReal p),
      ∀ w : lpL2Intersection μ (ENNReal.ofReal q),
      B (Tp v) w = B v (Tsq w) := by
    intro v w
    rw [ContinuousLinearMap.lpPairing_eq_integral, ContinuousLinearMap.lpPairing_eq_integral]
    simp only [ContinuousLinearMap.mul_apply']
    calc
      _ = ∫ x, (T (lpL2ToL2 μ (ENNReal.ofReal p) v)) x *
          (lpL2ToL2 μ (ENNReal.ofReal q) w) x ∂μ := by
        apply integral_congr_ae
        filter_upwards [hTp v, w.property.coeFn_toLp] with x hx hy
        change (lpL2ToL2 μ (ENNReal.ofReal q) w) x = (w : Lp ℝ (ENNReal.ofReal q) μ) x at hy
        rw [hx, hy]
      _ = ∫ x, (lpL2ToL2 μ (ENNReal.ofReal p) v) x *
          (Ts (lpL2ToL2 μ (ENNReal.ofReal q) w)) x ∂μ := hadj _ _
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [v.property.coeFn_toLp, hTsq w] with x hx hy
        change (lpL2ToL2 μ (ENNReal.ofReal p) v) x = (v : Lp ℝ (ENNReal.ofReal p) μ) x at hx
        rw [hx, hy]
  have hfixed : ∀ v : lpL2Intersection μ (ENNReal.ofReal p),
      ∀ g : Lp ℝ (ENNReal.ofReal q) μ, B (Tp v) g = B v (Tsq g) := by
    intro v
    have hh := (lpL2Intersection_dense μ (ENNReal.ofReal q) ENNReal.ofReal_ne_top).equalizer
      (B (Tp v)).continuous ((B v).comp Tsq).continuous (by funext w; exact heq v w)
    exact congrFun hh
  intro f g
  have hh := (lpL2Intersection_dense μ (ENNReal.ofReal p) ENNReal.ofReal_ne_top).equalizer
    ((B.flip g).comp Tp).continuous (B.flip (Tsq g)).continuous (by funext v; exact hfixed v g)
  have h := congrFun hh f
  simpa only [B, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.lpPairing_eq_integral, ContinuousLinearMap.mul_apply'] using h

end RothschildStein.H2
