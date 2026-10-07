-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.DriftVariation
public import Mathlib.Topology.Order.LeftRightNhds

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology ENNReal BigOperators

namespace RothschildStein.G1

/-- Passing from bounds for actual curves to the fixed
control infimum uses a continuous monotone cost; no minimizing curve is
assumed (BB Thms 1.54/1.56, pp. 36–37). -/
theorem variation_le_controlDistance_of_curve_bound {m n : ℕ}
    {Ω : Set (Fin n → ℝ)} {w : Fin m → ℕ+}
    {X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)} {x y : Fin n → ℝ}
    (hfinite : controlDistance Ω w X x y ≠ ∞) {A : ℝ} (C : ℝ → ℝ)
    (hC : Continuous C) (hmono : MonotoneOn C (Ici 0))
    (hcurve : ∀ δ γ, isControlledCurve Ω w X δ γ → γ 0 = x → γ 1 = y → A ≤ C δ) :
    A ≤ C (controlDistance Ω w X x y).toReal := by
  let d := (controlDistance Ω w X x y).toReal
  apply ge_of_tendsto ((hC.continuousAt : ContinuousAt C d).tendsto.mono_left
    (show 𝓝[>] d ≤ 𝓝 d from inf_le_left))
  filter_upwards [self_mem_nhdsWithin] with r hr
  obtain ⟨δ, hδ, hδr, γ, hγ, hγ0, hγ1⟩ :=
    exists_controlledCurve_of_controlDistance_lt
      ((ENNReal.lt_ofReal_iff_toReal_lt hfinite).mpr hr)
  exact (hcurve δ γ hγ hγ0 hγ1).trans
    (hmono hδ.le (hδ.le.trans hδr.le) hδr.le)

/-- Global drift variation for C¹ functions with globally bounded
field derivatives. Compact support is used only when replacing these bounds
by bounds on its containing ball. The control distance is assumed finite
(BB Thm 1.56, p. 37; Prop 2.18(i), pp. 84–85). -/
theorem global_drift_variation_of_finite_distance {q n : ℕ}
    {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω)
    {X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ)}
    {f : (Fin n → ℝ) → ℝ} (hf : ContDiffOn ℝ 1 f Ω)
    {H D : ℝ} (hH0 : 0 ≤ H) (hD0 : 0 ≤ D)
    (hH : ∀ z ∈ Ω, Real.sqrt (∑ i : Fin q, (fderiv ℝ f z (X i.succ z)) ^ 2) ≤ H)
    (hD : ∀ z ∈ Ω, |fderiv ℝ f z (X 0 z)| ≤ D)
    {x y : Fin n → ℝ} (hfinite : controlDistance Ω driftWeight X x y ≠ ∞) :
    |f y - f x| ≤ Real.sqrt q * (controlDistance Ω driftWeight X x y).toReal * H +
      (controlDistance Ω driftWeight X x y).toReal ^ 2 * D := by
  apply variation_le_controlDistance_of_curve_bound hfinite
    (fun δ => Real.sqrt q * δ * H + δ ^ 2 * D) (by fun_prop)
  · intro a ha b hb hab
    have h1 := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hab (Real.sqrt_nonneg q)) hH0
    have h2 := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha hab 2) hD0
    exact add_le_add h1 h2
  · intro δ γ hγ hγ0 hγ1
    simpa only [hγ0, hγ1] using controlledCurve_drift_variation_le hΩ hf hγ
      (fun t ht => hH _ (hγ.2.2.1 ht)) (fun t ht => hD _ (hγ.2.2.1 ht))

/-- The global drift-free variation bound has coefficient √q.
The bound applies when the control distance is finite
(BB Prop 2.18(i), pp. 84–85). -/
theorem global_noDrift_variation_of_finite_distance {q n : ℕ}
    {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω)
    {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)}
    {f : (Fin n → ℝ) → ℝ} (hf : ContDiffOn ℝ 1 f Ω)
    {H : ℝ} (hH0 : 0 ≤ H)
    (hH : ∀ z ∈ Ω, Real.sqrt (∑ i, (fderiv ℝ f z (X i z)) ^ 2) ≤ H)
    {x y : Fin n → ℝ} (hfinite : controlDistance Ω noDriftWeight X x y ≠ ∞) :
    |f y - f x| ≤ Real.sqrt q * (controlDistance Ω noDriftWeight X x y).toReal * H := by
  apply variation_le_controlDistance_of_curve_bound hfinite
    (fun δ => Real.sqrt q * δ * H) (by fun_prop)
  · intro a ha b hb hab
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hab (Real.sqrt_nonneg q)) hH0
  · intro δ γ hγ hγ0 hγ1
    simpa only [hγ0, hγ1] using controlledCurve_noDrift_variation_le hΩ hf hγ
      (fun t ht => hH _ (hγ.2.2.1 ht))

end RothschildStein.G1
