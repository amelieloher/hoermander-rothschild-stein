-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.FlowLiouville
public import Hormander.Interface.EuclideanDivergence
public import Mathlib.Analysis.Calculus.Deriv.Slope

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter
open scoped Topology BigOperators Matrix.Norms.Elementwise
namespace RothschildStein.S
variable {n : ℕ}

/-- G1's coordinate determinant is the determinant used
by Mathlib's change-of-variables formula (BB pp. 89–90). -/
theorem coefficientMatrix_det_eq (A : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) :
    (G1.coefficientMatrix n A).det = A.det := by
  exact LinearMap.det_toMatrix' A.toLinearMap

/-- The actual flow Jacobian solves the scalar divergence
ODE. This reuses the G1 variational equation and determinant derivative;
it requires no matrix mean-value claim (BB (2.28)–(2.30), pp. 89–90). -/
theorem flow_jacobian_hasDerivAt
    {Ω U : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) (hU : IsOpen U)
    {X : (Fin n → ℝ) → (Fin n → ℝ)}
    (hX : ContDiffOn ℝ (⊤ : ℕ∞) X Ω) {τ : ℝ}
    (Φ : ((Fin n → ℝ) × ℝ) → (Fin n → ℝ))
    (hjoint : ContDiffOn ℝ (⊤ : ℕ∞) Φ (U ×ˢ Ioo (-τ) τ))
    (hΦ : ∀ x ∈ U,∀ t ∈ Ioo (-τ) τ,
      HasDerivAt (fun v => Φ (x,v)) (X (Φ (x,t))) t ∧ Φ (x,t) ∈ Ω)
    {x : Fin n → ℝ} (hx : x ∈ U) {t : ℝ} (ht : t ∈ Ioo (-τ) τ) :
    HasDerivAt (fun v => (fderiv ℝ (fun y => Φ (y,v)) x).det)
      (Hormander.Interface.euclideanDivergence X (Φ (x,t)) *
        (fderiv ℝ (fun y => Φ (y,t)) x).det) t := by
  let J := fun v => fderiv ℝ (fun y => Φ (y,v)) x
  have hd : HasDerivAt J ((fderiv ℝ X (Φ (x,t))).comp (J t)) t :=
    G1.localFlow_variational_of_joint_contDiff hΩ hU hX Φ hjoint hΦ hx ht
  have hm := HasFDerivAt.comp_hasDerivAt t (l := G1.coefficientMatrix n) (f := J)
    ((G1.coefficientMatrix n).hasFDerivAt (x := J t)) hd
  have hm' : HasDerivAt (fun v => G1.coefficientMatrix n (J v))
      (G1.coefficientMatrix n (fderiv ℝ X (Φ (x,t))) * G1.coefficientMatrix n (J t)) t := by
    simpa only [Function.comp_def,G1.coefficientMatrix_comp] using hm
  have H := G1.matrixODE_det_hasDerivAt hm'
  simpa only [coefficientMatrix_det_eq] using! H

/-- The initial spatial Jacobian is one on an open
starting domain (BB (2.28), p. 89). -/
theorem flow_jacobian_eq_one_at_zero
    {U : Set (Fin n → ℝ)} (hU : IsOpen U)
    (Φ : ((Fin n → ℝ) × ℝ) → (Fin n → ℝ))
    (hi : ∀ x ∈ U,Φ (x,0) = x) {x : Fin n → ℝ} (hx : x ∈ U) :
    (fderiv ℝ (fun y => Φ (y,0)) x).det = 1 := by
  have he : (fun y => Φ (y,0)) =ᶠ[𝓝 x] id := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact hi y hy
  rw [he.fderiv_eq,fderiv_id]
  exact LinearMap.det_id

/-- The inverse-time Jacobian has derivative minus the
Euclidean divergence at zero (BB (2.29)–(2.30), p. 90). -/
theorem flow_inverse_jacobian_hasDerivAt_zero
    {Ω U : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) (hU : IsOpen U)
    {X : (Fin n → ℝ) → (Fin n → ℝ)}
    (hX : ContDiffOn ℝ (⊤ : ℕ∞) X Ω) {τ : ℝ} (hτ : 0 < τ)
    (Φ : ((Fin n → ℝ) × ℝ) → (Fin n → ℝ))
    (hjoint : ContDiffOn ℝ (⊤ : ℕ∞) Φ (U ×ˢ Ioo (-τ) τ))
    (hΦ : ∀ x ∈ U,Φ (x,0) = x ∧ ∀ t ∈ Ioo (-τ) τ,
      HasDerivAt (fun v => Φ (x,v)) (X (Φ (x,t))) t ∧ Φ (x,t) ∈ Ω)
    {x : Fin n → ℝ} (hx : x ∈ U) :
    HasDerivAt (fun v => (fderiv ℝ (fun y => Φ (y,-v)) x).det)
      (-Hormander.Interface.euclideanDivergence X x) 0 := by
  have h0 : (0 : ℝ) ∈ Ioo (-τ) τ := ⟨by linarith,hτ⟩
  have hd := flow_jacobian_hasDerivAt hΩ hU hX Φ hjoint
    (fun y hy => (hΦ y hy).2) hx h0
  rw [(hΦ x hx).1,flow_jacobian_eq_one_at_zero hU Φ
    (fun y hy => (hΦ y hy).1) hx,mul_one] at hd
  have hd' : HasDerivAt (fun v => (fderiv ℝ (fun y => Φ (y,v)) x).det)
      (Hormander.Interface.euclideanDivergence X x) (- (0 : ℝ)) := by
    simpa only [neg_zero] using hd
  have H := hd'.scomp (h := fun v : ℝ => -v) 0 (hasDerivAt_id 0).neg
  simpa only [neg_zero,Function.comp_def,smul_eq_mul,mul_neg_one,neg_one_mul] using H

/-- The inverse Jacobian difference quotient converges
to minus divergence, with the actual change-of-variables determinant
(BB (2.30), p. 90; as follows from the variational equation). -/
theorem flow_inverse_jacobian_quotient_tendsto
    {Ω U : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) (hU : IsOpen U)
    {X : (Fin n → ℝ) → (Fin n → ℝ)}
    (hX : ContDiffOn ℝ (⊤ : ℕ∞) X Ω) {τ : ℝ} (hτ : 0 < τ)
    (Φ : ((Fin n → ℝ) × ℝ) → (Fin n → ℝ))
    (hjoint : ContDiffOn ℝ (⊤ : ℕ∞) Φ (U ×ˢ Ioo (-τ) τ))
    (hΦ : ∀ x ∈ U,Φ (x,0) = x ∧ ∀ t ∈ Ioo (-τ) τ,
      HasDerivAt (fun v => Φ (x,v)) (X (Φ (x,t))) t ∧ Φ (x,t) ∈ Ω)
    {x : Fin n → ℝ} (hx : x ∈ U) :
    Tendsto (fun t => ((fderiv ℝ (fun y => Φ (y,-t)) x).det-1)/t)
      (𝓝[≠] 0) (𝓝 (-Hormander.Interface.euclideanDivergence X x)) := by
  have H := (flow_inverse_jacobian_hasDerivAt_zero hΩ hU hX hτ Φ hjoint hΦ hx).tendsto_slope_zero
  simpa only [zero_add,neg_zero,flow_jacobian_eq_one_at_zero hU Φ
    (fun y hy => (hΦ y hy).1) hx,smul_eq_mul,div_eq_mul_inv,mul_comm] using H

/-- The actual change-of-variables Jacobian is positive,
so its absolute value equals itself. G1's proved Liouville formula applies
without a nonvanishing assumption on the field (BB p. 90). -/
theorem flow_jacobian_pos
    {Ω U : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) (hU : IsOpen U)
    {X : (Fin n → ℝ) → (Fin n → ℝ)}
    (hX : ContDiffOn ℝ (⊤ : ℕ∞) X Ω) {τ : ℝ} (hτ : 0 < τ)
    (Φ : ((Fin n → ℝ) × ℝ) → (Fin n → ℝ))
    (hjoint : ContDiffOn ℝ (⊤ : ℕ∞) Φ (U ×ˢ Ioo (-τ) τ))
    (hΦ : ∀ x ∈ U,Φ (x,0) = x ∧ ∀ t ∈ Ioo (-τ) τ,
      HasDerivAt (fun v => Φ (x,v)) (X (Φ (x,t))) t ∧ Φ (x,t) ∈ Ω)
    {x : Fin n → ℝ} (hx : x ∈ U) {t : ℝ} (ht : t ∈ Ioo (-τ) τ) :
    0 < (fderiv ℝ (fun y => Φ (y,t)) x).det := by
  simpa only [coefficientMatrix_det_eq] using
    G1.localFlow_jacobian_pos_of_joint_contDiff hΩ hU hX hτ Φ hjoint hΦ hx ht

end RothschildStein.S
