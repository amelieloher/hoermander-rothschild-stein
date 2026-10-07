-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.FlowVariational
public import RothschildStein.G1.Liouville
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Analysis.Matrix.Normed

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators Matrix.Norms.Elementwise

namespace RothschildStein.G1

/-- Continuous coefficient-matrix map in the standard coordinate basis
(BB Prop 1.2, pp. 3–4). -/
def coefficientMatrix (N : ℕ) :
    ((Fin N → ℝ) →L[ℝ] (Fin N → ℝ)) →L[ℝ] Matrix (Fin N) (Fin N) ℝ :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.pi fun j =>
    (ContinuousLinearMap.proj i).comp
      (ContinuousLinearMap.apply ℝ (Fin N → ℝ) (Pi.single j 1))

/-- Composition is matrix multiplication in standard coordinates
(BB Prop 1.2, pp. 3–4). -/
theorem coefficientMatrix_comp {N : ℕ}
    (A B : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ)) :
    coefficientMatrix N (A.comp B) = coefficientMatrix N A * coefficientMatrix N B :=
  LinearMap.toMatrix'_comp A.toLinearMap B.toLinearMap

/-- Liouville's formula for the spatial Jacobian has the coordinate
divergence in its exponent (BB Prop 2.22, pp. 89–90). -/
theorem localFlow_liouville_of_joint_contDiff {N : ℕ} {Ω U : Set (Fin N → ℝ)}
    (hΩ : IsOpen Ω) (hU : IsOpen U) {Z : (Fin N → ℝ) → (Fin N → ℝ)}
    (hZ : ContDiffOn ℝ (⊤ : ℕ∞) Z Ω) {τ : ℝ} (hτ : 0 < τ)
    (Φ : ((Fin N → ℝ) × ℝ) → (Fin N → ℝ))
    (hjoint : ContDiffOn ℝ (⊤ : ℕ∞) Φ (U ×ˢ Ioo (-τ) τ))
    (hΦ : ∀ x ∈ U, Φ (x, 0) = x ∧ ∀ v ∈ Ioo (-τ) τ,
      HasDerivAt (fun w => Φ (x, w)) (Z (Φ (x, v))) v ∧ Φ (x, v) ∈ Ω)
    {x : Fin N → ℝ} (hx : x ∈ U) {t : ℝ} (ht : t ∈ Ioo (-τ) τ) :
    (coefficientMatrix N (fderiv ℝ (fun y => Φ (y, t)) x)).det =
      Real.exp (∫ v in 0..t, ∑ i : Fin N,
        (fderiv ℝ Z (Φ (x, v)) (Pi.single i 1)) i) := by
  let J := fun v => fderiv ℝ (fun y => Φ (y, v)) x
  let A := fun v => coefficientMatrix N (fderiv ℝ Z (Φ (x, v)))
  let M := fun v => coefficientMatrix N (J v)
  have hA : ContinuousOn A (Ioo (-τ) τ) := by
    intro v hv
    have hZat := hZ.contDiffAt (hΩ.mem_nhds ((hΦ x hx).2 v hv).2)
    have hDZ := (hZat.fderiv_right (m := 0) (by simp)).continuousAt
    have hα := ((hΦ x hx).2 v hv).1.continuousAt
    have hDZcurve : ContinuousAt (fun w => fderiv ℝ Z (Φ (x, w))) v :=
      hDZ.comp (f := fun w => Φ (x, w)) hα
    exact ((coefficientMatrix N).continuous.continuousAt.comp hDZcurve).continuousWithinAt
  have hM : ∀ v ∈ Ioo (-τ) τ, HasDerivAt M (A v * M v) v := by
    intro v hv
    have hd : HasDerivAt J ((fderiv ℝ Z (Φ (x, v))).comp (J v)) v :=
      localFlow_variational_of_joint_contDiff hΩ hU hZ Φ hjoint
      (fun y hy => (hΦ y hy).2) hx hv
    have hmatrix := HasFDerivAt.comp_hasDerivAt v (l := (coefficientMatrix N)) (f := J)
      ((coefficientMatrix N).hasFDerivAt (x := J v)) hd
    convert hmatrix using 1
    all_goals first | rfl | exact (coefficientMatrix_comp (fderiv ℝ Z (Φ (x, v))) (J v)).symm
  have hzero : (0 : ℝ) ∈ Ioo (-τ) τ := ⟨by linarith, hτ⟩
  have hM₀ : M 0 = 1 := by
    have heq : (fun y => Φ (y, 0)) =ᶠ[𝓝 x] id := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact (hΦ y hy).1
    have hJ₀ : J 0 = ContinuousLinearMap.id ℝ (Fin N → ℝ) :=
      heq.fderiv_eq.trans fderiv_id
    change coefficientMatrix N (J 0) = 1
    rw [hJ₀]
    exact LinearMap.toMatrix'_id
  exact matrixODE_det_eq_exp_integral hA hzero hM hM₀ ht

/-- Under joint smoothness: the actual spatial Jacobian is
strictly positive (BB pp. 89–90). -/
theorem localFlow_jacobian_pos_of_joint_contDiff {N : ℕ} {Ω U : Set (Fin N → ℝ)}
    (hΩ : IsOpen Ω) (hU : IsOpen U) {Z : (Fin N → ℝ) → (Fin N → ℝ)}
    (hZ : ContDiffOn ℝ (⊤ : ℕ∞) Z Ω) {τ : ℝ} (hτ : 0 < τ)
    (Φ : ((Fin N → ℝ) × ℝ) → (Fin N → ℝ))
    (hjoint : ContDiffOn ℝ (⊤ : ℕ∞) Φ (U ×ˢ Ioo (-τ) τ))
    (hΦ : ∀ x ∈ U, Φ (x, 0) = x ∧ ∀ v ∈ Ioo (-τ) τ,
      HasDerivAt (fun w => Φ (x, w)) (Z (Φ (x, v))) v ∧ Φ (x, v) ∈ Ω)
    {x : Fin N → ℝ} (hx : x ∈ U) {t : ℝ} (ht : t ∈ Ioo (-τ) τ) :
    0 < (coefficientMatrix N (fderiv ℝ (fun y => Φ (y, t)) x)).det := by
  rw [localFlow_liouville_of_joint_contDiff hΩ hU hZ hτ Φ hjoint hΦ hx ht]
  exact Real.exp_pos _

end RothschildStein.G1
