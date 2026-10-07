-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.LocalFlows
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.FDeriv.Symmetric
public import Mathlib.Analysis.Calculus.Deriv.Mul

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology

namespace RothschildStein.G1

/-- Under joint smoothness of the local flow, the spatial derivative
satisfies the variational differential equation. The proof uses symmetry
of the second derivative, not a matrix mean-value assertion
(BB Prop 1.2, pp. 3–4; see also Prop 2.22, pp. 89–90). -/
theorem localFlow_variational_of_joint_contDiff {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {Ω U : Set E} (hΩ : IsOpen Ω) (hU : IsOpen U)
    {Z : E → E} (hZ : ContDiffOn ℝ (⊤ : ℕ∞) Z Ω) {τ : ℝ}
    (Φ : (E × ℝ) → E)
    (hjoint : ContDiffOn ℝ (⊤ : ℕ∞) Φ (U ×ˢ Ioo (-τ) τ))
    (hΦ : ∀ x ∈ U, ∀ v ∈ Ioo (-τ) τ,
      HasDerivAt (fun w => Φ (x, w)) (Z (Φ (x, v))) v ∧ Φ (x, v) ∈ Ω)
    {x : E} (hx : x ∈ U) {t : ℝ} (ht : t ∈ Ioo (-τ) τ) :
    HasDerivAt (fun v => fderiv ℝ (fun y => Φ (y, v)) x)
      ((fderiv ℝ Z (Φ (x, t))).comp (fderiv ℝ (fun y => Φ (y, t)) x)) t := by
  let L := fderiv ℝ Φ
  let A := fderiv ℝ L (x, t)
  let i : E →L[ℝ] (E × ℝ) := ContinuousLinearMap.inl ℝ E ℝ
  let e : E × ℝ := (0, 1)
  have hpt := (hU.prod isOpen_Ioo).mem_nhds (show (x, t) ∈ U ×ˢ Ioo (-τ) τ from ⟨hx, ht⟩)
  have hs := hjoint.contDiffAt hpt
  have hd : HasFDerivAt L A (x, t) :=
    ((hs.fderiv_right (m := 1) (by simp)).differentiableAt (by simp)).hasFDerivAt
  have hJ : ∀ y ∈ U, ∀ v ∈ Ioo (-τ) τ,
      fderiv ℝ (fun y => Φ (y, v)) y = (L (y, v)).comp i := by
    intro y hy v hv
    exact (((hjoint.contDiffAt ((hU.prod isOpen_Ioo).mem_nhds ⟨hy, hv⟩)).differentiableAt
      (by simp)).hasFDerivAt.comp y (hasFDerivAt_prodMk_left y v)).fderiv
  have htime : ∀ p ∈ U ×ˢ Ioo (-τ) τ, L p e = Z (Φ p) := by
    intro p hp
    have hdtime := (((hjoint.contDiffAt ((hU.prod isOpen_Ioo).mem_nhds hp)).differentiableAt
      (by simp)).hasFDerivAt.comp p.2 (hasFDerivAt_prodMk_right p.1 p.2)).hasDerivAt
    exact hdtime.unique (hΦ p.1 hp.1 p.2 hp.2).1
  have heq : (fun p => L p e) =ᶠ[𝓝 (x, t)] (fun p => Z (Φ p)) := by
    filter_upwards [hpt] with p hp
    exact htime p hp
  have happ : HasFDerivAt (fun p => L p e)
      ((ContinuousLinearMap.apply ℝ E e).comp A) (x, t) :=
    (ContinuousLinearMap.apply ℝ E e).hasFDerivAt.comp (x, t) hd
  have hz := ((hZ.contDiffAt (hΩ.mem_nhds (hΦ x hx t ht).2)).differentiableAt
    (by simp)).hasFDerivAt.comp (x, t) (hs.differentiableAt (by simp)).hasFDerivAt
  have hA := (happ.congr_of_eventuallyEq heq.symm).unique hz
  have hsym := hs.isSymmSndFDerivAt (by simp)
  have hcoeff : (A e).comp i = (fderiv ℝ Z (Φ (x, t))).comp ((L (x, t)).comp i) := by
    ext v
    change A e (i v) = fderiv ℝ Z (Φ (x, t)) (L (x, t) (i v))
    rw [hsym e (i v)]
    exact congrArg (fun M : (E × ℝ) →L[ℝ] E => M (i v)) hA
  have hcurve : HasDerivAt (fun v => L (x, v)) (A e) t :=
    (hd.comp t (hasFDerivAt_prodMk_right x t)).hasDerivAt
  have hcurveJ := hcurve.clm_comp (hasDerivAt_const t i)
  simp only [ContinuousLinearMap.comp_zero, add_zero] at hcurveJ
  have hJeq : (fun v => fderiv ℝ (fun y => Φ (y, v)) x) =ᶠ[𝓝 t]
      (fun v => (L (x, v)).comp i) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with v hv
    exact hJ x hx v hv
  rw [hcoeff, ← hJ x hx t ht] at hcurveJ
  exact hcurveJ.congr_of_eventuallyEq hJeq

end RothschildStein.G1
