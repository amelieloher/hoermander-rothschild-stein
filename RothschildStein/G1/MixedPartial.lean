-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.FlowVariational

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology

namespace RothschildStein.G1

/-- Spatial differentiation commutes with time differentiation for a
jointly smooth family with its actual time derivative specified. The codomain
may be a space of derivative tensors (BB Prop 1.2, pp. 3–4). -/
theorem spatial_derivative_hasDerivAt {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set E} (hU : IsOpen U) {a b : ℝ} {G H : (E × ℝ) → F}
    (hG : ContDiffOn ℝ (⊤ : ℕ∞) G (U ×ˢ Ioo a b))
    (hH : ContDiffOn ℝ (⊤ : ℕ∞) H (U ×ˢ Ioo a b))
    (hderiv : ∀ x ∈ U, ∀ v ∈ Ioo a b,
      HasDerivAt (fun w => G (x, w)) (H (x, v)) v)
    {x : E} (hx : x ∈ U) {t : ℝ} (ht : t ∈ Ioo a b) :
    HasDerivAt (fun v => fderiv ℝ (fun y => G (y, v)) x)
      (fderiv ℝ (fun y => H (y, t)) x) t := by
  let L := fderiv ℝ G
  let A := fderiv ℝ L (x, t)
  let i : E →L[ℝ] (E × ℝ) := ContinuousLinearMap.inl ℝ E ℝ
  let e : E × ℝ := (0, 1)
  have hpt := (hU.prod isOpen_Ioo).mem_nhds (show (x, t) ∈ U ×ˢ Ioo a b from ⟨hx, ht⟩)
  have hs := hG.contDiffAt hpt
  have hd : HasFDerivAt L A (x, t) :=
    ((hs.fderiv_right (m := 1) (by simp)).differentiableAt (by simp)).hasFDerivAt
  have hJ : ∀ y ∈ U, ∀ v ∈ Ioo a b,
      fderiv ℝ (fun y => G (y, v)) y = (L (y, v)).comp i := by
    intro y hy v hv
    exact (((hG.contDiffAt ((hU.prod isOpen_Ioo).mem_nhds ⟨hy, hv⟩)).differentiableAt
      (by simp)).hasFDerivAt.comp y (hasFDerivAt_prodMk_left y v)).fderiv
  have htime : ∀ p ∈ U ×ˢ Ioo a b, L p e = H p := by
    intro p hp
    have hdtime := (((hG.contDiffAt ((hU.prod isOpen_Ioo).mem_nhds hp)).differentiableAt
      (by simp)).hasFDerivAt.comp p.2 (hasFDerivAt_prodMk_right p.1 p.2)).hasDerivAt
    exact hdtime.unique (hderiv p.1 hp.1 p.2 hp.2)
  have heq : (fun p => L p e) =ᶠ[𝓝 (x, t)] H := by
    filter_upwards [hpt] with p hp
    exact htime p hp
  have happ : HasFDerivAt (fun p => L p e)
      ((ContinuousLinearMap.apply ℝ F e).comp A) (x, t) :=
    (ContinuousLinearMap.apply ℝ F e).hasFDerivAt.comp (x, t) hd
  have hHpt := (hH.contDiffAt hpt).differentiableAt (by simp)
  have hA := (happ.congr_of_eventuallyEq heq.symm).unique hHpt.hasFDerivAt
  have hsym := hs.isSymmSndFDerivAt (by simp)
  have hcoeff : (A e).comp i = fderiv ℝ (fun y => H (y, t)) x := by
    have hHslice : fderiv ℝ (fun y => H (y, t)) x = (fderiv ℝ H (x, t)).comp i :=
      (hHpt.hasFDerivAt.comp x (hasFDerivAt_prodMk_left x t)).fderiv
    rw [hHslice]
    ext v
    change A e (i v) = fderiv ℝ H (x, t) (i v)
    rw [hsym e (i v)]
    exact congrArg (fun M : (E × ℝ) →L[ℝ] F => M (i v)) hA
  have hcurve : HasDerivAt (fun v => L (x, v)) (A e) t :=
    (hd.comp t (hasFDerivAt_prodMk_right x t)).hasDerivAt
  have hcurveJ := hcurve.clm_comp (hasDerivAt_const t i)
  simp only [ContinuousLinearMap.comp_zero, add_zero] at hcurveJ
  have hJeq : (fun v => fderiv ℝ (fun y => G (y, v)) x) =ᶠ[𝓝 t]
      (fun v => (L (x, v)).comp i) := by
    filter_upwards [isOpen_Ioo.mem_nhds ht] with v hv
    exact hJ x hx v hv
  rw [hcoeff] at hcurveJ
  exact hcurveJ.congr_of_eventuallyEq hJeq

/-- The spatial derivative of a jointly smooth family is jointly
smooth, including when its codomain is a derivative-tensor space
(BB Prop 1.2, pp. 3–4). -/
theorem spatial_derivative_contDiffOn {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    {U : Set E} (hU : IsOpen U) {a b : ℝ} {G : (E × ℝ) → F}
    (hG : ContDiffOn ℝ (⊤ : ℕ∞) G (U ×ˢ Ioo a b)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun p => fderiv ℝ (fun y => G (y, p.2)) p.1)
      (U ×ˢ Ioo a b) := by
  apply (hU.prod isOpen_Ioo).contDiffOn_iff.mpr
  intro p hp
  have hs := hG.contDiffAt ((hU.prod isOpen_Ioo).mem_nhds hp)
  have hfull : ContDiffAt ℝ (⊤ : ℕ∞) (fderiv ℝ G) p := hs.fderiv_right (by simp)
  have hclm := hfull.continuousLinearMap_comp
    ((ContinuousLinearMap.compL ℝ E (E × ℝ) F).flip (ContinuousLinearMap.inl ℝ E ℝ))
  apply hclm.congr_of_eventuallyEq
  filter_upwards [(hU.prod isOpen_Ioo).mem_nhds hp] with q hq
  exact (((hG.contDiffAt ((hU.prod isOpen_Ioo).mem_nhds hq)).differentiableAt
    (by simp)).hasFDerivAt.comp q.1 (hasFDerivAt_prodMk_left q.1 q.2)).fderiv

end RothschildStein.G1
