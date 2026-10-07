-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.KernelLpConvergence
public import RothschildStein.S.KernelZeroExtension
public import RothschildStein.S.MollifierZeroExtension

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory Function Metric Filter TopologicalSpace
open scoped ENNReal Topology
namespace RothschildStein.S
variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

omit [Fact (1 ≤ p)] in
/-- Interior-patch kernel norms agree with the zero-extension
norms for each positive scale below the tube radius (BB p. 74). -/
theorem eLpNorm_smoothFriedrichsKernelOp_eq_zeroExtension
    (Ω : Opens (Fin n → ℝ)) (K : SmoothFriedrichsKernel n)
    {U : Set (Fin n → ℝ)} (hU : IsOpen U)
    {δ ε : ℝ} (hε : ε ∈ Ioo 0 δ) (hδ : cthickening δ (closure U) ⊆ Ω)
    (h : (Fin n → ℝ) → ℝ) :
    eLpNorm (friedrichsKernelOp K.family h ε) p (volume.restrict U) =
      eLpNorm (friedrichsKernelOp K.family ((Ω : Set (Fin n → ℝ)).indicator h) ε)
        p (volume.restrict U) := by
  apply eLpNorm_congr_ae
  filter_upwards [ae_restrict_mem hU.measurableSet] with x hx
  exact smoothFriedrichsKernelOp_eq_zeroExtension Ω K h hε.1 x
    ((closedBall_subset_closedBall hε.2.le).trans
      (closedBall_subset_of_interior_thickening Ω hδ hx))

/-- Local Lp data are sent to zero in Lp on the interior patch
by every constructed bounded zero-mean kernel family
(BB Lemma 2.11, p. 74). -/
theorem tendsto_eLpNorm_smoothFriedrichsKernelOp_zero_local
    (Ω : Opens (Fin n → ℝ)) (K : SmoothFriedrichsKernel n)
    {U : Set (Fin n → ℝ)} (hU : IsOpen U) (hc : IsCompact (closure U))
    {δ : ℝ} (hd : 0 < δ) (hδ : cthickening δ (closure U) ⊆ Ω)
    (hmean : HasVanishingKernelMean (K.toBounded U hc δ)) (hpt : p ≠ ⊤)
    {h : (Fin n → ℝ) → ℝ} (hh : MemLp h p (volume.restrict (Ω : Set (Fin n → ℝ)))) :
    Tendsto (fun ε : ℝ => eLpNorm (friedrichsKernelOp K.family h ε) p (volume.restrict U))
      (𝓝[>] 0) (𝓝 0) := by
  have H := tendsto_eLpNorm_smoothFriedrichsKernelOp_zero Ω K hU hc hd hδ hmean hpt
    ((memLp_zeroExtension_iff Ω.isOpen.measurableSet h).mpr hh)
  apply H.congr'
  filter_upwards [Ioo_mem_nhdsGT hd] with ε hε
  exact (eLpNorm_smoothFriedrichsKernelOp_eq_zeroExtension Ω K hU hε hδ h).symm

end RothschildStein.S
