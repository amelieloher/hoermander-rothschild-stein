-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.KernelLpEstimate
public import RothschildStein.S.KernelAEInput
public import RothschildStein.S.KernelUniformConvergence

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory Function Metric Filter TopologicalSpace
open scoped ENNReal Topology ContDiff
namespace RothschildStein.S
variable {n : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- One uniform size constant bounds the kernel operator for
all positive small scales and every global Lp input representative
(BB Lemma 2.11, p. 74). -/
theorem exists_smoothFriedrichsKernelOp_modulus_bound
    (Ω : Opens (Fin n → ℝ)) (K : SmoothFriedrichsKernel n)
    {U : Set (Fin n → ℝ)} (hU : IsOpen U) (hc : IsCompact (closure U))
    {δ : ℝ} (hδ : cthickening δ (closure U) ⊆ Ω)
    (hmean : HasVanishingKernelMean (K.toBounded U hc δ)) (hpt : p ≠ ⊤) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (h : (Fin n → ℝ) → ℝ) (hh : MemLp h p volume),
      ∀ ε ∈ Ioo 0 δ,
      eLpNorm (friedrichsKernelOp K.family h ε) p (volume.restrict U) ≤
        ENNReal.ofReal C * volume (closedBall (0 : Fin n → ℝ) 1) *
          translationModulus (hh.toLp h) ε := by
  obtain ⟨C,hC,hsize⟩ := (K.toBounded U hc δ).exists_uniform_size
  refine ⟨C,hC,?_⟩
  intro h hh ε hε
  rw [← friedrichsKernelOp_eq_of_ae K.family hh.coeFn_toLp hε.1.ne']
  exact eLpNorm_smoothFriedrichsKernelOp_le_modulus Ω K hU hc hε hδ hpt
    (hh.toLp h) C (hsize ε hε) (hmean ε hε)

/-- Every constructed bounded zero-mean kernel family tends to
zero in finite Lp on the interior patch for global Lp data
(BB Lemma 2.11, p. 74). -/
theorem tendsto_eLpNorm_smoothFriedrichsKernelOp_zero
    (Ω : Opens (Fin n → ℝ)) (K : SmoothFriedrichsKernel n)
    {U : Set (Fin n → ℝ)} (hU : IsOpen U) (hc : IsCompact (closure U))
    {δ : ℝ} (hd : 0 < δ) (hδ : cthickening δ (closure U) ⊆ Ω)
    (hmean : HasVanishingKernelMean (K.toBounded U hc δ)) (hpt : p ≠ ⊤)
    {h : (Fin n → ℝ) → ℝ} (hh : MemLp h p volume) :
    Tendsto (fun ε : ℝ => eLpNorm (friedrichsKernelOp K.family h ε) p (volume.restrict U))
      (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C,hC,hb⟩ := exists_smoothFriedrichsKernelOp_modulus_bound Ω K hU hc hδ hmean hpt
  have ht := ENNReal.Tendsto.const_mul (tendsto_translationModulus hpt (hh.toLp h))
    (a := ENNReal.ofReal C * volume (closedBall (0 : Fin n → ℝ) 1))
    (Or.inr (ENNReal.mul_ne_top ENNReal.ofReal_ne_top measure_closedBall_lt_top.ne))
  have hz : Tendsto (fun ε : ℝ => ENNReal.ofReal C *
      volume (closedBall (0 : Fin n → ℝ) 1) * translationModulus (hh.toLp h) ε)
      (𝓝[>] 0) (𝓝 0) := by simpa only [mul_zero] using ht
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hz
  · exact Eventually.of_forall (fun _ => zero_le)
  · filter_upwards [Ioo_mem_nhdsGT hd] with ε hε
    exact hb h hh ε hε

end RothschildStein.S
