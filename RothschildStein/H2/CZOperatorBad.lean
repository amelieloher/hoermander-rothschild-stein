-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.CZConvergence
public import RothschildStein.H2.OperatorBadSeries
public import RothschildStein.H2.OperatorBadTail

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric Filter
open scoped ENNReal BigOperators Classical Topology

namespace RothschildStein.H2
variable {X ι : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [Countable ι]

/-- The sum of bad pieces has the uniform L¹ tail outside
all enlarged bad balls (BB p. 320, L² convergence and cancellation bounds). -/
theorem CZDecompositionFacts.operator_bad_sum_l1 (D : LocDoubling X)
    {xbar : X} {R β A S C : ℝ} {K : X → X → ℝ}
    {T : Lp ℝ 2 (D.μ.restrict (ball xbar R)) →L[ℝ]
      Lp ℝ 2 (D.μ.restrict (ball xbar R))}
    (hos : OffDiagonalL2 D (ball xbar R) K T)
    (hKt : KernelClass D.μ D.Ω₁ β 0 A S (fun x y => K y x))
    (hk : Measurable (Function.uncurry K))
    (hU : ball xbar R ⊆ D.Ω₁) (hR : R < D.κ)
    (hsupport : ∀ a b, a ∉ ball xbar R ∨ b ∉ ball xbar R → K a b = 0)
    (z : ι → X) (r : ι → ℝ) (hz : ∀ i, z i ∈ D.Ω₁)
    (hB : ∀ i, ball (z i) (r i) ⊆ D.Ω₁)
    (hr : ∀ i, 0 < r i) (hcap : ∀ i, 5 * r i ≤ D.κ)
    {f g : X → ℝ} {b : ι → X → ℝ}
    (hcz : CZDecompositionFacts (D.μ.restrict D.Ω₂)
      (fun i => ball (z i) (r i)) f C g b)
    (hf : MemLp f 2 (D.μ.restrict D.Ω₂)) :
    ∃ hv : MemLp (fun x => f x - g x) 2 (D.μ.restrict (ball xbar R)),
      (∫⁻ x in ball xbar R \ ⋃ i, ball (z i) (4 * r i),
        ‖(T (hv.toLp (fun x => f x - g x))) x‖ₑ ∂D.μ) ≤
        2 * ENNReal.ofReal (S * volumeIntegralConstant D.C_D β * (4 : ℝ) ^ (-β)) *
          ∫⁻ x in D.Ω₂, ‖f x‖ₑ ∂D.μ := by
  let : IsFiniteMeasure (D.μ.restrict D.Ω₂) := ⟨by simpa using D.finΩ₂⟩
  have hmeasure : D.μ.restrict (ball xbar R) ≤ D.μ.restrict D.Ω₂ :=
    Measure.restrict_mono (hU.trans D.sub₁₂) le_rfl
  rcases hcz with ⟨hgmeas, hbmeas, hgint, hbint, hdecomp, hgbound, hmass,
    hbzero, hcancel, hbadmass, hfinite, hdom, hbadLp, hgLp⟩
  have hg2 : MemLp g 2 (D.μ.restrict D.Ω₂) := hgLp 2 inferInstance
  have hv2 : MemLp (fun x => f x - g x) 2 (D.μ.restrict D.Ω₂) := hf.sub hg2
  have hv : MemLp (fun x => f x - g x) 2 (D.μ.restrict (ball xbar R)) := hv2.mono_measure hmeasure
  have hbU : ∀ i, MemLp (b i) 2 (D.μ.restrict (ball xbar R)) :=
    fun i => (hbadLp 2 hf i).mono_measure hmeasure
  have hcz' : CZDecompositionFacts (D.μ.restrict D.Ω₂) (fun i => ball (z i) (r i)) f C g b :=
    ⟨hgmeas, hbmeas, hgint, hbint, hdecomp, hgbound, hmass, hbzero,
      hcancel, hbadmass, hfinite, hdom, hbadLp, hgLp⟩
  obtain ⟨s, _, _, hconv⟩ := hcz'.partial_sums_l2 (D.μ.restrict D.Ω₂) hf
  have hconvU : Tendsto (fun n => eLpNorm (fun x => (∑ i ∈ s n, b i x) - (f x - g x))
      2 (D.μ.restrict (ball xbar R))) atTop (𝓝 0) :=
    tendsto_nhds_bot_mono hconv (Eventually.of_forall fun n => eLpNorm_mono_measure _ hmeasure)
  refine ⟨hv, ?_⟩
  calc
    _ ≤ ∑' i, ∫⁻ x in ball xbar R \ ball (z i) (4 * r i),
        ‖(T ((hbU i).toLp (b i))) x‖ₑ ∂D.μ :=
      operator_bad_series_l1_bound D.μ (ball xbar R) T
        (fun i => ball (z i) (4 * r i)) b hbU (fun x => f x - g x) hv s hconvU
    _ ≤ ∑' i, ENNReal.ofReal (S * volumeIntegralConstant D.C_D β * (4 : ℝ) ^ (-β)) *
        ∫⁻ x in D.Ω₂, ‖b i x‖ₑ ∂D.μ := by
      apply ENNReal.tsum_le_tsum
      intro i
      exact hos.bad_piece_l1_tail D hKt hk hU hR (hz i) (hB i) (hr i) (hcap i)
        hsupport (b i) (hbmeas i) (hbint i) (hbU i) (hbzero i) (hcancel i)
    _ = ENNReal.ofReal (S * volumeIntegralConstant D.C_D β * (4 : ℝ) ^ (-β)) *
        ∑' i, ∫⁻ x in D.Ω₂, ‖b i x‖ₑ ∂D.μ := ENNReal.tsum_mul_left
    _ ≤ _ := by
      exact (mul_le_mul' le_rfl hbadmass).trans_eq (by ac_rfl)

end RothschildStein.H2
