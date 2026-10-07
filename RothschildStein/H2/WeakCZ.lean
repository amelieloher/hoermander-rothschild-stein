-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.CZOperatorGood
public import RothschildStein.H2.CZOperatorBad
public import RothschildStein.H2.EnlargedBadSet
public import RothschildStein.H2.OperatorDistributionSplit

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal BigOperators Classical

namespace RothschildStein.H2
variable {X ι : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X] [Countable ι]

/-- Combine the actual CZ decomposition, the enlarged-ball
measure bound, and the operator good/bad estimates (BB pp. 319–320). -/
theorem CZDecompositionFacts.operator_weak_bound (D : LocDoubling X)
    {xbar : X} {R β A S C α cT : ℝ} {K : X → X → ℝ}
    (T : Lp ℝ 2 (D.μ.restrict (ball xbar R)) →L[ℝ]
      Lp ℝ 2 (D.μ.restrict (ball xbar R)))
    (hcT : ‖T‖ ≤ cT) (hC : 0 ≤ C) (hα : 0 < α)
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
      (fun i => ball (z i) (r i)) f (C * α) g b)
    (hf : MemLp f 2 (D.μ.restrict D.Ω₂))
    (hfi : IntegrableOn f D.Ω₂ D.μ)
    (hn : ∀ᵐ x ∂D.μ.restrict D.Ω₂, 0 ≤ f x) :
    ∃ hfU : MemLp f 2 (D.μ.restrict (ball xbar R)),
      distribution (D.μ.restrict (ball xbar R)) (fun x => (T (hfU.toLp f)) x) α ≤
        ENNReal.ofReal (4 * cT ^ 2 * C / α) * ∫⁻ x in D.Ω₂, ‖f x‖ₑ ∂D.μ +
        (ENNReal.ofReal D.C_D ^ 2 * ∑' i, D.μ (ball (z i) (r i)) +
          ENNReal.ofReal (4 * (S * volumeIntegralConstant D.C_D β * (4 : ℝ) ^ (-β)) / α) *
            ∫⁻ x in D.Ω₂, ‖f x‖ₑ ∂D.μ) := by
  let U := ball xbar R
  let E := ⋃ i, ball (z i) (4 * r i)
  have hE : MeasurableSet E := MeasurableSet.iUnion fun i => isOpen_ball.measurableSet
  have hm : D.μ.restrict U ≤ D.μ.restrict D.Ω₂ :=
    Measure.restrict_mono (hU.trans D.sub₁₂) le_rfl
  have hfU : MemLp f 2 (D.μ.restrict U) := hf.mono_measure hm
  obtain ⟨hg, hgood⟩ := hcz.operator_good_distribution D (hU.trans D.sub₁₂) T hcT hC hα hfi hn
  obtain ⟨hb, hbad⟩ := hcz.operator_bad_sum_l1 D hos hKt hk hU hR hsupport z r hz hB hr hcap hf
  have htail := distribution_half_le_of_l1_bound
    (a := 2 * (S * volumeIntegralConstant D.C_D β * (4 : ℝ) ^ (-β))) (D.μ.restrict (U \ E))
    (fun x => (T (hb.toLp (fun x => f x - g x))) x)
    ((Lp.aestronglyMeasurable _).aemeasurable.mono_measure
      (Measure.restrict_mono Set.sdiff_subset le_rfl)) hα
    (∫⁻ x in D.Ω₂, ‖f x‖ₑ ∂D.μ)
    (by simpa only [U, E, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
      ENNReal.ofReal_ofNat, mul_assoc] using hbad)
  have he : D.μ E ≤ ENNReal.ofReal D.C_D ^ 2 * ∑' i, D.μ (ball (z i) (r i)) :=
    D.outerPatch.enlarged_bad_set_measure z r hz hr hcap
  have hsplit := operator_distribution_split (D.μ.restrict U) T hfU hg hb E hE α
  have hrestrict : (D.μ.restrict U).restrict Eᶜ = D.μ.restrict (U \ E) := by
    rw [Measure.restrict_restrict hE.compl]
    congr 1
    ext x
    simp [and_comm]
  rw [hrestrict] at hsplit
  refine ⟨hfU, hsplit.trans (add_le_add hgood (add_le_add ?_ ?_))⟩
  · exact (Measure.restrict_apply_le U E).trans he
  · simpa only [show (2 : ℝ) * (2 * (S * volumeIntegralConstant D.C_D β * (4 : ℝ) ^ (-β))) =
      4 * (S * volumeIntegralConstant D.C_D β * (4 : ℝ) ^ (-β)) by ring] using htail

end RothschildStein.H2
