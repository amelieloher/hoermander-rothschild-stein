-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.WeakCZ
public import RothschildStein.H2.CalderonZygmund

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal BigOperators Classical

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Instantiate the operator CZ estimate using the actual covering (BB pp. 319–320, 324–325). -/
theorem LocDoubling.operator_weak_cover (D : LocDoubling X)
    {xbar : X} {R β A S α cT m : ℝ} {K : X → X → ℝ}
    (hxbar : xbar ∈ D.Ω₀)
    (T : Lp ℝ 2 (D.μ.restrict (ball xbar R)) →L[ℝ]
      Lp ℝ 2 (D.μ.restrict (ball xbar R)))
    (hcT : ‖T‖ ≤ cT) (hα : 0 < α)
    (hos : OffDiagonalL2 D (ball xbar R) K T)
    (hKt : KernelClass D.μ D.Ω₁ β 0 A S (fun x y => K y x))
    (hk : Measurable (Function.uncurry K))
    (hU : ball xbar R ⊆ D.Ω₁) (hR : R < D.κ)
    (hsupport : ∀ a b, a ∉ ball xbar R ∨ b ∉ ball xbar R → K a b = 0)
    (hm : 0 < m) (hml : ∀ z ∈ D.Ω₁, ENNReal.ofReal m ≤ D.μ (ball z D.κ))
    (f : X → ℝ) (hf : MemLp f 2 (D.μ.restrict D.Ω₂))
    (hfi : IntegrableOn f D.Ω₂ D.μ)
    (hn : ∀ᵐ x ∂D.μ.restrict D.Ω₂, 0 ≤ f x)
    (hfs : ∀ᵐ x ∂D.μ.restrict D.Ω₂, x ∉ ball xbar D.κ → f x = 0)
    (hthreshold : eLpNorm f 1 (D.μ.restrict D.Ω₂) / ENNReal.ofReal α < D.μ D.Ω₁) :
    ∃ hfU : MemLp f 2 (D.μ.restrict (ball xbar R)),
      distribution (D.μ.restrict (ball xbar R)) (fun x => (T (hfU.toLp f)) x) α ≤
        ENNReal.ofReal (4 * cT ^ 2 * ((D.C_D ^ 7 + D.C_D ^ 5) * goodAverageConstant D m) / α) *
          ∫⁻ x in D.Ω₂, ‖f x‖ₑ ∂D.μ +
        (ENNReal.ofReal D.C_D ^ 2 * (ENNReal.ofReal (D.C_D ^ 7 + D.C_D ^ 5) *
          (eLpNorm f 1 (D.μ.restrict D.Ω₂) / ENNReal.ofReal α)) +
          ENNReal.ofReal (4 * (S * volumeIntegralConstant D.C_D β * (4 : ℝ) ^ (-β)) / α) *
            ∫⁻ x in D.Ω₂, ‖f x‖ₑ ∂D.μ) := by
  obtain ⟨u, hu, hr, hlarge, hmass, _, g, b, hcz⟩ :=
    D.calderon_zygmund_decomposition_of_volume_lower hxbar f hfi hn hfs hm hml hα hthreshold
  let : Countable u := hu.to_subtype
  let r : u → ℝ := fun z => whitneyRadius (goodBadLevelSet D f α) D.κ z
  have hz : ∀ z : u, (z : X) ∈ D.Ω₁ := fun z =>
    hlarge z (mem_ball_self (by linarith [(hr z).1]))
  have hB : ∀ z : u, ball (z : X) (r z) ⊆ D.Ω₁ := fun z =>
    (ball_subset_ball (by dsimp [r]; linarith [(hr z).1])).trans (hlarge z)
  have hCD : 0 ≤ D.C_D := by linarith [D.one_lt_C_D]
  have hC : 0 ≤ (D.C_D ^ 7 + D.C_D ^ 5) * goodAverageConstant D m :=
    mul_nonneg (add_nonneg (pow_nonneg hCD _) (pow_nonneg hCD _))
      ((pow_nonneg hCD 6).trans (le_max_left _ _))
  obtain ⟨hfU, hweak⟩ := hcz.operator_weak_bound D T hcT hC hα hos hKt hk hU hR hsupport
    (fun z : u => (z : X)) r hz hB (fun z => (hr z).1) (fun z => (hr z).2) hf hfi hn
  refine ⟨hfU, hweak.trans (add_le_add le_rfl (add_le_add ?_ le_rfl))⟩
  exact mul_le_mul' le_rfl hmass

end RothschildStein.H2
