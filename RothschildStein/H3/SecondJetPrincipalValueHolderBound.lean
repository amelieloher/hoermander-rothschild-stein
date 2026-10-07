-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.SecondJetHolderBound
public import RothschildStein.H3.ControlMetric
public import RothschildStein.H1.PrincipalValueDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set
open scoped ENNReal NNReal BigOperators
namespace RothschildStein.H3

/-- Principal-value Holder estimates and fixed correction coefficients
give the horizontal-plus-drift estimate under the compact intrinsic
estimate hypothesis (BB Thm. 8.50). -/
theorem second_jet_holder_bound_of_principal_value_estimates {N q : ℕ}
    (G : HomogeneousGroup N) (ν : G2.HomogeneousNorm G) (h1 : ν.c = 1) (hsym : ν.Symmetric)
    (a : ℝ≥0) (U : Set (ControlCarrier N))
    (F u0 : ControlCarrier N → ℝ) (u : Fin q → Fin q → ControlCarrier N → ℝ)
    (K : Fin q → Fin q → (Fin N → ℝ) → ℝ) (c B : Fin q → Fin q → ℝ)
    (θ L : ℝ) (_hθ : 0 ≤ θ) (hL : 1 ≤ L) (hB : ∀ i j, 0 ≤ B i j)
    (hcoeff : ∀ i j, B i j + |c i j| ≤ L)
    (heq : F = fun x => u0 x + ∑ i : Fin q, u i i x)
    (hrep : ∀ i j, u i j = fun x => H1.principalValueConvolution G ν (K i j) F x + c i j * F x) :
    letI metric : MetricSpace (ControlCarrier N) := gaugeMetric G ν h1 hsym
    (∀ i j, @H2.boundedHolderNorm (ControlCarrier N) metric a U
      (fun x => H1.principalValueConvolution G ν (K i j) F x) ≤
        ENNReal.ofReal (B i j) * @H2.boundedHolderNorm (ControlCarrier N) metric a U F) →
    (∑ i : Fin q, ∑ j : Fin q, @H2.boundedHolderNorm (ControlCarrier N) metric a U (u i j)) +
      ENNReal.ofReal θ * @H2.boundedHolderNorm (ControlCarrier N) metric a U u0 ≤
      ((q : ℝ≥0∞)^2 + ENNReal.ofReal θ * (1 + (q : ℝ≥0∞))) * ENNReal.ofReal L *
        @H2.boundedHolderNorm (ControlCarrier N) metric a U F := by
  let metric : MetricSpace (ControlCarrier N) := gaugeMetric G ν h1 hsym
  intro hPV
  have hu (i j : Fin q) : @H2.boundedHolderNorm (ControlCarrier N) metric a U (u i j) ≤
      ENNReal.ofReal L * @H2.boundedHolderNorm (ControlCarrier N) metric a U F := by
    rw [hrep i j]
    apply H2.boundedHolderNorm_add_le.trans
    have hsmul := @H2.boundedHolderNorm_smul (ControlCarrier N) metric a U (c i j) F
    have he : (c i j • F) = (fun x => c i j * F x) := by
      funext x
      rfl
    rw [he] at hsmul
    rw [hsmul]
    have hcoef : ENNReal.ofReal (B i j) + ENNReal.ofReal |c i j| ≤ ENNReal.ofReal L := by
      rw [← ENNReal.ofReal_add (hB i j) (abs_nonneg _)]
      exact ENNReal.ofReal_le_ofReal (hcoeff i j)
    calc
      _ ≤ ENNReal.ofReal (B i j) * @H2.boundedHolderNorm (ControlCarrier N) metric a U F +
          ENNReal.ofReal |c i j| * @H2.boundedHolderNorm (ControlCarrier N) metric a U F :=
        add_le_add (hPV i j) le_rfl
      _ = (ENNReal.ofReal (B i j) + ENNReal.ofReal |c i j|) *
          @H2.boundedHolderNorm (ControlCarrier N) metric a U F := by rw [add_mul]
      _ ≤ _ := mul_le_mul' hcoef le_rfl
  have hLe : (1 : ℝ≥0∞) ≤ ENNReal.ofReal L := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hL
  exact @second_jet_holder_norm_bound (ControlCarrier N) metric q a U F u0 u
    (ENNReal.ofReal θ) (ENNReal.ofReal L) hLe heq hu

end RothschildStein.H3
