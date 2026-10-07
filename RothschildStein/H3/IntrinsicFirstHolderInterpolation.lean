-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.IntrinsicFirstHolderScale
public import RothschildStein.H3.HolderInterpolationScale

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal BigOperators
namespace RothschildStein.H3

/-- Compact intrinsic order-two inputs satisfy the first-order
interpolation estimate with the stated exponent. The constant is uniform
in the center, input, jets, and interpolation parameter. -/
theorem intrinsic_first_holder_interpolation_of_controlNorm {N q : ℕ} (G : HomogeneousGroup N)
    (H : H1.StandingHypotheses G q) (K : H1.FundamentalKernel G H)
    (Hc : G2.ControlNormConclusion G driftWeight H.fields)
    (hQ : 2 < (G.homogeneousDimension : ℝ)) (μ : G2.GroupMollifier G H.norm)
    (ν : G2.HomogeneousNorm G) (hν : ν.Smooth)
    {α : ℝ≥0} (hα : 0 < α) (hα1 : (α : ℝ) < 1) {ρ : ℝ} (hρ : 0 < ρ) :
    let metric : MetricSpace (ControlCarrier N) :=
      gaugeMetric G Hc.norm Hc.constant_one Hc.symmetric
    ∃ C : ℝ, 0 < C ∧ ∀ z : ControlCarrier N,
      ∀ u : (Fin N → ℝ) → ℝ,
      ∀ jet : List (Fin (q + 1)) → (Fin N → ℝ) → ℝ,
      jet [] = u →
      (∀ I, wordWeight driftWeight I ≤ 2 → hasIntrinsicWordDeriv H.fields ⊤ I u (jet I)) →
      (∀ I, wordWeight driftWeight I ≤ 2 → Continuous (jet I)) →
      (∀ I, wordWeight driftWeight I ≤ 2 → HasCompactSupport (jet I)) →
      (∀ I, wordWeight driftWeight I ≤ 2 → tsupport (jet I) ⊆ G2.gaugeBall G Hc.norm z ρ) →
      ∀ η : ℝ, 0 < η → η < 1 →
      let F := fun y => jet [0] y + ∑ i : Fin q, jet [i.succ, i.succ] y
      @H2.boundedHolderNorm (ControlCarrier N) metric α univ (fun x => u x) +
        (∑ i : Fin q, @H2.boundedHolderNorm (ControlCarrier N) metric α univ
          (fun x => jet [i.succ] x)) ≤
        ENNReal.ofReal (η * lpNorm F ∞ volume) +
        ENNReal.ofReal (C * η ^ (-(2 * (3 + (G.homogeneousDimension : ℝ)) /
          (1 - (α : ℝ)))) * lpNorm u ∞ volume) := by
  let metric : MetricSpace (ControlCarrier N) :=
    gaugeMetric G Hc.norm Hc.constant_one Hc.symmetric
  obtain ⟨a, b, _ha, hb, hscale⟩ := intrinsic_first_holder_scale_of_controlNorm G H K Hc hQ μ ν hν hα hα1 hρ
  let δ := (1 - (α : ℝ)) / 2
  let M := 3 + (G.homogeneousDimension : ℝ)
  let γ := M / δ
  let B := 2 * max a 1
  let C := b * B ^ γ
  have hδ : 0 < δ := div_pos (sub_pos.mpr hα1) (by norm_num)
  have hB : 0 < B := by dsimp [B]; positivity
  have hC : 0 < C := mul_pos hb (Real.rpow_pos_of_pos hB _)
  have hγ : γ = 2 * (3 + (G.homogeneousDimension : ℝ)) / (1 - (α : ℝ)) := by
    dsimp [γ, M, δ]
    field_simp [(sub_pos.mpr hα1).ne']
  refine ⟨C, hC, ?_⟩
  intro z u jet hzero hi hc hs hsupport η hη hη1
  let t := (η / B) ^ (1 / δ)
  obtain ⟨ht, ht1, hp, hn⟩ := holderInterpolation_scale_powers (a := a) (M := M) hδ hη hη1
  have hh := hscale z u jet hzero hi hc hs hsupport t ht ht1
  have hab : a / B ≤ 1 := (div_le_one hB).mpr (by
    dsimp [B]
    linarith [le_max_left a 1, le_max_right a 1])
  have hnear : a * t ^ δ ≤ η := by
    rw [hp]
    calc
      _ = η * (a / B) := by dsimp [B]; ring
      _ ≤ η * 1 := mul_le_mul_of_nonneg_left hab hη.le
      _ = η := mul_one η
  have hfar : b * t ^ (-3 - (G.homogeneousDimension : ℝ)) = C * η ^ (-γ) := by
    rw [show -3 - (G.homogeneousDimension : ℝ) = -M by dsimp [M]; ring, hn]
    dsimp [C, γ, B]
    rw [show -M / δ = -(M / δ) by ring]
    ring
  have hh' := hh.trans (add_le_add
    (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hnear lpNorm_nonneg))
    (ENNReal.ofReal_le_ofReal (show
      b * t ^ (-3 - (G.homogeneousDimension : ℝ)) * lpNorm u ∞ volume ≤
        C * η ^ (-γ) * lpNorm u ∞ volume by rw [hfar])))
  rw [hγ] at hh'
  exact hh'

end RothschildStein.H3
