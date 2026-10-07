-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.WeightTwoRepresentationCompactPv
public import RothschildStein.H1.FundamentalSecondDerivative
public import RothschildStein.H1.GaugeCutoff

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory Filter
open scoped ENNReal BigOperators

/-- The fundamental-solution formula gives the compact second-word
representation. Assume the Lp bounds for the actual principal-value
operators; coefficient bounds follow from the finite correction family. -/
theorem compact_weight_two_estimate_of_fundamental_kernel_and_compact_lp_bounds {n q : ℕ}
    (G : HomogeneousGroup n) (H : H1.StandingHypotheses G q) (K : H1.FundamentalKernel G H)
    (hQ : 2 < (G.homogeneousDimension : ℝ))
    (p : ℝ≥0∞) (hp : 1 ≤ p) (M : ℝ) (hM : 0 ≤ M)
    (η : (Fin n → ℝ) → ℝ) (R : ℝ)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hsη : HasCompactSupport η)
    (heη : η =ᶠ[nhds (0 : Fin n → ℝ)] fun _ => 1)
    (hR : 0 < R) (hout : ∀ z, R ≤ H.norm z → η z = 0) (hbη : ∀ z, ‖η z‖ ≤ 1)
    (hLp : ∀ i j : Fin q, ∀ f : (Fin n → ℝ) → ℝ, ContDiff ℝ 1 f → HasCompactSupport f →
      eLpNorm (H1.principalValueConvolution G H.norm
        (fieldDerivative (H.fields i.succ) (fieldDerivative (H.fields j.succ) K)) f) p volume ≤
          ENNReal.ofReal M*eLpNorm f p volume) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : (Fin n → ℝ) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) u → HasCompactSupport u →
      ∀ I : List (Fin (q+1)), wordWeight driftWeight I = 2 →
        eLpNorm (wordDerivative H.fields I u) p volume ≤
          ENNReal.ofReal C*eLpNorm (sumSquaresWithDrift H.fields u) p volume := by
  classical
  let T := fun i j : Fin q => H1.principalValueConvolution G H.norm
    (fieldDerivative (H.fields i.succ) (fieldDerivative (H.fields j.succ) K))
  let c := fun i j : Fin q => ∫ z in {z | H.norm z ≤ R}, fieldDerivative (H.fields i.succ)
    (fun y => fieldDerivative (H.fields j.succ) K y*(1-η y)) z
  let B : ℝ := ∑ i : Fin q, ∑ j : Fin q, |c i j|
  have hB : 0 ≤ B := Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _))
  have hc : ∀ i j, |c i j| ≤ B := by
    intro i j
    exact (Finset.single_le_sum (f := fun k : Fin q => |c i k|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ j)).trans
      (Finset.single_le_sum (f := fun k : Fin q => ∑ l : Fin q, |c k l|)
        (fun _ _ => Finset.sum_nonneg (fun _ _ => abs_nonneg _)) (Finset.mem_univ i))
  refine ⟨(q+1 : ℝ)*(M+B+1), ?_⟩
  apply compact_weight_two_estimate_of_representation_and_compact_lp_bounds H.fields (fun i => H.fields_smooth G i) p hp hM hB T c hc hLp
  intro u hu hsu i j
  apply Filter.Eventually.of_forall
  intro x
  have he := congrFun (K.secondDerivative_representation G H hQ i j hη hsη heη hR hout hbη hu hsu) x
  simpa only [wordDerivative, T, c, mul_comm] using he

/-- Compact a priori estimates for the actual fundamental kernel under
the global principal-value Lp bounds, with a smooth cutoff and finite
correction coefficients. -/
theorem compact_weight_two_estimate_of_fundamental_compact_principalValue_bounds {n q : ℕ}
    (G : HomogeneousGroup n) (H : H1.StandingHypotheses G q) (K : H1.FundamentalKernel G H)
    (hQ : 2 < (G.homogeneousDimension : ℝ))
    (p : ℝ≥0∞) (hp : 1 ≤ p) (M : ℝ) (hM : 0 ≤ M)
    (hLp : ∀ i j : Fin q, ∀ f : (Fin n → ℝ) → ℝ, ContDiff ℝ 1 f → HasCompactSupport f →
      eLpNorm (H1.principalValueConvolution G H.norm
        (fieldDerivative (H.fields i.succ) (fieldDerivative (H.fields j.succ) K)) f) p volume ≤
          ENNReal.ofReal M*eLpNorm f p volume) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : (Fin n → ℝ) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) u → HasCompactSupport u →
      ∀ I : List (Fin (q+1)), wordWeight driftWeight I = 2 →
        eLpNorm (wordDerivative H.fields I u) p volume ≤
          ENNReal.ofReal C*eLpNorm (sumSquaresWithDrift H.fields u) p volume := by
  obtain ⟨η,R,hη,hsη,heη,hR,hout,hbη⟩ := H1.exists_compactGaugeCutoff G H.norm.gauge
  exact compact_weight_two_estimate_of_fundamental_kernel_and_compact_lp_bounds G H K hQ p hp M hM
    η R hη hsη heη hR hout hbη hLp

end RothschildStein.H3
