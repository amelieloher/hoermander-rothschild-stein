-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.Integration
public import RothschildStein.H1.TestOperator
public import RothschildStein.H1.FundamentalDictionary
public import RothschildStein.G2.DifferentialTranspose

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped BigOperators
namespace RothschildStein.H1
variable {N q : ℕ} (G : HomogeneousGroup N)

/-- Global bilinear integration by parts for the full standing
operator against one compact smooth test (BB Remark 3.30, p. 111).
The noncompact smooth function is allowed on either side of the equation. -/
theorem StandingHypotheses.integral_operator_test
    (H : StandingHypotheses G q) {f : (Fin N → ℝ) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (φ : TestFunction (⊤ : Opens (Fin N → ℝ)) ℝ (⊤ : ℕ∞)) :
    (∫ x, sumSquaresWithDrift H.fields f x * φ x) =
      ∫ x, f x * sumSquaresWithDriftTranspose H.fields φ x := by
  have hd := H.integral_field_test G ⊤ 0 f (hf.of_le (by simp)).contDiffOn φ
  have hs (i : Fin q) := H.integral_square_test G ⊤ i.succ f
    (hf.of_le (by simp)).contDiffOn φ
  simp only [Opens.coe_top, setIntegral_univ] at hd hs
  have hi (i : Fin (q + 1)) : Integrable (fun x => fieldDerivative (H.fields i) f x * φ x) :=
    (smooth_fieldDerivative (H.fields i) (H.fields_smooth G i) f hf).continuous.locallyIntegrable
      |>.integrable_smul_right_of_hasCompactSupport φ.contDiff.continuous φ.hasCompactSupport
  have hii (i : Fin q) : Integrable (fun x =>
      fieldDerivative (H.fields i.succ) (fieldDerivative (H.fields i.succ) f) x * φ x) :=
    (smooth_fieldDerivative (H.fields i.succ) (H.fields_smooth G i.succ) _
      (smooth_fieldDerivative (H.fields i.succ) (H.fields_smooth G i.succ) f hf)).continuous.locallyIntegrable
      |>.integrable_smul_right_of_hasCompactSupport φ.contDiff.continuous φ.hasCompactSupport
  have hit (I : List (Fin (q + 1))) : Integrable (fun x => f x * wordDerivative H.fields I φ x) := by
    let ψ := S.wordDerivativeTest ⊤ H.fields (fun i => (H.fields_smooth G i).contDiffOn) I φ
    have he : (ψ : (Fin N → ℝ) → ℝ) = wordDerivative H.fields I φ := rfl
    exact hf.continuous.locallyIntegrable.integrable_smul_right_of_hasCompactSupport
      (he ▸ ψ.contDiff.continuous) (he ▸ ψ.hasCompactSupport)
  have hit0 : Integrable (fun x => f x * fieldDerivative (H.fields 0) φ x) := hit [0]
  have hitii (i : Fin q) : Integrable (fun x => f x *
      fieldDerivative (H.fields i.succ) (fieldDerivative (H.fields i.succ) φ) x) := hit [i.succ, i.succ]
  have hin : Integrable (fun x => -(f x * fieldDerivative (H.fields 0) φ x)) := hit0.neg
  simp_rw [sumSquaresWithDrift, H.sumSquaresTranspose_formula G φ φ.contDiff,
    add_mul, Finset.sum_mul, mul_add, mul_neg, Finset.mul_sum]
  rw [integral_add (hi 0) (integrable_finsetSum _ (fun i _ => hii i)),
    integral_add hin (integrable_finsetSum _ (fun i _ => hitii i)),
    integral_neg, integral_finsetSum _ (fun i _ => hii i),
    integral_finsetSum _ (fun i _ => hitii i), hd]
  congr 1
  exact Finset.sum_congr rfl (fun i _ => hs i)

/-- A smooth weak solution of the standing operator is a
pointwise solution. The conversion uses the fundamental lemma for compact
smooth tests (BB p. 270). -/
theorem StandingHypotheses.operator_eq_of_weak_pairing
    (H : StandingHypotheses G q) {f g : (Fin N → ℝ) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : Continuous g)
    (heq : ∀ φ : (Fin N → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ x, f x * sumSquaresWithDriftTranspose H.fields φ x) = ∫ x, g x * φ x) :
    sumSquaresWithDrift H.fields f = g := by
  have hPf : Continuous (sumSquaresWithDrift H.fields f) := by
    apply Continuous.add (smooth_fieldDerivative _ (H.fields_smooth G 0) f hf).continuous
    exact continuous_finsetSum _ (fun i _ =>
      (smooth_fieldDerivative _ (H.fields_smooth G i.succ) _
        (smooth_fieldDerivative _ (H.fields_smooth G i.succ) f hf)).continuous)
  apply G2.continuous_eq_of_test_pairings hPf hg
  intro φ hφ hc
  let φt : TestFunction (⊤ : Opens (Fin N → ℝ)) ℝ (⊤ : ℕ∞) := ⟨φ, hφ, hc, subset_univ _⟩
  have h := (H.integral_operator_test G hf φt).trans (heq φ hφ hc)
  change (∫ x, sumSquaresWithDrift H.fields f x * φ x) = ∫ x, g x * φ x at h
  simpa only [mul_comm] using h

end RothschildStein.H1
