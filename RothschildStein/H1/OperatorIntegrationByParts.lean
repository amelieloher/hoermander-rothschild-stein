-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.Integration
public import RothschildStein.H1.FundamentalDictionary

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped BigOperators
namespace RothschildStein.H1
variable {N q : ℕ} (G : HomogeneousGroup N)

/-- Green's identity for the standing operator on an open set,
with a compact test and a function smooth only on that set (BB p. 265). -/
theorem StandingHypotheses.integral_operator_test_on (H : StandingHypotheses G q)
    (U : Opens (Fin N → ℝ)) (f : (Fin N → ℝ) → ℝ)
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (U : Set (Fin N → ℝ)))
    (φ : TestFunction U ℝ (⊤ : ℕ∞)) :
    (∫ x in (U : Set (Fin N → ℝ)), sumSquaresWithDrift H.fields f x * φ x) =
      ∫ x in (U : Set (Fin N → ℝ)), f x * sumSquaresWithDriftTranspose H.fields φ x := by
  have hd (i : Fin (q + 1)) : ContDiffOn ℝ (⊤ : ℕ∞)
      (fieldDerivative (H.fields i) f) (U : Set (Fin N → ℝ)) :=
    (hf.fderiv_of_isOpen U.isOpen (by simp)).clm_apply (H.fields_smooth G i).contDiffOn
  have hdd (i : Fin (q + 1)) : ContDiffOn ℝ (⊤ : ℕ∞)
      (fieldDerivative (H.fields i) (fieldDerivative (H.fields i) f)) (U : Set (Fin N → ℝ)) :=
    ((hd i).fderiv_of_isOpen U.isOpen (by simp)).clm_apply (H.fields_smooth G i).contDiffOn
  have hi0 : IntegrableOn (fun x => fieldDerivative (H.fields 0) f x * φ x)
      (U : Set (Fin N → ℝ)) volume :=
    (S.integrable_mul_test U ((hd 0).continuousOn.locallyIntegrableOn
      (μ := volume) U.isOpen.measurableSet) φ).integrableOn
  have his (i : Fin q) : IntegrableOn
      (fun x => fieldDerivative (H.fields i.succ) (fieldDerivative (H.fields i.succ) f) x * φ x)
      (U : Set (Fin N → ℝ)) volume :=
    (S.integrable_mul_test U ((hdd i.succ).continuousOn.locallyIntegrableOn
      (μ := volume) U.isOpen.measurableSet) φ).integrableOn
  have hfLoc := hf.continuousOn.locallyIntegrableOn (μ := volume) U.isOpen.measurableSet
  have hit (i : Fin (q + 1)) : IntegrableOn
      (fun x => f x * fieldDerivative (H.fields i) φ x) (U : Set (Fin N → ℝ)) volume := by
    let ψ := fieldTransposeTest U (H.fields i) (H.fields_smooth G i).contDiffOn φ
    have hi : IntegrableOn (fun x => -(f x * ψ x)) (U : Set (Fin N → ℝ)) volume :=
      (S.integrable_mul_test U hfLoc ψ).integrableOn.neg
    have he : (fun x => -(f x * ψ x)) =
        (fun x => f x * fieldDerivative (H.fields i) φ x) := by
      funext x
      rw [S.fieldTransposeTest_apply, H.fieldTranspose_eq_neg G i φ φ.contDiff]
      change -(f x * -fieldDerivative (H.fields i) φ x) = _
      ring
    exact he ▸ hi
  have hitt (i : Fin q) : IntegrableOn
      (fun x => f x * fieldDerivative (H.fields i.succ) (fieldDerivative (H.fields i.succ) φ) x)
      (U : Set (Fin N → ℝ)) volume := by
    let ψ := fieldTransposeTest U (H.fields i.succ) (H.fields_smooth G i.succ).contDiffOn φ
    let χ := fieldTransposeTest U (H.fields i.succ) (H.fields_smooth G i.succ).contDiffOn ψ
    have hi : IntegrableOn (fun x => f x * χ x) (U : Set (Fin N → ℝ)) volume :=
      (S.integrable_mul_test U hfLoc χ).integrableOn
    have he : (χ : (Fin N → ℝ) → ℝ) =
        fieldDerivative (H.fields i.succ) (fieldDerivative (H.fields i.succ) φ) := by
      funext x
      rw [S.fieldTransposeTest_apply]
      have hψ : (ψ : (Fin N → ℝ) → ℝ) = fieldTranspose (H.fields i.succ) φ :=
        funext (S.fieldTransposeTest_apply U _ _ φ)
      rw [hψ, H.squareTranspose G i.succ φ φ.contDiff]
    simpa only [he] using hi
  simp_rw [sumSquaresWithDrift, add_mul, Finset.sum_mul]
  rw [integral_add hi0 (integrable_finsetSum _ (fun i _ => his i)),
    integral_finsetSum _ (fun i _ => his i), H.integral_field_test G U 0 f (hf.of_le (by simp)) φ]
  simp_rw [H.integral_square_test G U _ f (hf.of_le (by simp)) φ,
    H.sumSquaresTranspose_formula G φ φ.contDiff, mul_add, mul_neg, Finset.mul_sum]
  have hn : IntegrableOn (fun x => -(f x * fieldDerivative (H.fields 0) φ x))
      (U : Set (Fin N → ℝ)) volume := (hit 0).neg
  rw [integral_add hn (integrable_finsetSum _ (fun i _ => hitt i)),
    integral_neg, integral_finsetSum _ (fun i _ => hitt i)]

end RothschildStein.H1
