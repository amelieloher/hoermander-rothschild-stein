-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Geometry.GlobalWeakDerivative
public import HeatKernel.Geometry.GradientDuality

/-! Linear combinations of weak horizontal derivatives and their test pairings. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory RothschildStein Filter TopologicalSpace
open scoped NNReal ENNReal Topology BigOperators
namespace HeatKernel

/-- A single coordinate control selects its corresponding horizontal tangent. -/
theorem horizontalTangent_single {N q : ℕ} (hq : q ≤ N) (i : Fin q) :
    horizontalTangent hq (Pi.single i 1) = Hormander.Interface.basisVec (Fin.castLE hq i) := by
  classical
  simp [horizontalTangent, Pi.single_apply]

/-- Each horizontal generator has formal transpose equal to its negative action. -/
theorem horizontalField_transpose {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N)
    (i : Fin q) {ψ : (Fin N → ℝ) → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (x : Fin N → ℝ) :
    fieldTranspose (G.horizontalFields hq i) ψ x = -fieldDerivative (G.horizontalFields hq i) ψ x :=
  G2.leftField_transpose G (Hormander.Interface.basisVec (Fin.castLE hq i)) ψ hψ x

/-- Classical differentiation in a constant horizontal direction is the corresponding
linear combination of the generator derivatives. -/
theorem fieldDerivative_horizontalTangent {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N)
    (b : Fin q → ℝ) (ψ : (Fin N → ℝ) → ℝ) (x : Fin N → ℝ) :
    fieldDerivative (G2.leftField G (horizontalTangent hq b)) ψ x =
      ∑ i, b i * fieldDerivative (G.horizontalFields hq i) ψ x := by
  simp only [fieldDerivative, leftField_horizontalTangent, map_sum, map_smul, smul_eq_mul]

/-- The weak generator derivative gives the usual signed smooth-test pairing. -/
theorem integral_weak_horizontal_derivative_mul_test {N q : ℕ} (G : HomogeneousGroup N)
    (hq : q ≤ N) {f g : (Fin N → ℝ) → ℝ} (i : Fin q)
    (hg : hasWeakWordDeriv (G.horizontalFields hq) ⊤ [i] f g)
    (ψ : TestFunction (⊤ : Opens (Fin N → ℝ)) ℝ (⊤ : ℕ∞)) :
    (∫ x, g x * ψ x) = -(∫ x, f x * fieldDerivative (G.horizontalFields hq i) ψ x) := by
  have he := hg.2.2 ψ
  simp only [Opens.coe_top, Measure.restrict_univ, wordTranspose] at he
  simp_rw [horizontalField_transpose G hq i ψ.contDiff, mul_neg] at he
  rw [integral_neg] at he
  exact he

/-- Linear combinations of the weak horizontal derivatives are the weak derivatives in
constant horizontal directions. -/
theorem hasWeakWordDeriv_horizontal_linearCombination {N q : ℕ} (G : HomogeneousGroup N)
    (hq : q ≤ N) (b : Fin q → ℝ) {f : (Fin N → ℝ) → ℝ} (hf : Continuous f)
    (g : Fin q → (Fin N → ℝ) → ℝ)
    (hg : ∀ i, hasWeakWordDeriv (G.horizontalFields hq) ⊤ [i] f (g i)) :
    hasWeakWordDeriv (fun _ : Fin 1 => G2.leftField G (horizontalTangent hq b)) ⊤ [0]
      f (fun x => ∑ i, b i * g i x) := by
  have hgl : ∀ i, LocallyIntegrable (g i) volume := fun i =>
    locallyIntegrableOn_univ.mp (by simpa only [Opens.coe_top] using (hg i).2.1)
  have hsum : LocallyIntegrable (fun x => ∑ i, b i * g i x) volume :=
    locallyIntegrable_finsetSum Finset.univ (fun i _ => (hgl i).smul (b i))
  refine ⟨hf.locallyIntegrable.locallyIntegrableOn _, hsum.locallyIntegrableOn _, ?_⟩
  intro ψ
  have hleft : ∀ i, Integrable (fun x => b i * (g i x * ψ x)) := fun i =>
    (S.integrable_mul_test ⊤ (hg i).2.1 ψ).const_mul (b i)
  have hright : ∀ i, Integrable (fun x => b i * (f x * fieldDerivative (G.horizontalFields hq i) ψ x)) := by
    intro i
    have hd : Continuous (fieldDerivative (G.horizontalFields hq i) ψ) :=
      (ψ.contDiff.continuous_fderiv (by simp)).clm_apply (G.horizontalFields_contDiff hq i).continuous
    have hc : HasCompactSupport (fieldDerivative (G.horizontalFields hq i) ψ) :=
      ψ.hasCompactSupport.of_isClosed_subset isClosed_closure (S.tsupport_fieldDerivative_subset _ _)
    exact ((hf.mul hd).integrable_of_hasCompactSupport hc.mul_left).const_mul (b i)
  change (∫ x in (⊤ : Opens (Fin N → ℝ)), (∑ i, b i * g i x) * ψ x) =
    ∫ x in (⊤ : Opens (Fin N → ℝ)), f x * fieldTranspose (G2.leftField G (horizontalTangent hq b)) ψ x
  simp only [Opens.coe_top, Measure.restrict_univ]
  simp_rw [G2.leftField_transpose G _ ψ ψ.contDiff, fieldDerivative_horizontalTangent,
    mul_neg, Finset.sum_mul, Finset.mul_sum, mul_assoc]
  rw [integral_neg, integral_finsetSum _ (fun i _ => hleft i)]
  have hright' : ∀ i, Integrable (fun x => f x * (b i * fieldDerivative (G.horizontalFields hq i) ψ x)) := by
    intro i
    simpa only [mul_left_comm] using hright i
  rw [integral_finsetSum _ (fun i _ => hright' i)]
  simp_rw [integral_const_mul, mul_left_comm (f _) (b _)]
  simp_rw [integral_const_mul, integral_weak_horizontal_derivative_mul_test G hq _ (hg _) ψ,
    mul_neg, Finset.sum_neg_distrib]

end HeatKernel
