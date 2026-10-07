-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.WeakDeriv
public import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology
namespace RothschildStein.S
variable {n : ℕ}

/-- Coordinate integration by parts on an open set against a test
(BB p. 68). The function being differentiated needs only local C¹ regularity. -/
theorem integral_coordinate_mul_test (Ω : Opens (Fin n → ℝ))
    (g : (Fin n → ℝ) → ℝ) (hg : ContDiffOn ℝ 1 g (Ω : Set (Fin n → ℝ)))
    (ψ : TestFunction Ω ℝ (⊤ : ℕ∞)) (v : Fin n → ℝ) :
    (∫ x in (Ω : Set (Fin n → ℝ)), fderiv ℝ g x v * ψ x) =
      -(∫ x in (Ω : Set (Fin n → ℝ)), g x * fderiv ℝ ψ x v) := by
  have hgc := hg.continuousOn.locallyIntegrableOn (μ := volume) Ω.isOpen.measurableSet
  have hdc : ContinuousOn (fun x => fderiv ℝ g x v) (Ω : Set (Fin n → ℝ)) :=
    (hg.continuousOn_fderiv_of_isOpen Ω.isOpen (by rfl)).clm_apply continuousOn_const
  have hi₁ := integrable_mul_test Ω (hdc.locallyIntegrableOn (μ := volume) Ω.isOpen.measurableSet) ψ
  let dψ : TestFunction Ω ℝ (⊤ : ℕ∞) := TestFunction.lineDerivCLM (k := (⊤ : ℕ∞)) ℝ v ψ
  have hdψ : (dψ : (Fin n → ℝ) → ℝ) = fun x => fderiv ℝ ψ x v := by
    funext x
    rw [TestFunction.lineDerivCLM_apply_of_le (by simp)]
    exact ψ.contDiff.differentiable (by simp) |>.differentiableAt.lineDeriv_eq_fderiv
  have hi₂ : Integrable (fun x => g x * fderiv ℝ ψ x v) volume := by
    simpa only [hdψ] using integrable_mul_test Ω hgc dψ
  have hi₃ := integrable_mul_test Ω hgc ψ
  have hibp := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (μ := volume) hi₁ hi₂ hi₃
    (fun x hx => (hg.contDiffAt (Ω.isOpen.mem_nhds (ψ.tsupport_subset hx))).differentiableAt (by norm_num))
    (fun x _ => ψ.contDiff.differentiable (by simp) |>.differentiableAt)
  have hs₁ : (∫ x in (Ω : Set (Fin n → ℝ)), fderiv ℝ g x v * ψ x) =
      ∫ x, fderiv ℝ g x v * ψ x :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      simp [ψ.zero_on_compl hx])
  have hs₂ : (∫ x in (Ω : Set (Fin n → ℝ)), g x * fderiv ℝ ψ x v) =
      ∫ x, g x * fderiv ℝ ψ x v :=
    setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
      have hz : fderiv ℝ ψ x = 0 := fderiv_of_notMem_tsupport ℝ
        (fun ht => hx (ψ.tsupport_subset ht))
      simp [hz])
  rw [hs₁, hs₂]
  linarith

/-- Field integration by parts for locally C¹ functions and test functions
(BB (2.1)–(2.3), p. 68). -/
theorem integral_fieldDerivative_mul_test (Ω : Opens (Fin n → ℝ))
    (V : (Fin n → ℝ) → (Fin n → ℝ))
    (hV : ContDiffOn ℝ (⊤ : ℕ∞) V (Ω : Set (Fin n → ℝ)))
    (g : (Fin n → ℝ) → ℝ) (hg : ContDiffOn ℝ 1 g (Ω : Set (Fin n → ℝ)))
    (φ : TestFunction Ω ℝ (⊤ : ℕ∞)) :
    (∫ x in (Ω : Set (Fin n → ℝ)), fieldDerivative V g x * φ x) =
      ∫ x in (Ω : Set (Fin n → ℝ)), g x * fieldTranspose V φ x := by
  let ψ : Fin n → TestFunction Ω ℝ (⊤ : ℕ∞) := fun j =>
    testMultiplierOn Ω (fun x => V x j) ((contDiff_apply ℝ ℝ j).comp_contDiffOn hV) φ
  have he : ∀ x, fieldDerivative V g x * φ x =
      ∑ j : Fin n, fderiv ℝ g x (Hormander.Interface.basisVec j) * ψ j x := by
    intro x
    rw [fieldDerivative, differential_coordinates, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    change V x j * fderiv ℝ g x _ * φ x = fderiv ℝ g x _ * (φ x * V x j)
    ring
  have hdcoe : ∀ j, (TestFunction.lineDerivCLM (k := (⊤ : ℕ∞)) ℝ (Hormander.Interface.basisVec j)
      (ψ j) : (Fin n → ℝ) → ℝ) =
      fun x => fderiv ℝ (ψ j) x (Hormander.Interface.basisVec j) := by
    intro j
    funext x
    rw [TestFunction.lineDerivCLM_apply_of_le (by simp)]
    exact (ψ j).contDiff.differentiable (by simp) |>.differentiableAt.lineDeriv_eq_fderiv
  have hs : ∀ j, IntegrableOn (fun x => fderiv ℝ g x
      (Hormander.Interface.basisVec j) * ψ j x) (Ω : Set (Fin n → ℝ)) volume := by
    intro j
    exact (integrable_mul_test Ω (((hg.continuousOn_fderiv_of_isOpen Ω.isOpen (by rfl)).clm_apply continuousOn_const).locallyIntegrableOn (μ := volume) Ω.isOpen.measurableSet) (ψ j)).integrableOn
  have ht : ∀ j, IntegrableOn (fun x => g x *
      fderiv ℝ (ψ j) x (Hormander.Interface.basisVec j)) (Ω : Set (Fin n → ℝ)) volume := by
    intro j
    have hp := integrable_mul_test Ω (hg.continuousOn.locallyIntegrableOn (μ := volume) Ω.isOpen.measurableSet)
      (TestFunction.lineDerivCLM (k := (⊤ : ℕ∞)) ℝ (Hormander.Interface.basisVec j) (ψ j))
    rw [hdcoe j] at hp
    exact hp.integrableOn
  simp_rw [he]
  rw [integral_finsetSum _ (fun j _ => hs j)]
  simp_rw [integral_coordinate_mul_test Ω g hg]
  rw [Finset.sum_neg_distrib, ← integral_finsetSum _ (fun j _ => ht j), ← integral_neg]
  apply integral_congr_ae
  filter_upwards [] with x
  have hc := fieldTransposeTest_apply Ω V hV φ x
  unfold fieldTransposeTest at hc
  simp only [neg_apply] at hc
  let ev : TestFunction Ω ℝ (⊤ : ℕ∞) →+ ℝ :=
    { toFun := fun ψ => ψ x, map_zero' := rfl, map_add' := fun _ _ => rfl }
  change -ev (∑ j : Fin n, _) = _ at hc
  rw [map_sum] at hc
  change -(∑ j : Fin n, ev (TestFunction.lineDerivCLM
    (k := (⊤ : ℕ∞)) ℝ (Hormander.Interface.basisVec j) (ψ j))) = _ at hc
  have hj : ∀ j : Fin n, ev (TestFunction.lineDerivCLM
      (k := (⊤ : ℕ∞)) ℝ (Hormander.Interface.basisVec j) (ψ j)) =
      fderiv ℝ (ψ j) x (Hormander.Interface.basisVec j) := by
    intro j
    change (TestFunction.lineDerivCLM (k := (⊤ : ℕ∞)) ℝ
      (Hormander.Interface.basisVec j) (ψ j)) x = _
    rw [hdcoe j]
  simp_rw [hj] at hc
  change -(∑ j : Fin n, fderiv ℝ (ψ j) x _) = fieldTranspose V φ x at hc
  rw [← Finset.mul_sum, ← mul_neg, hc]

end RothschildStein.S
