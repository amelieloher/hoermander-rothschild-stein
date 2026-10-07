-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.DriftAdjointBridge
public import RothschildStein.H3.SobolevOperatorData

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory TopologicalSpace
open scoped ENNReal

private theorem setIntegral_mul_test_eq {n : ℕ}
    (Ω : Opens (Fin n → ℝ)) (f : (Fin n → ℝ) → ℝ)
    (ψ : TestFunction Ω ℝ (⊤ : ℕ∞)) :
    (∫ x in (Ω : Set (Fin n → ℝ)), f x*ψ x) = ∫ x, ψ x*f x := by
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero
    (fun x hx => by simp [ψ.zero_on_compl hx])]
  simp only [mul_comm]

/-- the actual certified weak operator equation
is the distributional equation tested against the exact H1.HYP adjoint.
Forcing local integrability is derived from the operator jets. -/
theorem WeakDriftOperatorData.ofFun_adjoint_equation {n q : ℕ}
    {X : Fin (q+1) → (Fin n → ℝ) → (Fin n → ℝ)}
    {Ω : Opens (Fin n → ℝ)} {p : ℝ≥0∞} {u : (Fin n → ℝ) → ℝ}
    (D : WeakDriftOperatorData X Ω p u) (hp : 1 ≤ p)
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (F : (Fin n → ℝ) → ℝ)
    (heq : D.operator =ᵐ[volume.restrict (Ω : Set (Fin n → ℝ))] F)
    (ψ : TestFunction Ω ℝ (⊤ : ℕ∞)) :
    Distribution.ofFun Ω u volume (⊤ : ℕ∞)
      (Distribution.adjointTest Ω X (fun _ => 0) hX (by fun_prop) ψ) =
      Distribution.ofFun Ω F volume (⊤ : ℕ∞) ψ := by
  have hu := (D.first_weak 0).1
  have hF := locallyIntegrableOn_of_locallyIntegrable_restrict
    ((D.operator_memLp.ae_eq heq).locallyIntegrable hp)
  rw [Distribution.ofFun_apply hu, Distribution.ofFun_apply hF,
    adjointTest_zero_eq_driftTransposeTest]
  simp only [smul_eq_mul]
  have hb : (∫ x in (Ω : Set (Fin n → ℝ)), F x*ψ x) =
      ∫ x in (Ω : Set (Fin n → ℝ)), u x*(driftTransposeTest Ω X hX ψ) x := by
    calc
      _ = ∫ x in (Ω : Set (Fin n → ℝ)), D.operator x*ψ x :=
        integral_congr_ae (heq.symm.mul ae_eq_rfl)
      _ = ∫ x in (Ω : Set (Fin n → ℝ)), u x*sumSquaresWithDriftTranspose X ψ x :=
        D.operator_pairing hX ψ
      _ = _ := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun x =>
          congrArg (fun z => u x*z) (driftTransposeTest_apply Ω X hX ψ x).symm)
  rw [setIntegral_mul_test_eq, setIntegral_mul_test_eq] at hb
  exact hb.symm

end RothschildStein.H3
