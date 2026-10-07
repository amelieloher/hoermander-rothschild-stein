-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.OutputDifferentiatedOperator
public import RothschildStein.P1.TypeZeroOperatorTranspose
public import RothschildStein.P1.RightDifferentiationStandard

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
namespace RothschildStein.P1.LiftedChart
variable {n k m q : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {F : KernelFrame (n + m)}
  {H : H1.StandingHypotheses C.G q} {K : H1.FundamentalKernel C.G H}
  {hQ : 2 < (C.G.homogeneousDimension : ℝ)}

/-- Full left differentiation on standard frames, including the
critical type-zero output, obtained from the proved right differentiation
and the actual bilinear transpose with its multiplier. -/
theorem leftDifferentiation_standard (hF : C.IsStandardFrame F H K hQ) : LeftDifferentiation F w C.Xl := by
  intro lam T i hw
  obtain ⟨A, hAk, _, hAp⟩ := C.exists_type_transpose_standard hF T
  let B := C.inputDifferentiatedOperator hF A i hw
  obtain ⟨W, hWk, _, hWp⟩ := C.exists_type_transpose_standard hF B
  have hW : W.kernel = fun ξ η => cutoffInputTranspose F (C.Xl i)
      (fun x y => T.kernel y x) η ξ := by
    rw [hWk]
    simp only [B, inputDifferentiatedOperator, hAk]
  let S := C.outputDifferentiatedOperator hF T i hw W
  refine ⟨S, ?_⟩
  intro f
  refine ⟨T.locallyIntegrableOn_apply_test hF f, S.locallyIntegrableOn_apply_test hF f, ?_⟩
  intro ψ
  let dψ := RothschildStein.S.wordDerivativeTest F.V C.Xl hF.lifted.contDiffOn_Xl [i] ψ
  let τψ := RothschildStein.wordTransposeTest F.V C.Xl hF.lifted.contDiffOn_Xl [i] ψ
  have hd : A.apply dψ = B.apply ψ :=
    C.inputDifferentiatedOperator_apply hF A i hw hF.lifted.contDiffOn_Xl ψ
  have hpair : (∫ ξ, ψ ξ * W.apply f ξ) = ∫ ξ, T.apply f ξ * dψ ξ := by
    rw [← hWp ψ f, ← hd, ← hAp f dψ]
    apply integral_congr_ae
    exact Eventually.of_forall (fun ξ => mul_comm _ _)
  have hτeq : (τψ : (Fin (n + m) → ℝ) → ℝ) = wordTranspose C.Xl [i] ψ :=
    RothschildStein.S.wordTransposeTest_apply F.V C.Xl hF.lifted.contDiffOn_Xl [i] ψ
  have hτ (ξ : Fin (n + m) → ℝ) (hξ : ξ ∈ (F.V : Set (Fin (n + m) → ℝ))) :
      τψ ξ = -dψ ξ - ψ ξ * Hormander.Interface.euclideanDivergence (C.Xl i) ξ := by
    rw [congrFun hτeq ξ]
    change fieldTranspose (C.Xl i) ψ ξ =
      -fieldDerivative (C.Xl i) ψ ξ - ψ ξ * Hormander.Interface.euclideanDivergence (C.Xl i) ξ
    exact RothschildStein.S.fieldTranspose_formula (C.Xl i) ψ ξ
      (((hF.lifted.contDiffOn_Xl i).contDiffAt (F.V.isOpen.mem_nhds hξ)).differentiableAt (by simp))
      (ψ.contDiff.differentiable (by simp)).differentiableAt
  have he : (fun ξ => S.apply f ξ * ψ ξ) =
      fun ξ => - (ψ ξ * W.apply f ξ) + T.apply f ξ * τψ ξ + T.apply f ξ * dψ ξ := by
    funext ξ
    by_cases hξ : ξ ∈ (F.V : Set (Fin (n + m) → ℝ))
    · have hs := C.outputDifferentiatedOperator_apply hF T i hw W hW f hξ
      change S.apply f ξ = _ at hs
      rw [hs, hτ ξ hξ]
      ring
    · have hψ : ψ ξ = 0 := image_eq_zero_of_notMem_tsupport (fun ht => hξ (ψ.tsupport_subset ht))
      have hdψ : dψ ξ = 0 := image_eq_zero_of_notMem_tsupport (fun ht => hξ (dψ.tsupport_subset ht))
      have hτψ : τψ ξ = 0 := image_eq_zero_of_notMem_tsupport (fun ht => hξ (τψ.tsupport_subset ht))
      simp only [hψ, hdψ, hτψ, zero_mul, mul_zero, neg_zero, add_zero]
  have hiW : Integrable (fun ξ => ψ ξ * W.apply f ξ) := by
    simpa only [mul_comm] using RothschildStein.S.integrable_mul_test F.V (W.locallyIntegrableOn_apply_test hF f) ψ
  have hiτ := RothschildStein.S.integrable_mul_test F.V (T.locallyIntegrableOn_apply_test hF f) τψ
  have hid := RothschildStein.S.integrable_mul_test F.V (T.locallyIntegrableOn_apply_test hF f) dψ
  have hglobal : (∫ ξ, S.apply f ξ * ψ ξ) = ∫ ξ, T.apply f ξ * τψ ξ := by
    have h123 := integral_add (hiW.neg.add hiτ) hid
    have h12 := integral_add hiW.neg hiτ
    simp only [Pi.add_apply, Pi.neg_apply] at h123 h12
    rw [he, h123, h12, integral_neg, hpair]
    ring
  have hzLeft : ∀ ξ, ξ ∉ (F.V : Set (Fin (n + m) → ℝ)) → S.apply f ξ * ψ ξ = 0 := by
    intro ξ hξ
    rw [image_eq_zero_of_notMem_tsupport (fun ht => hξ (ψ.tsupport_subset ht)), mul_zero]
  have hzRight : ∀ ξ, ξ ∉ (F.V : Set (Fin (n + m) → ℝ)) → T.apply f ξ * τψ ξ = 0 := by
    intro ξ hξ
    rw [image_eq_zero_of_notMem_tsupport (fun ht => hξ (τψ.tsupport_subset ht)), mul_zero]
  rw [← hτeq]
  change (∫ ξ in (F.V : Set (Fin (n + m) → ℝ)), S.apply f ξ * ψ ξ) =
    ∫ ξ in (F.V : Set (Fin (n + m) → ℝ)), T.apply f ξ * τψ ξ
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzLeft,
    setIntegral_eq_integral_of_forall_compl_eq_zero hzRight]
  exact hglobal

end RothschildStein.P1.LiftedChart
