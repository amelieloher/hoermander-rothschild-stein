-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.GeneratorTransferCoefficients
public import RothschildStein.P1.TypeKernelHomogeneousMultiplier
public import RothschildStein.P1.ContinuityPositive

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MvPolynomial
namespace RothschildStein.P1.LiftedChart
variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  (C : LiftedChart w s Ω hΩ X x₀ m) (F : KernelFrame (n+m))

/-- The canonical transfer kernel multiplies the original kernel
by the polynomial left-to-right basis coefficient, evaluated at Θ
(BB Lemma 11.23, pp. 554–555; Theorem 11.24, pp. 555–558). -/
def generatorTransferKernel (i : Fin k) (j : Fin (n+m))
    (κ : (Fin (n+m) → ℝ) → (Fin (n+m) → ℝ) → ℝ)
    (ξ η : Fin (n+m) → ℝ) : ℝ :=
  eval (F.Θ η ξ) (C.generatorTransferCoefficient i j) * κ ξ η

/-- Every transfer kernel has exactly the required improved type
at all regularity budgets. Coefficients below the generator weight vanish
identically; no endpoint-limit or type assertion is assumed (BB pp. 554–558). -/
theorem isTypeKernel_generatorTransferKernel
    (hF : C.IsLiftedFrame F) {lam : ℕ}
    {κ : (Fin (n+m) → ℝ) → (Fin (n+m) → ℝ) → ℝ}
    (hκ : IsTypeKernel F lam κ) (i : Fin k) (j : Fin (n+m)) :
    IsTypeKernel F (lam + wordWeight w (C.B j) - (w i : ℕ))
      (C.generatorTransferKernel F i j κ) := by
  classical
  have hVU : (F.V : Set (Fin (n+m) → ℝ)) ⊆ C.U :=
    subset_closure.trans hF.closure_subset
  by_cases hj : (w i : ℕ) ≤ C.G.weight j
  · have hhom : ∀ r : ℝ, 0 < r → ∀ u : Fin (n+m) → ℝ,
        eval (F.G.dilate r u) (C.generatorTransferCoefficient i j) =
          r ^ ((C.G.weight j - (w i : ℕ) : ℕ) : ℝ) *
            eval u (C.generatorTransferCoefficient i j) := by
      intro r hr u
      rw [hF.G_eq, C.generatorTransferCoefficient_eval_dilate i j r hr u,
        Nat.cast_sub hj]
    have ht := C.isTypeKernel_homogeneousModelMultiplier F hF.Θ_eq hVU hκ
      (fun u => eval u (C.generatorTransferCoefficient i j))
      (G2.contDiff_eval _) (C.G.weight j - (w i : ℕ)) hhom
    have hd : lam + (C.G.weight j - (w i : ℕ)) =
        lam + wordWeight w (C.B j) - (w i : ℕ) := by
      rw [← (C.basis_weight j).2.2]
      omega
    rw [hd] at ht
    exact ht
  · have hz := C.generatorTransferCoefficient_zero_of_weight_lt i j (by omega)
    have he : C.generatorTransferKernel F i j κ = fun _ _ => 0 := by
      funext ξ η
      simp only [generatorTransferKernel, hz, map_zero, zero_mul]
    rw [he]
    exact IsTypeKernel.zero

/-- The positive-type transfer operator has no diagonal
multiplier. Its kernel is canonical, so it is shared by every requested
regularity budget (BB Theorem 11.24, pp. 555–558). -/
def generatorTransferOperator (hF : C.IsLiftedFrame F) {lam : ℕ}
    (T : TypeOperator F lam) (i : Fin k) (j : Fin (n+m)) :
    TypeOperator F (lam + wordWeight w (C.B j) - (w i : ℕ)) where
  kernel := C.generatorTransferKernel F i j T.kernel
  isType := C.isTypeKernel_generatorTransferKernel F hF T.isType i j
  mult := 0
  mult_eq_zero := by intro _; rfl

end RothschildStein.P1.LiftedChart
