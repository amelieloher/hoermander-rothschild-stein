-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.WeakDerivativeLift
public import RothschildStein.S.DistributionRestriction
public import RothschildStein.S.DistributionWords
public import RothschildStein.Definitions.hasDistributionEquation
public import RothschildStein.Definitions.hasDistributionEquationWithDrift

/-!
# The fiber test map and adjoint intertwining

The lifting step of the proof of BB Thm 11.62 (pp. 608-610, (11.101)). A `FiberIntegration Uo Vo`
consists of a fiber setting (`FiberSetting`) and the fiber integral
`J φ (x) = ∫ φ(x, t) dt` as a *continuous linear* map of tests `D(Uo) → D(Vo)`. For a lifted chart
it is supplied by the `fiber_average` field (`RothschildStein.P2.liftedChartFiberIntegration`); for
any `FiberSetting` it is `FiberSetting.fiberIntegration` (`SmoothingFiberCLM`: continuity proved from
the seminorm bounds of BB p. 608).
The lifted distribution is `T̃ = T ∘ J` (`FiberIntegration.lift`).

Since the vertical divergences integrate to zero, `J` intertwines the transposes of the triangular
lift with those of the base fields, `J (X̃ᵢ^* φ) = Xᵢ^* (J φ)` (`FiberSetting.test_fieldTransposeTest`),
hence `J (L̃^* φ) = L^* (J φ)` for `L = ∑ Xᵢ²` and for `L = ∑ Xᵢ² + X₀`, and `L̃ T̃ = f̃` whenever
`L T = f`, with `f̃ = f ∘ π` (`hasDistributionEquation_lift`, `hasDistributionEquationWithDrift_lift`)
without ever expanding the square of a variable coefficient vertical field.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped ENNReal Topology BigOperators Distributions CompactConvergenceCLM
namespace RothschildStein.P2
variable {n m : ℕ}

/-- A regular distribution paired with a test: `ofFun Ω f φ = ∫_Ω f φ`. -/
theorem ofFun_apply_eq_setIntegral {N : ℕ} (Ω : Opens (Fin N → ℝ)) {f : (Fin N → ℝ) → ℝ}
    (hf : LocallyIntegrableOn f (Ω : Set (Fin N → ℝ)) volume) (φ : TestFunction Ω ℝ (⊤ : ℕ∞)) :
    Distribution.ofFun Ω f volume (⊤ : ℕ∞) φ = ∫ x in (Ω : Set (Fin N → ℝ)), f x * φ x := by
  rw [Distribution.ofFun_apply hf]
  have hz : ∀ x, x ∉ (Ω : Set (Fin N → ℝ)) → f x * φ x = 0 := by
    intro x hx
    simp [φ.zero_on_compl hx]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero hz]
  simp only [smul_eq_mul, mul_comm]

/-- The fiber integration of tests `J φ (x) = ∫ φ(x, t) dt` as a continuous
linear map `C_c^∞(Uo) → C_c^∞(Vo)`, together with the fiber setting (projection into `Vo`, bounded
fiber volumes, smoothness of fiber integrals) it is built on. For a lifted chart the continuous
linear map is the `fiber_average` field of `LiftedChart` (BB p. 608, (11.101); p. 584). -/
structure FiberIntegration (Uo : Opens (Fin (n + m) → ℝ)) (Vo : Opens (Fin n → ℝ)) where
  /-- The fiber setting of `Uo` over `Vo`. -/
  setting : FiberSetting Uo Vo
  /-- The fiber integration `J : D(Uo) → D(Vo)`, continuous and linear. -/
  J : TestFunction Uo ℝ (⊤ : ℕ∞) →L[ℝ] TestFunction Vo ℝ (⊤ : ℕ∞)
  /-- `J φ (x) = ∫ φ(x, t) dt`. -/
  J_apply : ∀ (φ : TestFunction Uo ℝ (⊤ : ℕ∞)) (x : Fin n → ℝ),
    J φ x = ∫ t : Fin m → ℝ, φ (joinPoint x t)

namespace FiberIntegration

variable {Uo : Opens (Fin (n + m) → ℝ)} {Vo : Opens (Fin n → ℝ)} (F : FiberIntegration Uo Vo)

/-- The continuous fiber integration is the fiber integral `FiberSetting.test`. -/
theorem J_eq_test (φ : TestFunction Uo ℝ (⊤ : ℕ∞)) : F.J φ = F.setting.test φ :=
  TestFunction.ext fun x => F.J_apply φ x

/-- The lifted distribution `T̃ = T ∘ J = π^* T` on `Uo`. -/
def lift : Distribution Vo ℝ (⊤ : ℕ∞) →L[ℝ] Distribution Uo ℝ (⊤ : ℕ∞) :=
  F.J.precompCompactConvergenceCLM ℝ

/-- `T̃ (φ) = T (J φ)`: the defining formula of the lift (BB p. 608, (11.101)). -/
theorem lift_apply (T : Distribution Vo ℝ (⊤ : ℕ∞)) (φ : TestFunction Uo ℝ (⊤ : ℕ∞)) :
    F.lift T φ = T (F.J φ) := rfl

theorem lift_apply_test (T : Distribution Vo ℝ (⊤ : ℕ∞)) (φ : TestFunction Uo ℝ (⊤ : ℕ∞)) :
    F.lift T φ = T (F.setting.test φ) := by
  rw [lift_apply, J_eq_test]

/-- The lift of a regular distribution `f` is the regular distribution `f ∘ π`. -/
theorem lift_ofFun {f : (Fin n → ℝ) → ℝ} (hf : LocallyIntegrableOn f (Vo : Set (Fin n → ℝ)) volume) :
    F.lift (Distribution.ofFun Vo f volume (⊤ : ℕ∞)) =
      Distribution.ofFun Uo (fun ξ => f (basePoint ξ)) volume (⊤ : ℕ∞) := by
  ext ψ
  rw [lift_apply_test, ofFun_apply_eq_setIntegral Vo hf,
    ofFun_apply_eq_setIntegral Uo (F.setting.locallyIntegrableOn_comp_basePoint hf)]
  exact (F.setting.integral_comp_mul_test hf ψ).symm

end FiberIntegration

namespace FiberSetting

variable {Uo : Opens (Fin (n + m) → ℝ)} {Vo : Opens (Fin n → ℝ)} (S : FiberSetting Uo Vo)
include S

theorem test_sum {ι : Type*} (s : Finset ι) (φ : ι → TestFunction Uo ℝ (⊤ : ℕ∞)) :
    S.test (∑ i ∈ s, φ i) = ∑ i ∈ s, S.test (φ i) :=
  map_sum S.testLM φ s

theorem test_add (φ ψ : TestFunction Uo ℝ (⊤ : ℕ∞)) :
    S.test (φ + ψ) = S.test φ + S.test ψ :=
  map_add S.testLM φ ψ

/-- `J (L̃^* φ) = L^* (J φ)` for `L = ∑ Xᵢ²`: apply the first-order
identity `J (X̃ᵢ^* φ) = Xᵢ^* (J φ)` twice, to `φ` and to `X̃ᵢ^* φ`, and sum (BB p. 609). -/
theorem test_sumSquaresTransposeTest {q : ℕ} (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (P : Fin q → Fin m → MvPolynomial (Fin (n + m)) ℝ)
    (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (triangularLift X P i) (Uo : Set (Fin (n + m) → ℝ)))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Vo : Set (Fin n → ℝ)))
    (φ : TestFunction Uo ℝ (⊤ : ℕ∞)) :
    S.test (sumSquaresTransposeTest Uo (triangularLift X P) hXt φ) =
      sumSquaresTransposeTest Vo X hX (S.test φ) := by
  unfold sumSquaresTransposeTest
  rw [S.test_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [S.test_fieldTransposeTest X P hXt hX i, S.test_fieldTransposeTest X P hXt hX i]

/-- `J (L̃^* φ) = L^* (J φ)` for `L = ∑ Xᵢ² + X₀`: the drift identity
`J (X̃₀^* φ) = X₀^* (J φ)` is added once to the sum of squares of the other fields. -/
theorem test_sumSquaresWithDriftTransposeTest {q : ℕ} (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (P : Fin (q + 1) → Fin m → MvPolynomial (Fin (n + m)) ℝ)
    (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (triangularLift X P i) (Uo : Set (Fin (n + m) → ℝ)))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Vo : Set (Fin n → ℝ)))
    (φ : TestFunction Uo ℝ (⊤ : ℕ∞)) :
    S.test (sumSquaresWithDriftTransposeTest Uo (triangularLift X P) hXt φ) =
      sumSquaresWithDriftTransposeTest Vo X hX (S.test φ) := by
  unfold sumSquaresWithDriftTransposeTest
  rw [S.test_add, S.test_sum, S.test_fieldTransposeTest X P hXt hX 0]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [S.test_fieldTransposeTest X P hXt hX i.succ, S.test_fieldTransposeTest X P hXt hX i.succ]

end FiberSetting

namespace FiberIntegration

variable {Uo : Opens (Fin (n + m) → ℝ)} {Vo : Opens (Fin n → ℝ)} (F : FiberIntegration Uo Vo)

/-- `J (L̃^* φ) = L^* (J φ)`, `L = ∑ Xᵢ²`. -/
theorem J_sumSquaresTransposeTest {q : ℕ} (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (P : Fin q → Fin m → MvPolynomial (Fin (n + m)) ℝ)
    (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (triangularLift X P i) (Uo : Set (Fin (n + m) → ℝ)))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Vo : Set (Fin n → ℝ)))
    (φ : TestFunction Uo ℝ (⊤ : ℕ∞)) :
    F.J (sumSquaresTransposeTest Uo (triangularLift X P) hXt φ) =
      sumSquaresTransposeTest Vo X hX (F.J φ) := by
  rw [J_eq_test, J_eq_test, F.setting.test_sumSquaresTransposeTest X P hXt hX]

/-- `J (L̃^* φ) = L^* (J φ)`, `L = ∑ Xᵢ² + X₀`. -/
theorem J_sumSquaresWithDriftTransposeTest {q : ℕ} (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (P : Fin (q + 1) → Fin m → MvPolynomial (Fin (n + m)) ℝ)
    (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (triangularLift X P i) (Uo : Set (Fin (n + m) → ℝ)))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Vo : Set (Fin n → ℝ)))
    (φ : TestFunction Uo ℝ (⊤ : ℕ∞)) :
    F.J (sumSquaresWithDriftTransposeTest Uo (triangularLift X P) hXt φ) =
      sumSquaresWithDriftTransposeTest Vo X hX (F.J φ) := by
  rw [J_eq_test, J_eq_test, F.setting.test_sumSquaresWithDriftTransposeTest X P hXt hX]

/-- `L T = f` on the base implies `L̃ T̃ = f̃` on the lift, with
`f̃ = f ∘ π` (no drift; BB p. 609, (11.101)). -/
theorem hasDistributionEquation_lift {q : ℕ} (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (P : Fin q → Fin m → MvPolynomial (Fin (n + m)) ℝ)
    (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (triangularLift X P i) (Uo : Set (Fin (n + m) → ℝ)))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Vo : Set (Fin n → ℝ)))
    {T : Distribution Vo ℝ (⊤ : ℕ∞)} {f : (Fin n → ℝ) → ℝ}
    (h : hasDistributionEquation Vo X hX T f) :
    hasDistributionEquation Uo (triangularLift X P) hXt (F.lift T) (fun ξ => f (basePoint ξ)) := by
  refine ⟨F.setting.locallyIntegrableOn_comp_basePoint h.1, fun φ => ?_⟩
  rw [lift_apply, F.J_sumSquaresTransposeTest X P hXt hX, h.2, ← lift_ofFun F h.1, lift_apply]

/-- The same with drift: `L = ∑ Xᵢ² + X₀`. -/
theorem hasDistributionEquationWithDrift_lift {q : ℕ} (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (P : Fin (q + 1) → Fin m → MvPolynomial (Fin (n + m)) ℝ)
    (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (triangularLift X P i) (Uo : Set (Fin (n + m) → ℝ)))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Vo : Set (Fin n → ℝ)))
    {T : Distribution Vo ℝ (⊤ : ℕ∞)} {f : (Fin n → ℝ) → ℝ}
    (h : hasDistributionEquationWithDrift Vo X hX T f) :
    hasDistributionEquationWithDrift Uo (triangularLift X P) hXt (F.lift T)
      (fun ξ => f (basePoint ξ)) := by
  refine ⟨F.setting.locallyIntegrableOn_comp_basePoint h.1, fun φ => ?_⟩
  rw [lift_apply, F.J_sumSquaresWithDriftTransposeTest X P hXt hX, h.2, ← lift_ofFun F h.1,
    lift_apply]

end FiberIntegration

end RothschildStein.P2
