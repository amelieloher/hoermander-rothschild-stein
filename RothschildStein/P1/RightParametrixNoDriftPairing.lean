-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.RightParametrixNoDriftError
public import RothschildStein.P1.RightParametrixPairing
public import RothschildStein.Definitions.sumSquaresTransposeTest

/-!
# The model-variable pairing, without drift, of the right pole computation

The no-drift counterpart of `RightParametrixPairing`. Fix `η ∈ C.U`, tests `α, βᵢ, λ` on the target
of the endpoint chart `e η` and set

`T(α, β, λ) = 𝓛ᵀ α + Eᵀ α + ∑ᵢ 2 Zᵢᵀ βᵢ + λ`  (`LiftedChart.poleTransposeNoDrift`),

`𝓛 = ∑ᵢ Yᵢ²`. For a function `g` with the integration-by-parts pairs of `ErrorIbpNoDrift` one has
`∫ g T = ∫ g 𝓛ᵀα + ∫ (E g) α + ∑ᵢ ∫ 2 (Zᵢ g) βᵢ + ∫ g λ` (`integral_mul_poleTransposeNoDrift`).
For smooth `g` the model part is `∫ (𝓛 g) α`; for the H1 fundamental kernel of the no-drift model
it is `α(0)` (`𝓛Γ = δ₀`), the pole contribution of the right pole computation.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology
open RothschildStein.P2
namespace RothschildStein.P1

section TestCoe

variable {n : ℕ}

/-- The function underlying the bundled no-drift transpose test is the
transpose `sumSquaresTranspose`. -/
theorem sumSquaresTransposeTest_coe_noDrift {q : ℕ} (Ω : Opens (Fin n → ℝ))
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (φ : TestFunction Ω ℝ (⊤ : ℕ∞)) :
    (sumSquaresTransposeTest Ω X hX φ : (Fin n → ℝ) → ℝ) = sumSquaresTranspose X φ := by
  funext x
  let ev : TestFunction Ω ℝ (⊤ : ℕ∞) →+ ℝ :=
    { toFun := fun ψ => ψ x, map_zero' := rfl, map_add' := fun _ _ => rfl }
  have h : (sumSquaresTransposeTest Ω X hX φ : (Fin n → ℝ) → ℝ) x =
      ev (∑ i : Fin q, fieldTransposeTest Ω (X i) (hX i)
          (fieldTransposeTest Ω (X i) (hX i) φ)) := rfl
  rw [h, map_sum]
  unfold sumSquaresTranspose
  simp only [ev, AddMonoidHom.coe_mk, ZeroHom.coe_mk, S.fieldTransposeTest_apply,
    S.fieldTransposeTest_coe]

/-- Smoothness of `L = ∑ Xᵢ²` on functions smooth on an open set. -/
theorem contDiffOn_sumSquares_noDrift {q : ℕ} (Ω : Opens (Fin n → ℝ))
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ))) {f : (Fin n → ℝ) → ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (Ω : Set (Fin n → ℝ))) :
    ContDiffOn ℝ (⊤ : ℕ∞) (sumSquares X f) (Ω : Set (Fin n → ℝ)) := by
  have h1 : ∀ i : Fin q, ContDiffOn ℝ (⊤ : ℕ∞)
      (fieldDerivative (X i) (fieldDerivative (X i) f)) (Ω : Set (Fin n → ℝ)) := fun i =>
    S.contDiffOn_fieldDerivative Ω (X i) _ (hX i)
      (S.contDiffOn_fieldDerivative Ω (X i) f (hX i) hf)
  exact ContDiffOn.sum fun i _ => h1 i

end TestCoe

namespace LiftedChart

variable {n q s m : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  (C : LiftedChart (fun _ : Fin q => (1 : ℕ+)) s Ω hΩ X x₀ m)

/-- The bundled transposed no-drift error operator on tests on the
target of `e η`. -/
def errorTransposeTestNoDrift {η : Fin (n + m) → ℝ} (hη : η ∈ C.U)
    (φ : TestFunction (C.modelOpens η) ℝ (⊤ : ℕ∞)) : TestFunction (C.modelOpens η) ℝ (⊤ : ℕ∞) :=
  ∑ i : Fin q, (fieldTransposeTest (C.modelOpens η) (C.R [i] η)
      (contDiffOn_R_model_noDrift hη _)
      (fieldTransposeTest (C.modelOpens η) (C.Y i) (contDiffOn_Y_model_noDrift i) φ) +
    fieldTransposeTest (C.modelOpens η) (zField C i η) (contDiffOn_zField_model_noDrift hη i)
      (fieldTransposeTest (C.modelOpens η) (C.R [i] η) (contDiffOn_R_model_noDrift hη _) φ))

theorem errorTransposeTestNoDrift_coe {η : Fin (n + m) → ℝ} (hη : η ∈ C.U)
    (φ : TestFunction (C.modelOpens η) ℝ (⊤ : ℕ∞)) :
    (C.errorTransposeTestNoDrift hη φ : (Fin (n + m) → ℝ) → ℝ) =
      C.errorTransposeNoDrift η φ := by
  funext x
  let ev : TestFunction (C.modelOpens η) ℝ (⊤ : ℕ∞) →+ ℝ :=
    { toFun := fun ψ => ψ x, map_zero' := rfl, map_add' := fun _ _ => rfl }
  have t1 : ∀ i : Fin q, (fieldTransposeTest (C.modelOpens η) (C.R [i] η)
      (contDiffOn_R_model_noDrift hη _)
      (fieldTransposeTest (C.modelOpens η) (C.Y i) (contDiffOn_Y_model_noDrift i) φ)) x =
      fieldTranspose (C.R [i] η) (fieldTranspose (C.Y i) φ) x := fun i => by
    rw [S.fieldTransposeTest_apply, S.fieldTransposeTest_coe]
  have t2 : ∀ i : Fin q, (fieldTransposeTest (C.modelOpens η) (zField C i η)
      (contDiffOn_zField_model_noDrift hη i)
      (fieldTransposeTest (C.modelOpens η) (C.R [i] η) (contDiffOn_R_model_noDrift hη _) φ)) x =
      fieldTranspose (zField C i η) (fieldTranspose (C.R [i] η) φ) x := fun i => by
    rw [S.fieldTransposeTest_apply, S.fieldTransposeTest_coe]
  have h : (C.errorTransposeTestNoDrift hη φ : (Fin (n + m) → ℝ) → ℝ) x =
      ev (C.errorTransposeTestNoDrift hη φ) := rfl
  rw [h]
  unfold errorTransposeTestNoDrift
  rw [map_sum]
  simp only [map_add]
  unfold errorTransposeNoDrift
  exact Finset.sum_congr rfl (fun i _ => congrArg₂ (· + ·) (t1 i) (t2 i))

/-- The transposed model operator combination of the no-drift right pole
computation, `T(α, β, λ) = 𝓛ᵀ α + Eᵀ α + ∑ᵢ 2 Zᵢᵀ βᵢ + λ`. -/
def poleTransposeNoDrift (η : Fin (n + m) → ℝ) (α : (Fin (n + m) → ℝ) → ℝ)
    (β : Fin q → (Fin (n + m) → ℝ) → ℝ) (lam : (Fin (n + m) → ℝ) → ℝ)
    (u : Fin (n + m) → ℝ) : ℝ :=
  sumSquaresTranspose C.Y α u + C.errorTransposeNoDrift η α u +
    ∑ i : Fin q, 2 * fieldTranspose (zField C i η) (β i) u + lam u

variable {C}

/-- The pairing of `g` with `T(α, β, λ)`: for `g` with the integration by parts
pairs of `ErrorIbpNoDrift`,
`∫ g T = ∫ g 𝓛ᵀα + ∫ (E g) α + ∑ᵢ ∫ 2 (Zᵢ g) βᵢ + ∫ g λ`. -/
theorem integral_mul_poleTransposeNoDrift {η : Fin (n + m) → ℝ} (hη : η ∈ C.U)
    {g : (Fin (n + m) → ℝ) → ℝ} (h : ErrorIbpNoDrift C η g)
    (α : TestFunction (C.modelOpens η) ℝ (⊤ : ℕ∞))
    (β : Fin q → TestFunction (C.modelOpens η) ℝ (⊤ : ℕ∞))
    (lam : TestFunction (C.modelOpens η) ℝ (⊤ : ℕ∞)) :
    (∫ u in (C.e η).target, g u * C.poleTransposeNoDrift η α (fun i => β i) lam u) =
      (∫ u in (C.e η).target, g u * sumSquaresTranspose C.Y α u) +
      (∫ u in (C.e η).target, C.errorOpNoDrift η g u * α u) +
      ∑ i : Fin q, (∫ u in (C.e η).target,
        2 * (fieldDerivative (zField C i η) g u * β i u)) +
      ∫ u in (C.e η).target, g u * lam u := by
  have i1 : IntegrableOn (fun u => g u * sumSquaresTranspose C.Y α u) (C.e η).target :=
    integrableOn_mul_test_target_noDrift h.loc
      (sumSquaresTransposeTest (C.modelOpens η) C.Y (fun i => contDiffOn_Y_model_noDrift i) α)
      (sumSquaresTransposeTest_coe_noDrift _ _ _ α)
  have i2 : IntegrableOn (fun u => g u * C.errorTransposeNoDrift η α u) (C.e η).target :=
    integrableOn_mul_test_target_noDrift h.loc (C.errorTransposeTestNoDrift hη α)
      (errorTransposeTestNoDrift_coe C hη α)
  have i3 : ∀ i : Fin q, IntegrableOn (fun u => g u *
      (2 * fieldTranspose (zField C i η) (β i) u)) (C.e η).target := fun i => by
    have h1 : IntegrableOn (fun u => g u * fieldTranspose (zField C i η) (β i) u)
        (C.e η).target := integrableOn_mul_test_target_noDrift h.loc
      (fieldTransposeTest (C.modelOpens η) (zField C i η) (contDiffOn_zField_model_noDrift hη i)
        (β i)) (S.fieldTransposeTest_coe _ _ _ (β i))
    have h2 : IntegrableOn (fun u => 2 * (g u * fieldTranspose (zField C i η) (β i) u))
        (C.e η).target := h1.const_mul 2
    exact IntegrableOn.congr_fun h2 (fun u _ => by ring) (C.e η).open_target.measurableSet
  have i4 : IntegrableOn (fun u => g u * lam u) (C.e η).target :=
    integrableOn_mul_test_target_noDrift h.loc lam rfl
  have hs : IntegrableOn (fun u => ∑ i : Fin q, g u *
      (2 * fieldTranspose (zField C i η) (β i) u)) (C.e η).target :=
    integrable_finsetSum _ (fun i _ => i3 i)
  have e : ∀ u, g u * C.poleTransposeNoDrift η α (fun i => β i) lam u =
      g u * sumSquaresTranspose C.Y α u + g u * C.errorTransposeNoDrift η α u +
        ∑ i : Fin q, g u * (2 * fieldTranspose (zField C i η) (β i) u) + g u * lam u := by
    intro u
    simp only [poleTransposeNoDrift, mul_add, Finset.mul_sum]
  have s12 : IntegrableOn (fun u => g u * sumSquaresTranspose C.Y α u +
      g u * C.errorTransposeNoDrift η α u) (C.e η).target := i1.add i2
  have s123 : IntegrableOn (fun u => g u * sumSquaresTranspose C.Y α u +
      g u * C.errorTransposeNoDrift η α u + ∑ i : Fin q, g u *
        (2 * fieldTranspose (zField C i η) (β i) u)) (C.e η).target := s12.add hs
  simp_rw [e]
  rw [integral_add s123 i4, integral_add s12 hs, integral_add i1 i2,
    integral_finsetSum _ (fun i _ => i3 i), ← h.integral_errorOp_mul hη α]
  have hsum : (∑ i : Fin q, ∫ u in (C.e η).target,
      g u * (2 * fieldTranspose (zField C i η) (β i) u)) =
      ∑ i : Fin q, ∫ u in (C.e η).target,
        2 * (fieldDerivative (zField C i η) g u * β i u) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have hz : (∫ u in (C.e η).target, fieldDerivative (zField C i η) g u * β i u) =
        ∫ u in (C.e η).target, g u * fieldTranspose (zField C i η) (β i) u :=
      (h.zg i (β i)).2
    calc (∫ u in (C.e η).target, g u * (2 * fieldTranspose (zField C i η) (β i) u))
        = ∫ u in (C.e η).target, 2 * (g u * fieldTranspose (zField C i η) (β i) u) :=
          integral_congr_ae (Filter.Eventually.of_forall (fun u => by ring))
      _ = 2 * ∫ u in (C.e η).target, g u * fieldTranspose (zField C i η) (β i) u :=
          integral_const_mul _ _
      _ = 2 * ∫ u in (C.e η).target, fieldDerivative (zField C i η) g u * β i u := by
          rw [hz]
      _ = ∫ u in (C.e η).target, 2 * (fieldDerivative (zField C i η) g u * β i u) :=
          (integral_const_mul _ _).symm
  rw [hsum]

/-- The pairing for a smooth function `g`: the model part is
`∫ (𝓛 g) α`. -/
theorem integral_smooth_mul_poleTransposeNoDrift {η : Fin (n + m) → ℝ} (hη : η ∈ C.U)
    {g : (Fin (n + m) → ℝ) → ℝ} (hg : ContDiffOn ℝ (⊤ : ℕ∞) g (C.e η).target)
    (α : TestFunction (C.modelOpens η) ℝ (⊤ : ℕ∞))
    (β : Fin q → TestFunction (C.modelOpens η) ℝ (⊤ : ℕ∞))
    (lam : TestFunction (C.modelOpens η) ℝ (⊤ : ℕ∞)) :
    (∫ u in (C.e η).target, g u * C.poleTransposeNoDrift η α (fun i => β i) lam u) =
      (∫ u in (C.e η).target, sumSquares C.Y g u * α u) +
      (∫ u in (C.e η).target, C.errorOpNoDrift η g u * α u) +
      ∑ i : Fin q, (∫ u in (C.e η).target,
        2 * (fieldDerivative (zField C i η) g u * β i u)) +
      ∫ u in (C.e η).target, g u * lam u := by
  rw [integral_mul_poleTransposeNoDrift hη (errorIbpNoDrift_of_smooth hη hg) α β lam]
  congr 3
  exact (integral_sumSquares_mul_test (C.modelOpens η) C.Y
    (fun i => contDiffOn_Y_model_noDrift i) g hg α).symm

/-- The pairing of the H1 fundamental kernel of the no-drift model with
`T(α, β, λ)`: the model part is the pole contribution `α(0)` (`𝓛 Γ = δ₀`). -/
theorem integral_kernel_mul_poleTransposeNoDrift (hq : 0 < q) (ν₀ : G2.HomogeneousNorm C.G)
    (K : H1.FundamentalKernel C.G (C.noDriftModel hq ν₀)) {η : Fin (n + m) → ℝ} (hη : η ∈ C.U)
    (α : TestFunction (C.modelOpens η) ℝ (⊤ : ℕ∞))
    (β : Fin q → TestFunction (C.modelOpens η) ℝ (⊤ : ℕ∞))
    (lam : TestFunction (C.modelOpens η) ℝ (⊤ : ℕ∞)) :
    (∫ u in (C.e η).target, K u * C.poleTransposeNoDrift η α (fun i => β i) lam u) =
      α 0 + (∫ u in (C.e η).target, C.errorOpNoDrift η K u * α u) +
      ∑ i : Fin q, (∫ u in (C.e η).target,
        2 * (fieldDerivative (zField C i η) K u * β i u)) +
      ∫ u in (C.e η).target, K u * lam u := by
  rw [integral_mul_poleTransposeNoDrift hη (errorIbp_kernel_noDrift K hη) α β lam]
  congr 3
  have h := integral_kernel_mul_transpose_noDrift K α α.contDiff α.hasCompactSupport
  have hz : ∀ u ∉ (C.e η).target, K u * sumSquaresTranspose C.Y α u = 0 := by
    intro u hu
    have hp := image_eq_zero_of_notMem_tsupport (f := sumSquaresTranspose C.Y α)
      (fun ht => hu (α.tsupport_subset (tsupport_sumSquaresTranspose_subset_noDrift C.Y α ht)))
    rw [hp, mul_zero]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz] at h
  exact h

end LiftedChart

end RothschildStein.P1
