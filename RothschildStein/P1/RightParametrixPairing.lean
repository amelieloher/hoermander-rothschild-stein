-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.RightParametrixError
public import RothschildStein.P1.AdjointExpansionChart
public import RothschildStein.P1.ModelHypotheses
public import RothschildStein.H1.OperatorIntegrationByParts

/-!
# The model-variable pairing of the right pole computation

Fix `η ∈ C.U`, tests `α, βᵢ, λ` on the target of the endpoint chart `e η` and set

`T(α, β, λ) = 𝓛ᵀ α + Eᵀ α + ∑_{i ≥ 1} 2 Zᵢᵀ βᵢ + λ`  (`LiftedChart.poleTranspose`).

For a function `g` with the integration-by-parts pairs of `ErrorIbp` one has
`∫ g T = ∫ g 𝓛ᵀα + ∫ (E g) α + ∑ᵢ ∫ 2 (Zᵢ g) βᵢ + ∫ g λ`
(`integral_mul_poleTranspose`). For smooth `g` the model part is `∫ (𝓛 g) α`; for the H1
fundamental kernel it is `α(0)` (`StandingHypotheses`, `FundamentalKernel.fundamental`: `𝓛Γ = δ₀`),
which is the pole contribution of the right pole computation.
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

/-- The function underlying the bundled transpose test is the
transpose `sumSquaresWithDriftTranspose`. -/
theorem sumSquaresWithDriftTransposeTest_coe {q : ℕ} (Ω : Opens (Fin n → ℝ))
    (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (φ : TestFunction Ω ℝ (⊤ : ℕ∞)) :
    (sumSquaresWithDriftTransposeTest Ω X hX φ : (Fin n → ℝ) → ℝ) =
      sumSquaresWithDriftTranspose X φ := by
  funext x
  let ev : TestFunction Ω ℝ (⊤ : ℕ∞) →+ ℝ :=
    { toFun := fun ψ => ψ x, map_zero' := rfl, map_add' := fun _ _ => rfl }
  have h : (sumSquaresWithDriftTransposeTest Ω X hX φ : (Fin n → ℝ) → ℝ) x =
      ev (fieldTransposeTest Ω (X 0) (hX 0) φ +
        ∑ i : Fin q, fieldTransposeTest Ω (X i.succ) (hX i.succ)
          (fieldTransposeTest Ω (X i.succ) (hX i.succ) φ)) := rfl
  rw [h, map_add, map_sum]
  unfold sumSquaresWithDriftTranspose
  simp only [ev, AddMonoidHom.coe_mk, ZeroHom.coe_mk, S.fieldTransposeTest_apply,
    S.fieldTransposeTest_coe]

/-- Smoothness of `L = ∑ Xᵢ² + X₀` on functions smooth on an open set. -/
theorem contDiffOn_sumSquaresWithDrift {q : ℕ} (Ω : Opens (Fin n → ℝ))
    (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ))) {f : (Fin n → ℝ) → ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (Ω : Set (Fin n → ℝ))) :
    ContDiffOn ℝ (⊤ : ℕ∞) (sumSquaresWithDrift X f) (Ω : Set (Fin n → ℝ)) := by
  have h0 := S.contDiffOn_fieldDerivative Ω (X 0) f (hX 0) hf
  have h1 : ∀ i : Fin q, ContDiffOn ℝ (⊤ : ℕ∞)
      (fieldDerivative (X i.succ) (fieldDerivative (X i.succ) f)) (Ω : Set (Fin n → ℝ)) := fun i =>
    S.contDiffOn_fieldDerivative Ω (X i.succ) _ (hX i.succ)
      (S.contDiffOn_fieldDerivative Ω (X i.succ) f (hX i.succ) hf)
  exact h0.add (ContDiffOn.sum fun i _ => h1 i)

end TestCoe

namespace LiftedChart

variable {n q s m : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  (C : LiftedChart (fun i : Fin (q + 1) => if i = 0 then (2 : ℕ+) else 1) s Ω hΩ X x₀ m)

/-- The bundled transposed error operator on tests on the target
of `e η`. -/
def errorTransposeTest {η : Fin (n + m) → ℝ} (hη : η ∈ C.U)
    (φ : TestFunction (C.modelOpens η) ℝ (⊤ : ℕ∞)) : TestFunction (C.modelOpens η) ℝ (⊤ : ℕ∞) :=
  (∑ i : Fin q, (fieldTransposeTest (C.modelOpens η) (C.R [i.succ] η)
      (contDiffOn_R_model hη _)
      (fieldTransposeTest (C.modelOpens η) (C.Y i.succ) (contDiffOn_Y_model i.succ) φ) +
    fieldTransposeTest (C.modelOpens η) (zField C i.succ η) (contDiffOn_zField_model hη i.succ)
      (fieldTransposeTest (C.modelOpens η) (C.R [i.succ] η) (contDiffOn_R_model hη _) φ))) +
  fieldTransposeTest (C.modelOpens η) (C.R [0] η) (contDiffOn_R_model hη _) φ

theorem errorTransposeTest_coe {η : Fin (n + m) → ℝ} (hη : η ∈ C.U)
    (φ : TestFunction (C.modelOpens η) ℝ (⊤ : ℕ∞)) :
    (C.errorTransposeTest hη φ : (Fin (n + m) → ℝ) → ℝ) = C.errorTranspose η φ := by
  funext x
  let ev : TestFunction (C.modelOpens η) ℝ (⊤ : ℕ∞) →+ ℝ :=
    { toFun := fun ψ => ψ x, map_zero' := rfl, map_add' := fun _ _ => rfl }
  have t1 : ∀ i : Fin q, (fieldTransposeTest (C.modelOpens η) (C.R [i.succ] η)
      (contDiffOn_R_model hη _)
      (fieldTransposeTest (C.modelOpens η) (C.Y i.succ) (contDiffOn_Y_model i.succ) φ)) x =
      fieldTranspose (C.R [i.succ] η) (fieldTranspose (C.Y i.succ) φ) x := fun i => by
    rw [S.fieldTransposeTest_apply, S.fieldTransposeTest_coe]
  have t2 : ∀ i : Fin q, (fieldTransposeTest (C.modelOpens η) (zField C i.succ η)
      (contDiffOn_zField_model hη i.succ)
      (fieldTransposeTest (C.modelOpens η) (C.R [i.succ] η) (contDiffOn_R_model hη _) φ)) x =
      fieldTranspose (zField C i.succ η) (fieldTranspose (C.R [i.succ] η) φ) x := fun i => by
    rw [S.fieldTransposeTest_apply, S.fieldTransposeTest_coe]
  have t3 : (fieldTransposeTest (C.modelOpens η) (C.R [0] η) (contDiffOn_R_model hη _) φ) x =
      fieldTranspose (C.R [0] η) φ x := S.fieldTransposeTest_apply _ _ _ _ _
  have h : (C.errorTransposeTest hη φ : (Fin (n + m) → ℝ) → ℝ) x = ev (C.errorTransposeTest hη φ) :=
    rfl
  rw [h]
  unfold errorTransposeTest
  rw [map_add, map_sum]
  simp only [map_add]
  unfold errorTranspose
  exact congrArg₂ (· + ·) (Finset.sum_congr rfl (fun i _ => congrArg₂ (· + ·) (t1 i) (t2 i))) t3

/-- The transposed model operator combination of the right pole computation,
`T(α, β, λ) = 𝓛ᵀ α + Eᵀ α + ∑ᵢ 2 Zᵢᵀ βᵢ + λ`. -/
def poleTranspose (η : Fin (n + m) → ℝ) (α : (Fin (n + m) → ℝ) → ℝ)
    (β : Fin q → (Fin (n + m) → ℝ) → ℝ) (lam : (Fin (n + m) → ℝ) → ℝ)
    (u : Fin (n + m) → ℝ) : ℝ :=
  sumSquaresWithDriftTranspose C.Y α u + C.errorTranspose η α u +
    ∑ i : Fin q, 2 * fieldTranspose (zField C i.succ η) (β i) u + lam u

variable {C}

/-- The pairing of `g` with `T(α, β, λ)`: for `g` with the integration by parts
pairs of `ErrorIbp`,
`∫ g T = ∫ g 𝓛ᵀα + ∫ (E g) α + ∑ᵢ ∫ 2 (Zᵢ g) βᵢ + ∫ g λ`. -/
theorem integral_mul_poleTranspose {η : Fin (n + m) → ℝ} (hη : η ∈ C.U)
    {g : (Fin (n + m) → ℝ) → ℝ} (h : ErrorIbp C η g)
    (α : TestFunction (C.modelOpens η) ℝ (⊤ : ℕ∞))
    (β : Fin q → TestFunction (C.modelOpens η) ℝ (⊤ : ℕ∞))
    (lam : TestFunction (C.modelOpens η) ℝ (⊤ : ℕ∞)) :
    (∫ u in (C.e η).target, g u * C.poleTranspose η α (fun i => β i) lam u) =
      (∫ u in (C.e η).target, g u * sumSquaresWithDriftTranspose C.Y α u) +
      (∫ u in (C.e η).target, C.errorOp η g u * α u) +
      ∑ i : Fin q, (∫ u in (C.e η).target,
        2 * (fieldDerivative (zField C i.succ η) g u * β i u)) +
      ∫ u in (C.e η).target, g u * lam u := by
  have i1 : IntegrableOn (fun u => g u * sumSquaresWithDriftTranspose C.Y α u) (C.e η).target :=
    integrableOn_mul_test_target h.loc
      (sumSquaresWithDriftTransposeTest (C.modelOpens η) C.Y (fun i => contDiffOn_Y_model i) α)
      (sumSquaresWithDriftTransposeTest_coe _ _ _ α)
  have i2 : IntegrableOn (fun u => g u * C.errorTranspose η α u) (C.e η).target :=
    integrableOn_mul_test_target h.loc (C.errorTransposeTest hη α) (errorTransposeTest_coe C hη α)
  have i3 : ∀ i : Fin q, IntegrableOn (fun u => g u *
      (2 * fieldTranspose (zField C i.succ η) (β i) u)) (C.e η).target := fun i => by
    have h1 : IntegrableOn (fun u => g u * fieldTranspose (zField C i.succ η) (β i) u)
        (C.e η).target := integrableOn_mul_test_target h.loc
      (fieldTransposeTest (C.modelOpens η) (zField C i.succ η) (contDiffOn_zField_model hη i.succ)
        (β i)) (S.fieldTransposeTest_coe _ _ _ (β i))
    have h2 : IntegrableOn (fun u => 2 * (g u * fieldTranspose (zField C i.succ η) (β i) u))
        (C.e η).target := h1.const_mul 2
    exact IntegrableOn.congr_fun h2 (fun u _ => by ring) (C.e η).open_target.measurableSet
  have i4 : IntegrableOn (fun u => g u * lam u) (C.e η).target :=
    integrableOn_mul_test_target h.loc lam rfl
  have hs : IntegrableOn (fun u => ∑ i : Fin q, g u *
      (2 * fieldTranspose (zField C i.succ η) (β i) u)) (C.e η).target :=
    integrable_finsetSum _ (fun i _ => i3 i)
  have e : ∀ u, g u * C.poleTranspose η α (fun i => β i) lam u =
      g u * sumSquaresWithDriftTranspose C.Y α u + g u * C.errorTranspose η α u +
        ∑ i : Fin q, g u * (2 * fieldTranspose (zField C i.succ η) (β i) u) + g u * lam u := by
    intro u
    simp only [poleTranspose, mul_add, Finset.mul_sum]
  have s12 : IntegrableOn (fun u => g u * sumSquaresWithDriftTranspose C.Y α u +
      g u * C.errorTranspose η α u) (C.e η).target := i1.add i2
  have s123 : IntegrableOn (fun u => g u * sumSquaresWithDriftTranspose C.Y α u +
      g u * C.errorTranspose η α u + ∑ i : Fin q, g u *
        (2 * fieldTranspose (zField C i.succ η) (β i) u)) (C.e η).target := s12.add hs
  simp_rw [e]
  rw [integral_add s123 i4, integral_add s12 hs, integral_add i1 i2,
    integral_finsetSum _ (fun i _ => i3 i), ← h.integral_errorOp_mul hη α]
  have hsum : (∑ i : Fin q, ∫ u in (C.e η).target,
      g u * (2 * fieldTranspose (zField C i.succ η) (β i) u)) =
      ∑ i : Fin q, ∫ u in (C.e η).target,
        2 * (fieldDerivative (zField C i.succ η) g u * β i u) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have hz : (∫ u in (C.e η).target, fieldDerivative (zField C i.succ η) g u * β i u) =
        ∫ u in (C.e η).target, g u * fieldTranspose (zField C i.succ η) (β i) u :=
      (h.zg i (β i)).2
    calc (∫ u in (C.e η).target, g u * (2 * fieldTranspose (zField C i.succ η) (β i) u))
        = ∫ u in (C.e η).target, 2 * (g u * fieldTranspose (zField C i.succ η) (β i) u) :=
          integral_congr_ae (Filter.Eventually.of_forall (fun u => by ring))
      _ = 2 * ∫ u in (C.e η).target, g u * fieldTranspose (zField C i.succ η) (β i) u :=
          integral_const_mul _ _
      _ = 2 * ∫ u in (C.e η).target, fieldDerivative (zField C i.succ η) g u * β i u := by
          rw [hz]
      _ = ∫ u in (C.e η).target, 2 * (fieldDerivative (zField C i.succ η) g u * β i u) :=
          (integral_const_mul _ _).symm
  rw [hsum]

/-- The pairing for a smooth function `g`: the model part is
`∫ (𝓛 g) α`. -/
theorem integral_smooth_mul_poleTranspose {η : Fin (n + m) → ℝ} (hη : η ∈ C.U)
    {g : (Fin (n + m) → ℝ) → ℝ} (hg : ContDiffOn ℝ (⊤ : ℕ∞) g (C.e η).target)
    (α : TestFunction (C.modelOpens η) ℝ (⊤ : ℕ∞))
    (β : Fin q → TestFunction (C.modelOpens η) ℝ (⊤ : ℕ∞))
    (lam : TestFunction (C.modelOpens η) ℝ (⊤ : ℕ∞)) :
    (∫ u in (C.e η).target, g u * C.poleTranspose η α (fun i => β i) lam u) =
      (∫ u in (C.e η).target, sumSquaresWithDrift C.Y g u * α u) +
      (∫ u in (C.e η).target, C.errorOp η g u * α u) +
      ∑ i : Fin q, (∫ u in (C.e η).target,
        2 * (fieldDerivative (zField C i.succ η) g u * β i u)) +
      ∫ u in (C.e η).target, g u * lam u := by
  rw [integral_mul_poleTranspose hη (errorIbp_of_smooth hη hg) α β lam]
  congr 3
  exact (integral_sumSquaresWithDrift_mul_test (C.modelOpens η) C.Y
    (fun i => contDiffOn_Y_model i) g hg α).symm

/-- The pairing of the H1 fundamental kernel with `T(α, β, λ)`: the model part
is the pole contribution `α(0)` (`𝓛 Γ = δ₀`). -/
theorem integral_kernel_mul_poleTranspose (hq : 0 < q) (ν₀ : G2.HomogeneousNorm C.G)
    (K : H1.FundamentalKernel C.G (C.driftModel hq ν₀)) {η : Fin (n + m) → ℝ} (hη : η ∈ C.U)
    (α : TestFunction (C.modelOpens η) ℝ (⊤ : ℕ∞))
    (β : Fin q → TestFunction (C.modelOpens η) ℝ (⊤ : ℕ∞))
    (lam : TestFunction (C.modelOpens η) ℝ (⊤ : ℕ∞)) :
    (∫ u in (C.e η).target, K u * C.poleTranspose η α (fun i => β i) lam u) =
      α 0 + (∫ u in (C.e η).target, C.errorOp η K u * α u) +
      ∑ i : Fin q, (∫ u in (C.e η).target,
        2 * (fieldDerivative (zField C i.succ η) K u * β i u)) +
      ∫ u in (C.e η).target, K u * lam u := by
  rw [integral_mul_poleTranspose hη (errorIbp_kernel K hη) α β lam]
  congr 3
  have h := K.fundamental α α.contDiff α.hasCompactSupport
  have hz : ∀ u ∉ (C.e η).target,
      K u * sumSquaresWithDriftTranspose (C.driftModel hq ν₀).fields α u = 0 := by
    intro u hu
    have hp := image_eq_zero_of_notMem_tsupport (f := sumSquaresWithDriftTranspose
      (C.driftModel hq ν₀).fields α) (fun ht => hu
        (α.tsupport_subset (H1.tsupport_sumSquaresTranspose_subset (C.driftModel hq ν₀).fields α ht)))
    rw [hp, mul_zero]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz] at h
  exact h

end LiftedChart

end RothschildStein.P1
