-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.LeftParametrixAlgebra
public import RothschildStein.P1.RightParametrixPairing
public import RothschildStein.P1.RightParametrixPole
public import RothschildStein.H1.ReflectedKernel
public import RothschildStein.H1.ReversedOperator

/-!
# The model-variable pairing of the left pole computation

Fix `η ∈ C.U`, tests `α, βᵢ, λ` on the target of the endpoint chart `e η` and set

`T*(α, β, λ) = 𝓛 α + (E*)ᵀ α + ∑_{i ≥ 1} 2 Zᵢᵀ βᵢ + λ`  (`LiftedChart.leftPoleTranspose`),

`𝓛 = ∑ Yᵢ² + Y₀` the model operator (the transpose of the model adjoint `𝓛* = ∑ Yᵢ² − Y₀`),
`E* = ∑ (Yᵢ Rᵢ + Rᵢ Yᵢ + Rᵢ²) − R₀` the left error (with the negative drift sign).
For `g` with the integration-by-parts pairs of `ErrorIbp` one has
`∫ g T* = ∫ g 𝓛α + ∫ (E* g) α + ∑ᵢ ∫ 2 (Zᵢ g) βᵢ + ∫ g λ`
(`integral_mul_leftPoleTranspose`). For smooth `g` the model part is `∫ (𝓛* g) α`; for the H1
fundamental kernel `Γ*` of the reversed-drift model (`𝓛*Γ* = δ₀`) it is `α(0)`, which is the pole
contribution of the left parametrix (`integral_kernel_mul_leftPoleTranspose`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology
open RothschildStein.P2
namespace RothschildStein.P1
namespace LiftedChart

variable {n q s m : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  (C : LiftedChart (fun i : Fin (q + 1) => if i = 0 then (2 : ℕ+) else 1) s Ω hΩ X x₀ m)

/-- The transposed model operator combination of the left pole computation,
`T*(α, β, λ) = 𝓛 α + (E*)ᵀ α + ∑ᵢ 2 Zᵢᵀ βᵢ + λ`. -/
def leftPoleTranspose (η : Fin (n + m) → ℝ) (α : (Fin (n + m) → ℝ) → ℝ)
    (β : Fin q → (Fin (n + m) → ℝ) → ℝ) (lam : (Fin (n + m) → ℝ) → ℝ)
    (u : Fin (n + m) → ℝ) : ℝ :=
  sumSquaresWithDrift C.Y α u + C.leftErrorTranspose η α u +
    ∑ i : Fin q, 2 * fieldTranspose (zField C i.succ η) (β i) u + lam u

variable {C}

/-- Integrability of `(E* g) α` from the pairs of `ErrorIbp`. -/
theorem ErrorIbp.integrableOn_leftErrorOp_mul {η : Fin (n + m) → ℝ} {g : (Fin (n + m) → ℝ) → ℝ}
    (h : ErrorIbp C η g) (α : TestFunction (C.modelOpens η) ℝ (⊤ : ℕ∞)) :
    IntegrableOn (fun u => C.leftErrorOp η g u * α u) (C.e η).target := by
  have e1 : ∀ u, C.leftErrorOp η g u * α u =
      C.errorOp η g u * α u - 2 * (fieldDerivative (C.R [0] η) g u * α u) := fun u => by
    simp only [leftErrorOp]
    ring
  simp_rw [e1]
  exact (h.integrableOn_errorOp_mul α).sub ((h.r0 α).1.const_mul 2)

/-- `∫ (E* g) φ = ∫ g ((E*)ᵀ φ)` for tests `φ` on the target of `e η`, given the
pairs of `ErrorIbp`. -/
theorem ErrorIbp.integral_leftErrorOp_mul {η : Fin (n + m) → ℝ} (hη : η ∈ C.U)
    {g : (Fin (n + m) → ℝ) → ℝ} (h : ErrorIbp C η g)
    (φ : TestFunction (C.modelOpens η) ℝ (⊤ : ℕ∞)) :
    (∫ u in (C.e η).target, C.leftErrorOp η g u * φ u) =
      ∫ u in (C.e η).target, g u * C.leftErrorTranspose η φ u := by
  have i1 := h.integrableOn_errorOp_mul φ
  have i2 := (h.r0 φ).1
  have j1 : IntegrableOn (fun u => g u * C.errorTranspose η φ u) (C.e η).target :=
    integrableOn_mul_test_target h.loc (C.errorTransposeTest hη φ) (errorTransposeTest_coe C hη φ)
  have j2 : IntegrableOn (fun u => g u * fieldTranspose (C.R [0] η) φ u) (C.e η).target :=
    integrableOn_mul_test_target h.loc
      (fieldTransposeTest (C.modelOpens η) (C.R [0] η) (contDiffOn_R_model hη _) φ)
      (S.fieldTransposeTest_coe _ _ _ φ)
  have e1 : ∀ u, C.leftErrorOp η g u * φ u =
      C.errorOp η g u * φ u - 2 * (fieldDerivative (C.R [0] η) g u * φ u) := fun u => by
    simp only [leftErrorOp]
    ring
  have e2 : ∀ u, g u * C.leftErrorTranspose η φ u =
      g u * C.errorTranspose η φ u - 2 * (g u * fieldTranspose (C.R [0] η) φ u) := fun u => by
    simp only [leftErrorTranspose]
    ring
  have hr0 : (∫ u in (C.e η).target, fieldDerivative (C.R [0] η) g u * φ u) =
      ∫ u in (C.e η).target, g u * fieldTranspose (C.R [0] η) φ u := (h.r0 φ).2
  simp_rw [e1, e2]
  rw [integral_sub i1 (i2.const_mul 2), integral_sub j1 (j2.const_mul 2), integral_const_mul,
    integral_const_mul, h.integral_errorOp_mul hη φ, hr0]

/-- The pairing of `g` with `T*(α, β, λ)`: for `g` with the integration by parts
pairs of `ErrorIbp`,
`∫ g T* = ∫ g 𝓛α + ∫ (E* g) α + ∑ᵢ ∫ 2 (Zᵢ g) βᵢ + ∫ g λ`. -/
theorem integral_mul_leftPoleTranspose {η : Fin (n + m) → ℝ} (hη : η ∈ C.U)
    {g : (Fin (n + m) → ℝ) → ℝ} (h : ErrorIbp C η g)
    (α : TestFunction (C.modelOpens η) ℝ (⊤ : ℕ∞))
    (β : Fin q → TestFunction (C.modelOpens η) ℝ (⊤ : ℕ∞))
    (lam : TestFunction (C.modelOpens η) ℝ (⊤ : ℕ∞)) :
    (∫ u in (C.e η).target, g u * C.leftPoleTranspose η α (fun i => β i) lam u) =
      (∫ u in (C.e η).target, g u * sumSquaresWithDrift C.Y α u) +
      (∫ u in (C.e η).target, C.leftErrorOp η g u * α u) +
      ∑ i : Fin q, (∫ u in (C.e η).target,
        2 * (fieldDerivative (zField C i.succ η) g u * β i u)) +
      ∫ u in (C.e η).target, g u * lam u := by
  have i1 : IntegrableOn (fun u => g u * sumSquaresWithDrift C.Y α u) (C.e η).target :=
    integrableOn_mul_test_target h.loc
      (sumSquaresWithDriftTest (C.modelOpens η) C.Y (fun i => contDiffOn_Y_model i) α)
      (sumSquaresWithDriftTest_coe _ _ _ α)
  have i2 : IntegrableOn (fun u => g u * C.leftErrorTranspose η α u) (C.e η).target := by
    have j1 : IntegrableOn (fun u => g u * C.errorTranspose η α u) (C.e η).target :=
      integrableOn_mul_test_target h.loc (C.errorTransposeTest hη α)
        (errorTransposeTest_coe C hη α)
    have j2 : IntegrableOn (fun u => g u * fieldTranspose (C.R [0] η) α u) (C.e η).target :=
      integrableOn_mul_test_target h.loc
        (fieldTransposeTest (C.modelOpens η) (C.R [0] η) (contDiffOn_R_model hη _) α)
        (S.fieldTransposeTest_coe _ _ _ α)
    have e2 : ∀ u, g u * C.leftErrorTranspose η α u =
        g u * C.errorTranspose η α u - 2 * (g u * fieldTranspose (C.R [0] η) α u) := fun u => by
      simp only [leftErrorTranspose]
      ring
    simp_rw [e2]
    exact j1.sub (j2.const_mul 2)
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
  have e : ∀ u, g u * C.leftPoleTranspose η α (fun i => β i) lam u =
      g u * sumSquaresWithDrift C.Y α u + g u * C.leftErrorTranspose η α u +
        ∑ i : Fin q, g u * (2 * fieldTranspose (zField C i.succ η) (β i) u) + g u * lam u := by
    intro u
    simp only [leftPoleTranspose, mul_add, Finset.mul_sum]
  have s12 : IntegrableOn (fun u => g u * sumSquaresWithDrift C.Y α u +
      g u * C.leftErrorTranspose η α u) (C.e η).target := i1.add i2
  have s123 : IntegrableOn (fun u => g u * sumSquaresWithDrift C.Y α u +
      g u * C.leftErrorTranspose η α u + ∑ i : Fin q, g u *
        (2 * fieldTranspose (zField C i.succ η) (β i) u)) (C.e η).target := s12.add hs
  simp_rw [e]
  rw [integral_add s123 i4, integral_add s12 hs, integral_add i1 i2,
    integral_finsetSum _ (fun i _ => i3 i), ← h.integral_leftErrorOp_mul hη α]
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

/-- The fields of the reversed-drift model: `(−Y₀, Y₁, …, Y_q)`. The reversed
operator `∑ Yᵢ² − Y₀` of the model is `LiftedChart.modelAdjoint`. -/
theorem sumSquaresWithDrift_reverseDrift_fields (hq : 0 < q) (ν₀ : G2.HomogeneousNorm C.G)
    (g : (Fin (n + m) → ℝ) → ℝ) :
    sumSquaresWithDrift ((C.driftModel hq ν₀).reverseDrift C.G).fields g = C.modelAdjoint g := by
  funext u
  have h0 : ((C.driftModel hq ν₀).reverseDrift C.G).fields 0 = fun x => -(C.Y 0 x) := by
    funext x
    simp [H1.StandingHypotheses.reverseDrift, H1.driftSign]
  have hs : ∀ i : Fin q, ((C.driftModel hq ν₀).reverseDrift C.G).fields i.succ = C.Y i.succ :=
    fun i => (C.driftModel hq ν₀).reverseDrift_horizontal C.G i
  have h1 : fieldDerivative ((fun x => -(C.Y 0 x) : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ))) g u =
      -fieldDerivative (C.Y 0) g u := by
    simp [fieldDerivative]
  unfold sumSquaresWithDrift modelAdjoint
  rw [h0, h1]
  simp only [hs]
  ring

/-- The model part of the pairing for a smooth `g` and a test `α`:
`∫ (𝓛* g) α = ∫ g 𝓛α` (`𝓛*` is the transpose of `𝓛`; the reversed-drift fields have
transpose `𝓛`). -/
theorem integral_modelAdjoint_mul (hq : 0 < q) (ν₀ : G2.HomogeneousNorm C.G) {η : Fin (n + m) → ℝ}
    {g : (Fin (n + m) → ℝ) → ℝ} (hg : ContDiffOn ℝ (⊤ : ℕ∞) g (C.e η).target)
    (α : TestFunction (C.modelOpens η) ℝ (⊤ : ℕ∞)) :
    (∫ u in (C.e η).target, C.modelAdjoint g u * α u) =
      ∫ u in (C.e η).target, g u * sumSquaresWithDrift C.Y α u := by
  have h := integral_sumSquaresWithDrift_mul_test (C.modelOpens η)
    ((C.driftModel hq ν₀).reverseDrift C.G).fields
    (fun i => (((C.driftModel hq ν₀).reverseDrift C.G).fields_smooth C.G i).contDiffOn) g hg α
  have e1 : ∀ u, sumSquaresWithDrift ((C.driftModel hq ν₀).reverseDrift C.G).fields g u =
      C.modelAdjoint g u := fun u => by
    rw [sumSquaresWithDrift_reverseDrift_fields hq ν₀ g]
  have e2 : ∀ u, sumSquaresWithDriftTranspose ((C.driftModel hq ν₀).reverseDrift C.G).fields α u =
      sumSquaresWithDrift C.Y α u := fun u => by
    rw [(C.driftModel hq ν₀).reverseDrift_transpose_operator C.G α.contDiff u]
    rfl
  simp only [e1, e2] at h
  exact h

/-- The pairing for a smooth function `g`: the model part is `∫ (𝓛* g) α`. -/
theorem integral_smooth_mul_leftPoleTranspose (hq : 0 < q) (ν₀ : G2.HomogeneousNorm C.G)
    {η : Fin (n + m) → ℝ} (hη : η ∈ C.U) {g : (Fin (n + m) → ℝ) → ℝ}
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g (C.e η).target)
    (α : TestFunction (C.modelOpens η) ℝ (⊤ : ℕ∞))
    (β : Fin q → TestFunction (C.modelOpens η) ℝ (⊤ : ℕ∞))
    (lam : TestFunction (C.modelOpens η) ℝ (⊤ : ℕ∞)) :
    (∫ u in (C.e η).target, g u * C.leftPoleTranspose η α (fun i => β i) lam u) =
      (∫ u in (C.e η).target, C.modelAdjoint g u * α u) +
      (∫ u in (C.e η).target, C.leftErrorOp η g u * α u) +
      ∑ i : Fin q, (∫ u in (C.e η).target,
        2 * (fieldDerivative (zField C i.succ η) g u * β i u)) +
      ∫ u in (C.e η).target, g u * lam u := by
  rw [integral_mul_leftPoleTranspose hη (errorIbp_of_smooth hη hg) α β lam,
    integral_modelAdjoint_mul hq ν₀ hg α]

/-- The model fundamental identity for the reflected kernel: if `Γ*` is a
fundamental kernel of the reversed-drift model (`𝓛*Γ* = δ₀`), then
`∫ Γ* 𝓛α = α(0)` for tests `α` on the target. -/
theorem integral_kernel_mul_sumSquaresWithDrift (hq : 0 < q) (ν₀ : G2.HomogeneousNorm C.G)
    (K : H1.FundamentalKernel C.G ((C.driftModel hq ν₀).reverseDrift C.G)) {η : Fin (n + m) → ℝ}
    (α : TestFunction (C.modelOpens η) ℝ (⊤ : ℕ∞)) :
    (∫ u in (C.e η).target, K u * sumSquaresWithDrift C.Y α u) = α 0 := by
  have h := K.fundamental α α.contDiff α.hasCompactSupport
  have e2 : ∀ u, sumSquaresWithDriftTranspose ((C.driftModel hq ν₀).reverseDrift C.G).fields α u =
      sumSquaresWithDrift C.Y α u := fun u => by
    rw [(C.driftModel hq ν₀).reverseDrift_transpose_operator C.G α.contDiff u]
    rfl
  simp only [e2] at h
  have hts := (sumSquaresWithDriftTest (C.modelOpens η) C.Y (fun i => contDiffOn_Y_model i)
    α).tsupport_subset
  rw [sumSquaresWithDriftTest_coe] at hts
  have hz : ∀ u ∉ (C.e η).target, K u * sumSquaresWithDrift C.Y α u = 0 := by
    intro u hu
    rw [image_eq_zero_of_notMem_tsupport (f := sumSquaresWithDrift C.Y α) (fun ht => hu (hts ht)),
      mul_zero]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hz] at h
  exact h

/-- The pairing of the reflected fundamental kernel `Γ*` with `T*(α, β, λ)`: the
model part is the pole contribution `α(0)` (`𝓛*Γ* = δ₀`). -/
theorem integral_kernel_mul_leftPoleTranspose (hq : 0 < q) (ν₀ : G2.HomogeneousNorm C.G)
    (K : H1.FundamentalKernel C.G ((C.driftModel hq ν₀).reverseDrift C.G)) {η : Fin (n + m) → ℝ}
    (hη : η ∈ C.U) (α : TestFunction (C.modelOpens η) ℝ (⊤ : ℕ∞))
    (β : Fin q → TestFunction (C.modelOpens η) ℝ (⊤ : ℕ∞))
    (lam : TestFunction (C.modelOpens η) ℝ (⊤ : ℕ∞)) :
    (∫ u in (C.e η).target, K u * C.leftPoleTranspose η α (fun i => β i) lam u) =
      α 0 + (∫ u in (C.e η).target, C.leftErrorOp η K u * α u) +
      ∑ i : Fin q, (∫ u in (C.e η).target,
        2 * (fieldDerivative (zField C i.succ η) K u * β i u)) +
      ∫ u in (C.e η).target, K u * lam u := by
  rw [integral_mul_leftPoleTranspose hη (errorIbp_kernel K hη) α β lam,
    integral_kernel_mul_sumSquaresWithDrift hq ν₀ K α]

end LiftedChart

end RothschildStein.P1
