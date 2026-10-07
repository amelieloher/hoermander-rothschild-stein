-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.LeftParametrixPairing
public import RothschildStein.P1.RightParametrixPole

/-!
# The pole limit: the pole of the left parametrix contributes `a(η) φ(η)`

The left pole `Γ*(Θ(η, ξ))` tested in `ξ` against `L̃φ`, with an output cutoff `a` (the
pole computation for the left parametrix; BB pp. 560–563, with the sign erratum). Substituting `u = Θ(η, ξ)`
(`LiftedChart.modelTransport`) and testing against smooth compactly supported `g` of the model
variable gives `∫ g · S = ∫ g · T*(α, β, λ)` with `S` the transported `a L̃φ` and
`α = (aφ)~`, `βᵢ = ((a dᵢ + X̃ᵢ a) φ)~`, `λ = ((L̃* a) φ)~`; hence `S = T*(α, β, λ)`
(`modelTransport_eq_leftPoleTranspose`). For the fundamental kernel `Γ*` of
`𝓛* = ∑ Yᵢ² − Y₀` one has `∫ Γ* 𝓛α = α(0) = c(η) a(η) φ(η)`, and the remaining terms are the
absolutely convergent errors (the left error `E*` has the negative drift sign):
`integral_kernel_comp_theta_mul_sumSquares`. With `a ≡ 1` this is the pole limit
`∫ Γ*(Θ) L̃ψ = c(η) ψ(η) + ∫ (E*_η Γ*)(Θ) ψ` with the divergence terms of the formal adjoint `L̃*`
(`integral_kernel_comp_theta_sumSquares`).
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

/-- The first-order coefficient `a dᵢ + X̃ᵢ a` of the left error bracket
(`dᵢ = div X̃ᵢ`): it combines the output cutoff with the divergence terms of the formal adjoint `L̃*`. -/
def leftBetaCoeff (a : (Fin (n + m) → ℝ) → ℝ) (i : Fin q) (ξ : Fin (n + m) → ℝ) : ℝ :=
  a ξ * Hormander.Interface.euclideanDivergence (C.Xl i.succ) ξ +
    fieldDerivative (C.Xl i.succ) a ξ

/-- The bracket of the error kernel of the left parametrix,
`a(ξ) (E*_η K)(Θ(η, ξ)) + 2 ∑ᵢ (a dᵢ + X̃ᵢ a)(ξ) (Zᵢ K)(Θ(η, ξ)) + (L̃* a)(ξ) K(Θ(η, ξ))`
(the formal adjoint `L̃*` applied in `ξ` to `a(ξ) K(Θ(η, ξ))`). -/
def leftErrBracket (K a : (Fin (n + m) → ℝ) → ℝ) (η ξ : Fin (n + m) → ℝ) : ℝ :=
  a ξ * C.leftPoleError η K (C.Θ η ξ) +
    2 * ∑ i : Fin q, C.leftBetaCoeff a i ξ * C.zDeriv η i.succ K (C.Θ η ξ) +
    sumSquaresWithDriftTranspose C.Xl a ξ * K (C.Θ η ξ)

variable {C}

theorem contDiffOn_leftBetaCoeff {a : (Fin (n + m) → ℝ) → ℝ} (ha : ContDiffOn ℝ (⊤ : ℕ∞) a C.U)
    (i : Fin q) : ContDiffOn ℝ (⊤ : ℕ∞) (C.leftBetaCoeff a i) C.U :=
  (ha.mul (contDiffOn_euclideanDivergence C.chartOpens (C.Xl i.succ)
    (C.contDiffOn_Xl_U i.succ))).add (contDiffOn_fieldDerivative_Xl ha i.succ)

theorem contDiffOn_sumSquaresWithDriftTranspose_Xl {a : (Fin (n + m) → ℝ) → ℝ}
    (ha : ContDiffOn ℝ (⊤ : ℕ∞) a C.U) :
    ContDiffOn ℝ (⊤ : ℕ∞) (sumSquaresWithDriftTranspose C.Xl a) C.U := by
  unfold sumSquaresWithDriftTranspose
  have h0 := S.contDiffOn_fieldTranspose C.chartOpens (C.Xl 0) a (C.contDiffOn_Xl_U 0) ha
  have h1 : ∀ i : Fin q, ContDiffOn ℝ (⊤ : ℕ∞)
      (fieldTranspose (C.Xl i.succ) (fieldTranspose (C.Xl i.succ) a)) C.U := fun i =>
    S.contDiffOn_fieldTranspose C.chartOpens (C.Xl i.succ) _ (C.contDiffOn_Xl_U i.succ)
      (S.contDiffOn_fieldTranspose C.chartOpens (C.Xl i.succ) a (C.contDiffOn_Xl_U i.succ) ha)
  exact h0.add (ContDiffOn.sum fun i _ => h1 i)

variable (C) in
/-- The transported tests `((a dᵢ + X̃ᵢ a) φ)~`. -/
def betaL {η : Fin (n + m) → ℝ} (hη : η ∈ C.U) {a : (Fin (n + m) → ℝ) → ℝ}
    (ha : ContDiffOn ℝ (⊤ : ℕ∞) a C.U) (φ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞)) (i : Fin q) :
    TestFunction (C.modelOpens η) ℝ (⊤ : ℕ∞) :=
  modelTransportTest hη (testMultiplierOn C.chartOpens (C.leftBetaCoeff a i)
    (contDiffOn_leftBetaCoeff ha i) φ)

variable (C) in
/-- The transported test `((L̃* a) φ)~`. -/
def lamL {η : Fin (n + m) → ℝ} (hη : η ∈ C.U) {a : (Fin (n + m) → ℝ) → ℝ}
    (ha : ContDiffOn ℝ (⊤ : ℕ∞) a C.U) (φ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞)) :
    TestFunction (C.modelOpens η) ℝ (⊤ : ℕ∞) :=
  modelTransportTest hη (testMultiplierOn C.chartOpens (sumSquaresWithDriftTranspose C.Xl a)
    (contDiffOn_sumSquaresWithDriftTranspose_Xl ha) φ)

theorem contDiffOn_modelAdjoint {η : Fin (n + m) → ℝ} {g : (Fin (n + m) → ℝ) → ℝ}
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g (C.e η).target) :
    ContDiffOn ℝ (⊤ : ℕ∞) (C.modelAdjoint g) (C.e η).target := by
  have hYs : ∀ i : Fin (q + 1), ContDiffOn ℝ (⊤ : ℕ∞) (C.Y i)
      ((C.modelOpens η : Opens (Fin (n + m) → ℝ)) : Set (Fin (n + m) → ℝ)) :=
    fun i => (C.model_field_smooth i).contDiffOn
  have h1 : ∀ i : Fin q, ContDiffOn ℝ (⊤ : ℕ∞)
      (fieldDerivative (C.Y i.succ) (fieldDerivative (C.Y i.succ) g)) (C.e η).target := fun i =>
    S.contDiffOn_fieldDerivative (C.modelOpens η) _ _ (hYs _)
      (S.contDiffOn_fieldDerivative (C.modelOpens η) _ g (hYs _) hg)
  exact (ContDiffOn.sum fun i _ => h1 i).sub
    (S.contDiffOn_fieldDerivative (C.modelOpens η) _ g (hYs 0) hg)

theorem contDiffOn_leftErrorOp {η : Fin (n + m) → ℝ} (hη : η ∈ C.U) {g : (Fin (n + m) → ℝ) → ℝ}
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g (C.e η).target) :
    ContDiffOn ℝ (⊤ : ℕ∞) (C.leftErrorOp η g) (C.e η).target :=
  (contDiffOn_errorOp hη hg).sub (contDiffOn_const.mul
    (S.contDiffOn_fieldDerivative (C.modelOpens η) _ g (contDiffOn_R_model hη _) hg))

theorem zDeriv_eq_zField (η : Fin (n + m) → ℝ) (i : Fin (q + 1)) (g : (Fin (n + m) → ℝ) → ℝ)
    (u : Fin (n + m) → ℝ) : C.zDeriv η i g u = fieldDerivative (zField C i η) g u :=
  congrFun (zDeriv_eq_fieldDerivative η i g) u

/-- Transport of the operator to the model, for test functions: for `η ∈ C.U`,
a test `φ` on `C.U`, `a` smooth on `C.U` and a test function `g` of the model variable,
`∫_U g(Θ η ξ) (L̃φ)(ξ) a(ξ) dξ = ∫ g T*(α, β, λ)` (duality for `L̃` against the pullback test
function `a (g∘Θ η)`, the formal adjoint formula via the chain rule, and the substitution `u = Θ η ξ`). -/
theorem integral_comp_theta_mul_sumSquares_test (hq : 0 < q) (ν₀ : G2.HomogeneousNorm C.G)
    {η : Fin (n + m) → ℝ} (hη : η ∈ C.U) {a : (Fin (n + m) → ℝ) → ℝ}
    (ha : ContDiffOn ℝ (⊤ : ℕ∞) a C.U) (φ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞))
    (g : TestFunction (C.modelOpens η) ℝ (⊤ : ℕ∞)) :
    (∫ ξ in C.U, g (C.Θ η ξ) * (sumSquaresWithDrift C.Xl φ ξ * a ξ)) =
      ∫ u in (C.e η).target, g u * C.leftPoleTranspose η (alphaT C hη ha φ)
        (fun i => betaL C hη ha φ i) (lamL C hη ha φ) u := by
  have hmeas : MeasurableSet C.U := C.isOpen_U.measurableSet
  have hg : ContDiffOn ℝ (⊤ : ℕ∞) g (C.e η).target := g.contDiff.contDiffOn
  set h : TestFunction C.chartOpens ℝ (⊤ : ℕ∞) := pullbackTest hη ha g with hh
  have hdual := C.integral_sumSquaresWithDrift_mul_test_U (φ : (Fin (n + m) → ℝ) → ℝ)
    φ.contDiff.contDiffOn h
  -- the pointwise computation of `L̃* h` on `C.U`
  have hpt : ∀ ξ ∈ C.U, φ ξ * sumSquaresWithDriftTranspose C.Xl h ξ =
      C.modelAdjoint g (C.Θ η ξ) * (φ ξ * a ξ) + C.leftErrorOp η g (C.Θ η ξ) * (φ ξ * a ξ) +
        ∑ i : Fin q, 2 * (fieldDerivative (zField C i.succ η) g (C.Θ η ξ) *
          (φ ξ * C.leftBetaCoeff a i ξ)) +
        g (C.Θ η ξ) * (φ ξ * sumSquaresWithDriftTranspose C.Xl a ξ) := by
    intro ξ hξ
    have hev : (h : (Fin (n + m) → ℝ) → ℝ) =ᶠ[𝓝 ξ] fun ξ' => a ξ' * g (C.Θ η ξ') :=
      Filter.eventuallyEq_of_mem (C.isOpen_U.mem_nhds hξ)
        (fun y hy => pullbackTest_apply hη ha g hy)
    have hmem := C.theta_mem_target hη hξ
    rw [sumSquaresWithDriftTranspose_congr_of_eventuallyEq C.Xl hev,
      C.sumSquaresWithDriftTranspose_mul_comp_theta hη (C.e η).open_target hg ha hξ hmem,
      C.leftPoleError_eq_leftErrorOp hη (C.e η).open_target hg hmem hmem]
    simp only [zDeriv_eq_zField, leftBetaCoeff]
    have hs : φ ξ * (2 * ∑ i : Fin q, (a ξ * Hormander.Interface.euclideanDivergence (C.Xl i.succ) ξ +
        fieldDerivative (C.Xl i.succ) a ξ) * fieldDerivative (zField C i.succ η) g (C.Θ η ξ)) =
        ∑ i : Fin q, 2 * (fieldDerivative (zField C i.succ η) g (C.Θ η ξ) *
          (φ ξ * (a ξ * Hormander.Interface.euclideanDivergence (C.Xl i.succ) ξ +
            fieldDerivative (C.Xl i.succ) a ξ))) := by
      simp only [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    calc _ = φ ξ * (a ξ * (C.modelAdjoint g (C.Θ η ξ) + C.leftErrorOp η g (C.Θ η ξ))) +
          φ ξ * (2 * ∑ i : Fin q, (a ξ * Hormander.Interface.euclideanDivergence (C.Xl i.succ) ξ +
            fieldDerivative (C.Xl i.succ) a ξ) *
              fieldDerivative (zField C i.succ η) g (C.Θ η ξ)) +
          φ ξ * (sumSquaresWithDriftTranspose C.Xl a ξ * g (C.Θ η ξ)) := by ring
      _ = _ := by rw [hs]; ring
  have hLHS : (∫ ξ in C.U, g (C.Θ η ξ) * (sumSquaresWithDrift C.Xl φ ξ * a ξ)) =
      ∫ ξ in C.U, φ ξ * sumSquaresWithDriftTranspose C.Xl h ξ := by
    refine Eq.trans ?_ hdual
    refine setIntegral_congr_fun hmeas (fun ξ hξ => ?_)
    show _ = sumSquaresWithDrift C.Xl φ ξ * h ξ
    rw [hh, pullbackTest_apply hη ha g hξ]
    ring
  rw [hLHS, setIntegral_congr_fun hmeas hpt]
  -- the transported pieces
  have pL := integrableOn_integral_comp_theta_mul_smooth hη (contDiffOn_modelAdjoint hg)
    (testMultiplierOn C.chartOpens a ha φ)
  have pE := integrableOn_integral_comp_theta_mul_smooth hη (contDiffOn_leftErrorOp hη hg)
    (testMultiplierOn C.chartOpens a ha φ)
  have pZ : ∀ i : Fin q, _ := fun i => integrableOn_integral_comp_theta_mul_smooth hη
    (S.contDiffOn_fieldDerivative (C.modelOpens η) (zField C i.succ η) g
      (contDiffOn_zField hη i.succ) hg)
    (testMultiplierOn C.chartOpens (C.leftBetaCoeff a i) (contDiffOn_leftBetaCoeff ha i) φ)
  have pG := integrableOn_integral_comp_theta_mul_smooth hη hg
    (testMultiplierOn C.chartOpens (sumSquaresWithDriftTranspose C.Xl a)
      (contDiffOn_sumSquaresWithDriftTranspose_Xl ha) φ)
  have iL : IntegrableOn (fun ξ => C.modelAdjoint g (C.Θ η ξ) * (φ ξ * a ξ)) C.U := pL.1
  have iE : IntegrableOn (fun ξ => C.leftErrorOp η g (C.Θ η ξ) * (φ ξ * a ξ)) C.U := pE.1
  have iZ : ∀ i : Fin q, IntegrableOn (fun ξ => 2 * (fieldDerivative (zField C i.succ η) g
      (C.Θ η ξ) * (φ ξ * C.leftBetaCoeff a i ξ))) C.U := fun i => (pZ i).1.const_mul 2
  have iG : IntegrableOn (fun ξ => g (C.Θ η ξ) * (φ ξ * sumSquaresWithDriftTranspose C.Xl a ξ))
      C.U := pG.1
  have iLE : IntegrableOn (fun ξ => C.modelAdjoint g (C.Θ η ξ) * (φ ξ * a ξ) +
      C.leftErrorOp η g (C.Θ η ξ) * (φ ξ * a ξ)) C.U := iL.add iE
  have iZs : IntegrableOn (fun ξ => ∑ i : Fin q, 2 * (fieldDerivative (zField C i.succ η) g
      (C.Θ η ξ) * (φ ξ * C.leftBetaCoeff a i ξ))) C.U :=
    integrable_finsetSum _ (fun i _ => iZ i)
  have iLEZ : IntegrableOn (fun ξ => C.modelAdjoint g (C.Θ η ξ) * (φ ξ * a ξ) +
      C.leftErrorOp η g (C.Θ η ξ) * (φ ξ * a ξ) + ∑ i : Fin q, 2 * (fieldDerivative
        (zField C i.succ η) g (C.Θ η ξ) * (φ ξ * C.leftBetaCoeff a i ξ))) C.U := iLE.add iZs
  have qL : (∫ ξ in C.U, C.modelAdjoint g (C.Θ η ξ) * (φ ξ * a ξ)) =
      ∫ u in (C.e η).target, C.modelAdjoint g u * alphaT C hη ha φ u := pL.2
  have qE : (∫ ξ in C.U, C.leftErrorOp η g (C.Θ η ξ) * (φ ξ * a ξ)) =
      ∫ u in (C.e η).target, C.leftErrorOp η g u * alphaT C hη ha φ u := pE.2
  have qZ : ∀ i : Fin q, (∫ ξ in C.U, fieldDerivative (zField C i.succ η) g (C.Θ η ξ) *
      (φ ξ * C.leftBetaCoeff a i ξ)) =
      ∫ u in (C.e η).target, fieldDerivative (zField C i.succ η) g u * betaL C hη ha φ i u :=
    fun i => (pZ i).2
  have qG : (∫ ξ in C.U, g (C.Θ η ξ) * (φ ξ * sumSquaresWithDriftTranspose C.Xl a ξ)) =
      ∫ u in (C.e η).target, g u * lamL C hη ha φ u := pG.2
  rw [integral_add iLEZ iG, integral_add iLE iZs, integral_add iL iE,
    integral_finsetSum _ (fun i _ => iZ i),
    integral_smooth_mul_leftPoleTranspose hq ν₀ hη hg, qL, qE, qG]
  congr 2
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [integral_const_mul, qZ i, integral_const_mul]

theorem continuous_leftPoleTranspose {η : Fin (n + m) → ℝ} (hη : η ∈ C.U)
    (α : TestFunction (C.modelOpens η) ℝ (⊤ : ℕ∞))
    (β : Fin q → TestFunction (C.modelOpens η) ℝ (⊤ : ℕ∞))
    (lam : TestFunction (C.modelOpens η) ℝ (⊤ : ℕ∞)) :
    Continuous (C.leftPoleTranspose η α (fun i => β i) lam) := by
  let W := C.modelOpens η
  have hZs : ∀ i : Fin q, ContDiffOn ℝ (⊤ : ℕ∞) (zField C i.succ η)
      (W : Set (Fin (n + m) → ℝ)) := fun i => contDiffOn_zField hη i.succ
  have h1 : Continuous (sumSquaresWithDrift C.Y α) := by
    have := (sumSquaresWithDriftTest W C.Y (fun i => contDiffOn_Y_model i) α).continuous
    rwa [sumSquaresWithDriftTest_coe] at this
  have h2 : Continuous (C.leftErrorTranspose η α) := by
    have e1 := (C.errorTransposeTest hη α).continuous
    rw [errorTransposeTest_coe] at e1
    have e2 := (fieldTransposeTest W (C.R [0] η) (contDiffOn_R_model hη _) α).continuous
    rw [S.fieldTransposeTest_coe] at e2
    exact e1.sub (continuous_const.mul e2)
  have h3 : Continuous (fun u => ∑ i : Fin q, 2 * fieldTranspose (zField C i.succ η) (β i) u) :=
    continuous_finsetSum _ (fun i _ => continuous_const.mul (by
      have := (fieldTransposeTest W (zField C i.succ η) (hZs i) (β i)).continuous
      rwa [S.fieldTransposeTest_coe] at this))
  exact ((h1.add h2).add h3).add lam.continuous

/-- The transported test `(L̃φ) a` equals `T*(α, β, λ)` on the target of `e η`:
the transpose of the operator `L̃*` in the model variable (the pole computation, "the transformed
test is compactly supported"; both sides pair identically with every compactly supported
smooth `g`). -/
theorem modelTransport_eq_leftPoleTranspose (hq : 0 < q) (ν₀ : G2.HomogeneousNorm C.G)
    {η : Fin (n + m) → ℝ} (hη : η ∈ C.U) {a : (Fin (n + m) → ℝ) → ℝ}
    (ha : ContDiffOn ℝ (⊤ : ℕ∞) a C.U) (φ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞)) :
    ∀ u ∈ (C.e η).target,
      C.modelTransport η (fun ξ => sumSquaresWithDrift C.Xl φ ξ * a ξ) u =
        C.leftPoleTranspose η (alphaT C hη ha φ) (fun i => betaL C hη ha φ i)
          (lamL C hη ha φ) u := by
  set S' := C.modelTransport η (fun ξ => sumSquaresWithDrift C.Xl φ ξ * a ξ) with hS'
  set T := C.leftPoleTranspose η (alphaT C hη ha φ) (fun i => betaL C hη ha φ i)
    (lamL C hη ha φ) with hT
  have hTc : Continuous T := continuous_leftPoleTranspose hη _ _ _
  have hS'c : Continuous S' := by
    let LφT : TestFunction C.chartOpens ℝ (⊤ : ℕ∞) :=
      sumSquaresWithDriftTest C.chartOpens C.Xl C.contDiffOn_Xl_U φ
    let ψ' : TestFunction C.chartOpens ℝ (⊤ : ℕ∞) := testMultiplierOn C.chartOpens a ha LφT
    have hψ' : (ψ' : (Fin (n + m) → ℝ) → ℝ) = fun ξ => sumSquaresWithDrift C.Xl φ ξ * a ξ := by
      funext ξ
      show LφT ξ * a ξ = _
      rw [show (LφT : (Fin (n + m) → ℝ) → ℝ) = sumSquaresWithDrift C.Xl φ from
        sumSquaresWithDriftTest_coe C.chartOpens C.Xl C.contDiffOn_Xl_U φ]
    have e : S' = (modelTransportTest hη ψ' : (Fin (n + m) → ℝ) → ℝ) := by
      rw [hS', ← hψ']
      rfl
    rw [e]
    exact (modelTransportTest hη ψ').continuous
  have key : ∀ g : (Fin (n + m) → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g →
      tsupport g ⊆ (C.e η).target → ∫ x, g x • (S' x - T x) = 0 := by
    intro g hg hcs hts
    let gT : TestFunction (C.modelOpens η) ℝ (⊤ : ℕ∞) := ⟨g, hg, hcs, hts⟩
    have h1 := integral_comp_theta_mul_sumSquares_test hq ν₀ hη ha φ gT
    have h2 := integral_comp_theta_mul hη g (fun ξ => sumSquaresWithDrift C.Xl φ ξ * a ξ)
    have h1' : (∫ ξ in C.U, g (C.Θ η ξ) * (sumSquaresWithDrift C.Xl φ ξ * a ξ)) =
        ∫ x in (C.e η).target, g x * T x := h1
    rw [h1'] at h2
    have hz : ∀ x ∉ (C.e η).target, g x * T x = 0 := fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hts h)), zero_mul]
    have hgT : (∫ x in (C.e η).target, g x * T x) = ∫ x, g x * T x :=
      setIntegral_eq_integral_of_forall_compl_eq_zero hz
    have iS : Integrable (fun x => g x * S' x) :=
      (hg.continuous.mul hS'c).integrable_of_hasCompactSupport hcs.mul_right
    have iT : Integrable (fun x => g x * T x) :=
      (hg.continuous.mul hTc).integrable_of_hasCompactSupport hcs.mul_right
    simp only [smul_eq_mul, mul_sub]
    rw [integral_sub iS iT, ← h2, hgT, sub_self]
  have hae := (C.e η).open_target.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (μ := (volume : Measure (Fin (n + m) → ℝ))) (f := fun x => S' x - T x)
    ((hS'c.sub hTc).locallyIntegrable.locallyIntegrableOn _) key
  have hae' : (fun x => S' x - T x) =ᵐ[volume.restrict (C.e η).target] fun _ => (0 : ℝ) :=
    (ae_restrict_iff' (C.e η).open_target.measurableSet).2 hae
  intro u hu
  exact sub_eq_zero.1 (Measure.eqOn_open_of_ae_eq hae' (C.e η).open_target
    (hS'c.sub hTc).continuousOn continuousOn_const hu)

/-- The pole of the left parametrix with an output multiplier `a`:
for the H1 fundamental kernel `Γ*` of the reversed-drift lifted model, `η ∈ C.U`, `a` smooth on
`C.U` and a test `φ` on `C.U`,
`∫_U a Γ*(Θ η ξ) L̃φ(ξ) dξ = c(η) a(η) φ(η) + ∫_U (a (E*_η Γ*)(Θ η ξ) +
  2 ∑ᵢ (a dᵢ + X̃ᵢ a)(ξ) (Zᵢ Γ*)(Θ η ξ) + (L̃* a)(ξ) Γ*(Θ η ξ)) φ(ξ) dξ`,
`E*_η = ∑ᵢ (Yᵢ Rᵢ + Rᵢ Yᵢ + Rᵢ²) − R₀` (`leftPoleError`, negative drift sign) and the
integrand on the right is integrable (BB pp. 560–563; the pole computation: the density `c(η)` is the
only pole contribution, the cutoff-shell terms vanish in the limit). -/
theorem integral_kernel_comp_theta_mul_sumSquares (hq : 0 < q) (ν₀ : G2.HomogeneousNorm C.G)
    (K : H1.FundamentalKernel C.G ((C.driftModel hq ν₀).reverseDrift C.G))
    {η : Fin (n + m) → ℝ} (hη : η ∈ C.U) {a : (Fin (n + m) → ℝ) → ℝ}
    (ha : ContDiffOn ℝ (⊤ : ℕ∞) a C.U) (φ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞)) :
    IntegrableOn (fun ξ => C.leftErrBracket K a η ξ * φ ξ) C.U ∧
    (∫ ξ in C.U, a ξ * K (C.Θ η ξ) * sumSquaresWithDrift C.Xl φ ξ) =
      C.c η * (a η * φ η) + ∫ ξ in C.U, C.leftErrBracket K a η ξ * φ ξ := by
  have hNZ : NeZero (n + m) := ⟨C.G.dimension_pos.ne'⟩
  have hmeas : MeasurableSet C.U := C.isOpen_U.measurableSet
  have hEI := errorIbp_kernel K hη
  -- the transported pieces
  have pE := integrableOn_integral_comp_theta_mul hη (F := C.leftErrorOp η K)
    (ψ := fun ξ => φ ξ * a ξ) (hEI.integrableOn_leftErrorOp_mul (alphaT C hη ha φ))
  have pZ : ∀ i : Fin q, _ := fun i => integrableOn_integral_comp_theta_mul hη
    (F := fieldDerivative (zField C i.succ η) K) (ψ := fun ξ => φ ξ * C.leftBetaCoeff a i ξ)
    ((hEI.zg i (betaL C hη ha φ i)).1)
  have pK := integrableOn_integral_comp_theta_mul_test hη (F := (K : (Fin (n + m) → ℝ) → ℝ))
    (K.locallyIntegrable.locallyIntegrableOn _)
    (testMultiplierOn C.chartOpens (sumSquaresWithDriftTranspose C.Xl a)
      (contDiffOn_sumSquaresWithDriftTranspose_Xl ha) φ)
  have iE : IntegrableOn (fun ξ => C.leftErrorOp η K (C.Θ η ξ) * (φ ξ * a ξ)) C.U := pE.1
  have iZ : ∀ i : Fin q, IntegrableOn (fun ξ => 2 * (fieldDerivative (zField C i.succ η) K
      (C.Θ η ξ) * (φ ξ * C.leftBetaCoeff a i ξ))) C.U := fun i => (pZ i).1.const_mul 2
  have iK : IntegrableOn (fun ξ => K (C.Θ η ξ) * (φ ξ * sumSquaresWithDriftTranspose C.Xl a ξ))
      C.U := pK.1
  -- a.e. identification of the integrand
  have h0 : ∀ᵐ ξ ∂(volume : Measure (Fin (n + m) → ℝ)), ξ ≠ η := by
    have : ({η} : Set (Fin (n + m) → ℝ))ᶜ ∈ ae (volume : Measure (Fin (n + m) → ℝ)) := by
      rw [compl_mem_ae_iff]
      simp
    exact this
  have hpt : (fun ξ => C.leftErrBracket K a η ξ * φ ξ) =ᵐ[volume.restrict C.U]
      fun ξ => C.leftErrorOp η K (C.Θ η ξ) * (φ ξ * a ξ) +
        ∑ i : Fin q, 2 * (fieldDerivative (zField C i.succ η) K (C.Θ η ξ) *
          (φ ξ * C.leftBetaCoeff a i ξ)) +
        K (C.Θ η ξ) * (φ ξ * sumSquaresWithDriftTranspose C.Xl a ξ) := by
    filter_upwards [(ae_restrict_iff' hmeas).2 (Filter.Eventually.of_forall fun ξ hξ => hξ),
      ae_restrict_of_ae h0] with ξ hξ hne
    have hΘ : C.Θ η ξ ≠ 0 := C.theta_ne_zero hη hξ hne
    have hE := C.leftPoleError_eq_leftErrorOp hη
      (isOpen_compl_singleton (x := (0 : Fin (n + m) → ℝ))) K.smooth_off_zero hΘ
      (C.theta_mem_target hη hξ)
    simp only [leftErrBracket, zDeriv_eq_zField, hE]
    have hs : (2 * ∑ i : Fin q, C.leftBetaCoeff a i ξ *
        fieldDerivative (zField C i.succ η) K (C.Θ η ξ)) * φ ξ =
        ∑ i : Fin q, 2 * (fieldDerivative (zField C i.succ η) K (C.Θ η ξ) *
          (φ ξ * C.leftBetaCoeff a i ξ)) := by
      rw [Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    calc _ = a ξ * C.leftErrorOp η K (C.Θ η ξ) * φ ξ +
          (2 * ∑ i : Fin q, C.leftBetaCoeff a i ξ *
            fieldDerivative (zField C i.succ η) K (C.Θ η ξ)) * φ ξ +
          sumSquaresWithDriftTranspose C.Xl a ξ * K (C.Θ η ξ) * φ ξ := by ring
      _ = _ := by rw [hs]; ring
  have hint : IntegrableOn (fun ξ => C.leftErrBracket K a η ξ * φ ξ) C.U :=
    ((iE.add (integrable_finsetSum _ (fun i _ => iZ i))).add iK).congr_fun_ae hpt.symm
  refine ⟨hint, ?_⟩
  have qE : (∫ ξ in C.U, C.leftErrorOp η K (C.Θ η ξ) * (φ ξ * a ξ)) =
      ∫ u in (C.e η).target, C.leftErrorOp η K u * alphaT C hη ha φ u := pE.2
  have qZ : ∀ i : Fin q, (∫ ξ in C.U, 2 * (fieldDerivative (zField C i.succ η) K (C.Θ η ξ) *
      (φ ξ * C.leftBetaCoeff a i ξ))) =
      ∫ u in (C.e η).target, 2 * (fieldDerivative (zField C i.succ η) K u *
        betaL C hη ha φ i u) := fun i => by
    have h2 : (∫ ξ in C.U, fieldDerivative (zField C i.succ η) K (C.Θ η ξ) *
        (φ ξ * C.leftBetaCoeff a i ξ)) =
        ∫ u in (C.e η).target, fieldDerivative (zField C i.succ η) K u * betaL C hη ha φ i u :=
      (pZ i).2
    rw [integral_const_mul, h2, integral_const_mul]
  have qK : (∫ ξ in C.U, K (C.Θ η ξ) * (φ ξ * sumSquaresWithDriftTranspose C.Xl a ξ)) =
      ∫ u in (C.e η).target, K u * lamL C hη ha φ u := pK.2
  have hS := modelTransport_eq_leftPoleTranspose hq ν₀ hη ha φ
  have hL : (∫ ξ in C.U, a ξ * K (C.Θ η ξ) * sumSquaresWithDrift C.Xl φ ξ) =
      ∫ u in (C.e η).target, K u * C.leftPoleTranspose η (alphaT C hη ha φ)
        (fun i => betaL C hη ha φ i) (lamL C hη ha φ) u := by
    calc (∫ ξ in C.U, a ξ * K (C.Θ η ξ) * sumSquaresWithDrift C.Xl φ ξ)
        = ∫ ξ in C.U, K (C.Θ η ξ) * (sumSquaresWithDrift C.Xl φ ξ * a ξ) :=
          setIntegral_congr_fun hmeas (fun ξ _ => by ring)
      _ = ∫ u, K u * C.modelTransport η
            (fun ξ => sumSquaresWithDrift C.Xl φ ξ * a ξ) u :=
          integral_comp_theta_mul hη _ _
      _ = ∫ u in (C.e η).target, K u * C.modelTransport η
            (fun ξ => sumSquaresWithDrift C.Xl φ ξ * a ξ) u :=
          (setIntegral_eq_integral_of_forall_compl_eq_zero
            (fun u hu => by simp [modelTransport_of_notMem hu])).symm
      _ = ∫ u in (C.e η).target, K u * C.leftPoleTranspose η (alphaT C hη ha φ)
            (fun i => betaL C hη ha φ i) (lamL C hη ha φ) u :=
          setIntegral_congr_fun (C.e η).open_target.measurableSet
            (fun u hu => by rw [hS u hu])
  have iZs : IntegrableOn (fun ξ => ∑ i : Fin q, 2 * (fieldDerivative (zField C i.succ η) K
      (C.Θ η ξ) * (φ ξ * C.leftBetaCoeff a i ξ))) C.U :=
    integrable_finsetSum _ (fun i _ => iZ i)
  have iEZ : IntegrableOn (fun ξ => C.leftErrorOp η K (C.Θ η ξ) * (φ ξ * a ξ) +
      ∑ i : Fin q, 2 * (fieldDerivative (zField C i.succ η) K
      (C.Θ η ξ) * (φ ξ * C.leftBetaCoeff a i ξ))) C.U := iE.add iZs
  rw [hL, integral_kernel_mul_leftPoleTranspose hq ν₀ K hη, alphaT_zero hη ha φ,
    integral_congr_ae hpt, integral_add iEZ iK, integral_add iE iZs,
    integral_finsetSum _ (fun i _ => iZ i), qE, qK]
  simp only [qZ]
  ring

end LiftedChart

end RothschildStein.P1
