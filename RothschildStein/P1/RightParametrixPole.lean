-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.RightParametrixPairing

/-!
# The pole limit: the pole of the right parametrix contributes `a(η) φ(η)`

The right pole `Γ(Θ(η, ξ))` tested in `ξ` against `L̃ᵀφ`, with an output cutoff `a` (the
right pole computation). Substituting `u = Θ(η, ξ)` (`LiftedChart.modelTransport`) and testing against smooth
`g` in the model variable gives `∫ g · S = ∫ g · T(α, β, λ)` with `S` the transported
`a L̃ᵀφ` and `α = (aφ)~`, `βᵢ = ((X̃ᵢ a)φ)~`, `λ = ((L̃ a)φ)~`; hence `S = T(α, β, λ)`
(`modelTransport_eq_poleTranspose`). For the fundamental kernel `Γ` of `𝓛 = ∑ Yᵢ² + Y₀`,
`∫ Γ 𝓛ᵀα = α(0) = c(η) a(η) φ(η)` (`𝓛Γ = δ₀`, density `c(η)`), and the remaining terms are the
absolutely convergent errors of the right pole formula: `integral_kernel_comp_theta_mul_transpose`.
With `a ≡ 1` this is the pole limit `∫ Γ(Θ) L̃ᵀψ = c(η) ψ(η) + ∫ (E_η Γ)(Θ) ψ`
(`integral_kernel_comp_theta_transpose`).
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
  {C : LiftedChart (fun i : Fin (q + 1) => if i = 0 then (2 : ℕ+) else 1) s Ω hΩ X x₀ m}

theorem contDiffOn_fieldDerivative_Xl {a : (Fin (n + m) → ℝ) → ℝ}
    (ha : ContDiffOn ℝ (⊤ : ℕ∞) a C.U) (i : Fin (q + 1)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fieldDerivative (C.Xl i) a) C.U :=
  S.contDiffOn_fieldDerivative C.chartOpens (C.Xl i) a (C.contDiffOn_Xl_U i) ha

theorem contDiffOn_sumSquaresWithDrift_Xl {a : (Fin (n + m) → ℝ) → ℝ}
    (ha : ContDiffOn ℝ (⊤ : ℕ∞) a C.U) :
    ContDiffOn ℝ (⊤ : ℕ∞) (sumSquaresWithDrift C.Xl a) C.U :=
  contDiffOn_sumSquaresWithDrift C.chartOpens C.Xl C.contDiffOn_Xl_U ha

/-- The error operator preserves smoothness on the target of `e η`. -/
theorem contDiffOn_errorOp {η : Fin (n + m) → ℝ} (hη : η ∈ C.U) {g : (Fin (n + m) → ℝ) → ℝ}
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g (C.e η).target) :
    ContDiffOn ℝ (⊤ : ℕ∞) (C.errorOp η g) (C.e η).target := by
  let W := C.modelOpens η
  have hYs : ∀ i : Fin q, ContDiffOn ℝ (⊤ : ℕ∞) (C.Y i.succ) (W : Set (Fin (n + m) → ℝ)) :=
    fun i => (C.model_field_smooth i.succ).contDiffOn
  have hRs : ∀ I : List (Fin (q + 1)), ContDiffOn ℝ (⊤ : ℕ∞) (C.R I η) (W : Set (Fin (n + m) → ℝ)) :=
    fun I => C.contDiffOn_remainder hη I
  have hZs : ∀ i : Fin q, ContDiffOn ℝ (⊤ : ℕ∞) (zField C i.succ η)
      (W : Set (Fin (n + m) → ℝ)) := fun i => contDiffOn_zField hη i.succ
  have h1 : ∀ i : Fin q, ContDiffOn ℝ (⊤ : ℕ∞) (fun u =>
      fieldDerivative (C.Y i.succ) (fieldDerivative (C.R [i.succ] η) g) u +
      fieldDerivative (C.R [i.succ] η) (fieldDerivative (zField C i.succ η) g) u)
      (W : Set (Fin (n + m) → ℝ)) := fun i =>
    (S.contDiffOn_fieldDerivative W _ _ (hYs i) (S.contDiffOn_fieldDerivative W _ g (hRs _) hg)).add
      (S.contDiffOn_fieldDerivative W _ _ (hRs _)
        (S.contDiffOn_fieldDerivative W _ g (hZs i) hg))
  exact (ContDiffOn.sum fun i _ => h1 i).add (S.contDiffOn_fieldDerivative W _ g (hRs _) hg)

/-- Integrability of `(E g) α` from the pairs of `ErrorIbp`. -/
theorem ErrorIbp.integrableOn_errorOp_mul {η : Fin (n + m) → ℝ} {g : (Fin (n + m) → ℝ) → ℝ}
    (h : ErrorIbp C η g) (α : TestFunction (C.modelOpens η) ℝ (⊤ : ℕ∞)) :
    IntegrableOn (fun u => C.errorOp η g u * α u) (C.e η).target := by
  have e1 : ∀ u, C.errorOp η g u * α u =
      ∑ i : Fin q, (fieldDerivative (C.Y i.succ) (fieldDerivative (C.R [i.succ] η) g) u * α u +
        fieldDerivative (C.R [i.succ] η) (fieldDerivative (zField C i.succ η) g) u * α u) +
      fieldDerivative (C.R [0] η) g u * α u := by
    intro u
    simp only [errorOp, add_mul, Finset.sum_mul]
  refine IntegrableOn.congr_fun
    ((integrable_finsetSum _ (fun i _ => (h.yr i α).1.add (h.rz i α).1)).add (h.r0 α).1)
    (fun u _ => (e1 u).symm) (C.e η).open_target.measurableSet

/-- The pointwise form of the output product formula against a value `t` of
the test: `L̃(a (g ∘ Θ η)) · t` splits into the model, error, first-order and zeroth-order
terms. -/
theorem sumSquaresWithDrift_mul_comp_theta_mul {η ξ : Fin (n + m) → ℝ} (hη : η ∈ C.U)
    (hξ : ξ ∈ C.U) {a g : (Fin (n + m) → ℝ) → ℝ} (ha : ContDiffOn ℝ (⊤ : ℕ∞) a C.U)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g (C.e η).target) (t : ℝ) :
    sumSquaresWithDrift C.Xl (fun ξ' => a ξ' * g (C.Θ η ξ')) ξ * t =
      sumSquaresWithDrift C.Y g (C.Θ η ξ) * (t * a ξ) + C.errorOp η g (C.Θ η ξ) * (t * a ξ) +
      ∑ i : Fin q, 2 * (fieldDerivative (zField C i.succ η) g (C.Θ η ξ) *
        (t * fieldDerivative (C.Xl i.succ) a ξ)) +
      g (C.Θ η ξ) * (t * sumSquaresWithDrift C.Xl a ξ) := by
  have hmem := C.theta_mem_target hη hξ
  have h1 := C.sumSquaresWithDrift_mul_comp_theta hη (C.e η).open_target hg ha hξ hmem
  rw [h1, C.rightPoleError_eq_errorOp hη (C.e η).open_target hg hmem hmem]
  have hz : ∀ i : Fin q, C.zDeriv η i.succ g (C.Θ η ξ) =
      fieldDerivative (zField C i.succ η) g (C.Θ η ξ) := fun i => by
    rw [zDeriv_eq_fieldDerivative]
  simp only [hz]
  have hs : (2 * ∑ i : Fin q, fieldDerivative (C.Xl i.succ) a ξ *
      fieldDerivative (zField C i.succ η) g (C.Θ η ξ)) * t =
      ∑ i : Fin q, 2 * (fieldDerivative (zField C i.succ η) g (C.Θ η ξ) *
        (t * fieldDerivative (C.Xl i.succ) a ξ)) := by
    rw [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  calc _ = a ξ * (sumSquaresWithDrift C.Y g (C.Θ η ξ) + C.errorOp η g (C.Θ η ξ)) * t +
        (2 * ∑ i : Fin q, fieldDerivative (C.Xl i.succ) a ξ *
          fieldDerivative (zField C i.succ η) g (C.Θ η ξ)) * t +
        sumSquaresWithDrift C.Xl a ξ * g (C.Θ η ξ) * t := by ring
    _ = _ := by rw [hs]; ring

variable (C) in
/-- The transported test `(a φ)~` on the target of `e η`. -/
def alphaT {η : Fin (n + m) → ℝ} (hη : η ∈ C.U) {a : (Fin (n + m) → ℝ) → ℝ}
    (ha : ContDiffOn ℝ (⊤ : ℕ∞) a C.U) (φ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞)) :
    TestFunction (C.modelOpens η) ℝ (⊤ : ℕ∞) :=
  modelTransportTest hη (testMultiplierOn C.chartOpens a ha φ)

variable (C) in
/-- The transported tests `((X̃ᵢ a) φ)~`. -/
def betaT {η : Fin (n + m) → ℝ} (hη : η ∈ C.U) {a : (Fin (n + m) → ℝ) → ℝ}
    (ha : ContDiffOn ℝ (⊤ : ℕ∞) a C.U) (φ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞)) (i : Fin q) :
    TestFunction (C.modelOpens η) ℝ (⊤ : ℕ∞) :=
  modelTransportTest hη (testMultiplierOn C.chartOpens (fieldDerivative (C.Xl i.succ) a)
    (contDiffOn_fieldDerivative_Xl ha i.succ) φ)

variable (C) in
/-- The transported test `((L̃ a) φ)~`. -/
def lamT {η : Fin (n + m) → ℝ} (hη : η ∈ C.U) {a : (Fin (n + m) → ℝ) → ℝ}
    (ha : ContDiffOn ℝ (⊤ : ℕ∞) a C.U) (φ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞)) :
    TestFunction (C.modelOpens η) ℝ (⊤ : ℕ∞) :=
  modelTransportTest hη (testMultiplierOn C.chartOpens (sumSquaresWithDrift C.Xl a)
    (contDiffOn_sumSquaresWithDrift_Xl ha) φ)

theorem integrableOn_integral_comp_theta_mul_smooth {η : Fin (n + m) → ℝ} (hη : η ∈ C.U)
    {F : (Fin (n + m) → ℝ) → ℝ} (hF : ContDiffOn ℝ (⊤ : ℕ∞) F (C.e η).target)
    (ψ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞)) :
    IntegrableOn (fun ξ => F (C.Θ η ξ) * ψ ξ) C.U ∧
      ∫ ξ in C.U, F (C.Θ η ξ) * ψ ξ = ∫ u in (C.e η).target, F u * modelTransportTest hη ψ u :=
  integrableOn_integral_comp_theta_mul_test hη
    (hF.continuousOn.locallyIntegrableOn (C.e η).open_target.measurableSet) ψ

/-- The pairing of a smooth function `g` of the model variable with the
transported test, `∫_U g(Θ η ξ) (a L̃ᵀφ)(ξ) dξ = ∫ g T(α, β, λ)` (duality for `L̃`, the chain rule
`L̃(g ∘ Θ η) = (𝓛 g + E g) ∘ Θ η`, the substitution `u = Θ η ξ` and model-variable integration by
parts). -/
theorem integral_comp_theta_mul_transpose_smooth {η : Fin (n + m) → ℝ} (hη : η ∈ C.U)
    {a : (Fin (n + m) → ℝ) → ℝ} (ha : ContDiffOn ℝ (⊤ : ℕ∞) a C.U)
    (φ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞)) {g : (Fin (n + m) → ℝ) → ℝ}
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g (C.e η).target) :
    (∫ ξ in C.U, g (C.Θ η ξ) * (sumSquaresWithDriftTranspose C.Xl φ ξ * a ξ)) =
      ∫ u in (C.e η).target, g u * C.poleTranspose η (alphaT C hη ha φ) (fun i => betaT C hη ha φ i)
        (lamT C hη ha φ) u := by
  rw [integral_smooth_mul_poleTranspose hη hg]
  have hmeas : MeasurableSet C.U := C.isOpen_U.measurableSet
  have hYs : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (C.Y i) ((C.modelOpens η : Opens (Fin (n + m) → ℝ)) :
      Set (Fin (n + m) → ℝ)) := fun i => (C.model_field_smooth i).contDiffOn
  have hgΘ : ContDiffOn ℝ (⊤ : ℕ∞) (fun ξ => a ξ * g (C.Θ η ξ)) C.U :=
    ha.mul (hg.comp (C.contDiffOn_theta hη) (fun ξ hξ => C.theta_mem_target hη hξ))
  have hdual := C.integral_sumSquaresWithDrift_mul_test_U (fun ξ => a ξ * g (C.Θ η ξ)) hgΘ φ
  have pL := integrableOn_integral_comp_theta_mul_smooth hη
    (contDiffOn_sumSquaresWithDrift (C.modelOpens η) C.Y hYs hg)
    (testMultiplierOn C.chartOpens a ha φ)
  have pE := integrableOn_integral_comp_theta_mul_smooth hη (contDiffOn_errorOp hη hg)
    (testMultiplierOn C.chartOpens a ha φ)
  have pZ : ∀ i : Fin q, _ := fun i => integrableOn_integral_comp_theta_mul_smooth hη
    (S.contDiffOn_fieldDerivative (C.modelOpens η) (zField C i.succ η) g
      (contDiffOn_zField hη i.succ) hg)
    (testMultiplierOn C.chartOpens (fieldDerivative (C.Xl i.succ) a)
      (contDiffOn_fieldDerivative_Xl ha i.succ) φ)
  have pG := integrableOn_integral_comp_theta_mul_smooth hη hg
    (testMultiplierOn C.chartOpens (sumSquaresWithDrift C.Xl a)
      (contDiffOn_sumSquaresWithDrift_Xl ha) φ)
  have iL : IntegrableOn (fun ξ => sumSquaresWithDrift C.Y g (C.Θ η ξ) * (φ ξ * a ξ)) C.U := pL.1
  have iE : IntegrableOn (fun ξ => C.errorOp η g (C.Θ η ξ) * (φ ξ * a ξ)) C.U := pE.1
  have iZ : ∀ i : Fin q, IntegrableOn (fun ξ => 2 * (fieldDerivative (zField C i.succ η) g
      (C.Θ η ξ) * (φ ξ * fieldDerivative (C.Xl i.succ) a ξ))) C.U := fun i => (pZ i).1.const_mul 2
  have iG : IntegrableOn (fun ξ => g (C.Θ η ξ) * (φ ξ * sumSquaresWithDrift C.Xl a ξ)) C.U := pG.1
  have iLE : IntegrableOn (fun ξ => sumSquaresWithDrift C.Y g (C.Θ η ξ) * (φ ξ * a ξ) +
      C.errorOp η g (C.Θ η ξ) * (φ ξ * a ξ)) C.U := iL.add iE
  have iZs : IntegrableOn (fun ξ => ∑ i : Fin q, 2 * (fieldDerivative (zField C i.succ η) g
      (C.Θ η ξ) * (φ ξ * fieldDerivative (C.Xl i.succ) a ξ))) C.U :=
    integrable_finsetSum _ (fun i _ => iZ i)
  have iLEZ : IntegrableOn (fun ξ => sumSquaresWithDrift C.Y g (C.Θ η ξ) * (φ ξ * a ξ) +
      C.errorOp η g (C.Θ η ξ) * (φ ξ * a ξ) + ∑ i : Fin q, 2 * (fieldDerivative (zField C i.succ η) g
      (C.Θ η ξ) * (φ ξ * fieldDerivative (C.Xl i.succ) a ξ))) C.U := iLE.add iZs
  have qL : (∫ ξ in C.U, sumSquaresWithDrift C.Y g (C.Θ η ξ) * (φ ξ * a ξ)) =
      ∫ u in (C.e η).target, sumSquaresWithDrift C.Y g u * alphaT C hη ha φ u := pL.2
  have qE : (∫ ξ in C.U, C.errorOp η g (C.Θ η ξ) * (φ ξ * a ξ)) =
      ∫ u in (C.e η).target, C.errorOp η g u * alphaT C hη ha φ u := pE.2
  have qZ : ∀ i : Fin q, (∫ ξ in C.U, fieldDerivative (zField C i.succ η) g (C.Θ η ξ) *
      (φ ξ * fieldDerivative (C.Xl i.succ) a ξ)) =
      ∫ u in (C.e η).target, fieldDerivative (zField C i.succ η) g u * betaT C hη ha φ i u :=
    fun i => (pZ i).2
  have qG : (∫ ξ in C.U, g (C.Θ η ξ) * (φ ξ * sumSquaresWithDrift C.Xl a ξ)) =
      ∫ u in (C.e η).target, g u * lamT C hη ha φ u := pG.2
  calc (∫ ξ in C.U, g (C.Θ η ξ) * (sumSquaresWithDriftTranspose C.Xl φ ξ * a ξ))
      = ∫ ξ in C.U, (a ξ * g (C.Θ η ξ)) * sumSquaresWithDriftTranspose C.Xl φ ξ :=
        setIntegral_congr_fun hmeas (fun ξ _ => by ring)
    _ = ∫ ξ in C.U, sumSquaresWithDrift C.Xl (fun ξ' => a ξ' * g (C.Θ η ξ')) ξ * φ ξ :=
        hdual.symm
    _ = ∫ ξ in C.U, (sumSquaresWithDrift C.Y g (C.Θ η ξ) * (φ ξ * a ξ) +
          C.errorOp η g (C.Θ η ξ) * (φ ξ * a ξ) +
          ∑ i : Fin q, 2 * (fieldDerivative (zField C i.succ η) g (C.Θ η ξ) *
            (φ ξ * fieldDerivative (C.Xl i.succ) a ξ)) +
          g (C.Θ η ξ) * (φ ξ * sumSquaresWithDrift C.Xl a ξ)) :=
        setIntegral_congr_fun hmeas (fun ξ hξ =>
          sumSquaresWithDrift_mul_comp_theta_mul hη hξ ha hg (φ ξ))
    _ = (∫ ξ in C.U, sumSquaresWithDrift C.Y g (C.Θ η ξ) * (φ ξ * a ξ)) +
        (∫ ξ in C.U, C.errorOp η g (C.Θ η ξ) * (φ ξ * a ξ)) +
        ∑ i : Fin q, (∫ ξ in C.U, 2 * (fieldDerivative (zField C i.succ η) g (C.Θ η ξ) *
          (φ ξ * fieldDerivative (C.Xl i.succ) a ξ))) +
        ∫ ξ in C.U, g (C.Θ η ξ) * (φ ξ * sumSquaresWithDrift C.Xl a ξ) := by
        rw [integral_add iLEZ iG, integral_add iLE iZs, integral_add iL iE,
          integral_finsetSum _ (fun i _ => iZ i)]
    _ = _ := by
        rw [qL, qE, qG]
        congr 2
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [integral_const_mul, qZ i, integral_const_mul]

theorem continuous_poleTranspose {η : Fin (n + m) → ℝ} (hη : η ∈ C.U)
    (α : TestFunction (C.modelOpens η) ℝ (⊤ : ℕ∞))
    (β : Fin q → TestFunction (C.modelOpens η) ℝ (⊤ : ℕ∞))
    (lam : TestFunction (C.modelOpens η) ℝ (⊤ : ℕ∞)) :
    Continuous (C.poleTranspose η α (fun i => β i) lam) := by
  let W := C.modelOpens η
  have hYs : ∀ i : Fin (q + 1), ContDiffOn ℝ (⊤ : ℕ∞) (C.Y i) (W : Set (Fin (n + m) → ℝ)) :=
    fun i => (C.model_field_smooth i).contDiffOn
  have hZs : ∀ i : Fin q, ContDiffOn ℝ (⊤ : ℕ∞) (zField C i.succ η)
      (W : Set (Fin (n + m) → ℝ)) := fun i => contDiffOn_zField hη i.succ
  have h1 : Continuous (sumSquaresWithDriftTranspose C.Y α) := by
    have := (sumSquaresWithDriftTransposeTest W C.Y hYs α).continuous
    rwa [sumSquaresWithDriftTransposeTest_coe] at this
  have h2 : Continuous (C.errorTranspose η α) := by
    have := (C.errorTransposeTest hη α).continuous
    rwa [errorTransposeTest_coe] at this
  have h3 : Continuous (fun u => ∑ i : Fin q, 2 * fieldTranspose (zField C i.succ η) (β i) u) :=
    continuous_finsetSum _ (fun i _ => continuous_const.mul (by
      have := (fieldTransposeTest W (zField C i.succ η) (hZs i) (β i)).continuous
      rwa [S.fieldTransposeTest_coe] at this))
  exact ((h1.add h2).add h3).add lam.continuous

/-- The transported test `a L̃ᵀφ` equals `T(α, β, λ)` on the target of `e η`:
the transpose of the operator `L̃` in the model variable (the right pole computation, "the transformed
test is compactly supported"; both sides pair identically with every smooth `g`). -/
theorem modelTransport_eq_poleTranspose {η : Fin (n + m) → ℝ} (hη : η ∈ C.U)
    {a : (Fin (n + m) → ℝ) → ℝ} (ha : ContDiffOn ℝ (⊤ : ℕ∞) a C.U)
    (φ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞)) :
    ∀ u ∈ (C.e η).target,
      C.modelTransport η (fun ξ => sumSquaresWithDriftTranspose C.Xl φ ξ * a ξ) u =
        C.poleTranspose η (alphaT C hη ha φ) (fun i => betaT C hη ha φ i) (lamT C hη ha φ) u := by
  set S' := C.modelTransport η (fun ξ => sumSquaresWithDriftTranspose C.Xl φ ξ * a ξ) with hS'
  set T := C.poleTranspose η (alphaT C hη ha φ) (fun i => betaT C hη ha φ i) (lamT C hη ha φ) with hT
  have hTc : Continuous T := continuous_poleTranspose hη _ _ _
  have hS'c : Continuous S' := by
    let LφT : TestFunction C.chartOpens ℝ (⊤ : ℕ∞) :=
      sumSquaresWithDriftTransposeTest C.chartOpens C.Xl C.contDiffOn_Xl_U φ
    let ψ' : TestFunction C.chartOpens ℝ (⊤ : ℕ∞) := testMultiplierOn C.chartOpens a ha LφT
    have hψ' : (ψ' : (Fin (n + m) → ℝ) → ℝ) =
        fun ξ => sumSquaresWithDriftTranspose C.Xl φ ξ * a ξ := by
      funext ξ
      show LφT ξ * a ξ = _
      rw [show (LφT : (Fin (n + m) → ℝ) → ℝ) = sumSquaresWithDriftTranspose C.Xl φ from
        sumSquaresWithDriftTransposeTest_coe C.chartOpens C.Xl C.contDiffOn_Xl_U φ]
    have e : S' = (modelTransportTest hη ψ' : (Fin (n + m) → ℝ) → ℝ) := by
      rw [hS', ← hψ']
      rfl
    rw [e]
    exact (modelTransportTest hη ψ').continuous
  have key : ∀ g : (Fin (n + m) → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g →
      tsupport g ⊆ (C.e η).target → ∫ x, g x • (S' x - T x) = 0 := by
    intro g hg hcs hts
    have hgs : ContDiffOn ℝ (⊤ : ℕ∞) g (C.e η).target := hg.contDiffOn
    have h1 := integral_comp_theta_mul_transpose_smooth hη ha φ hgs
    have h2 := integral_comp_theta_mul hη g
      (fun ξ => sumSquaresWithDriftTranspose C.Xl φ ξ * a ξ)
    rw [h1] at h2
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

/-- The diagonal value of the transported test: `(a φ)~(0) = c(η) a(η) φ(η)`. -/
theorem alphaT_zero {η : Fin (n + m) → ℝ} (hη : η ∈ C.U) {a : (Fin (n + m) → ℝ) → ℝ}
    (ha : ContDiffOn ℝ (⊤ : ℕ∞) a C.U) (φ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞)) :
    alphaT C hη ha φ 0 = C.c η * (φ η * a η) :=
  modelTransport_zero hη _

/-- The pole of the right parametrix with an output multiplier `a`:
for the H1 fundamental kernel `Γ` of the lifted drift model, `η ∈ C.U`, `a` smooth on `C.U` and a
test `φ` on `C.U`,
`∫_U a Γ(Θ η ξ) L̃ᵀφ(ξ) dξ = c(η) a(η) φ(η) + ∫_U (a (E_η Γ)(Θ η ξ) +
  2 ∑ᵢ (X̃ᵢ a)(ξ) (Zᵢ Γ)(Θ η ξ) + (L̃ a)(ξ) Γ(Θ η ξ)) φ(ξ) dξ`,
`E_η = ∑ᵢ (Yᵢ Rᵢ + Rᵢ Yᵢ + Rᵢ²) + R₀` (`rightPoleError`) and the integrand on the right
is integrable (BB p. 605, Prop 11.61 proof; the right pole computation: the density `c(η)` is the only
pole contribution, the cutoff-shell terms vanish in the limit). -/
theorem integral_kernel_comp_theta_mul_transpose (hq : 0 < q) (ν₀ : G2.HomogeneousNorm C.G)
    (K : H1.FundamentalKernel C.G (C.driftModel hq ν₀)) {η : Fin (n + m) → ℝ} (hη : η ∈ C.U)
    {a : (Fin (n + m) → ℝ) → ℝ} (ha : ContDiffOn ℝ (⊤ : ℕ∞) a C.U)
    (φ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞)) :
    IntegrableOn (fun ξ => (a ξ * C.rightPoleError η K (C.Θ η ξ) +
        2 * ∑ i : Fin q, fieldDerivative (C.Xl i.succ) a ξ * C.zDeriv η i.succ K (C.Θ η ξ) +
        sumSquaresWithDrift C.Xl a ξ * K (C.Θ η ξ)) * φ ξ) C.U ∧
    (∫ ξ in C.U, a ξ * K (C.Θ η ξ) * sumSquaresWithDriftTranspose C.Xl φ ξ) =
      C.c η * (a η * φ η) + ∫ ξ in C.U, (a ξ * C.rightPoleError η K (C.Θ η ξ) +
        2 * ∑ i : Fin q, fieldDerivative (C.Xl i.succ) a ξ * C.zDeriv η i.succ K (C.Θ η ξ) +
        sumSquaresWithDrift C.Xl a ξ * K (C.Θ η ξ)) * φ ξ := by
  have hNZ : NeZero (n + m) := ⟨C.G.dimension_pos.ne'⟩
  have hmeas : MeasurableSet C.U := C.isOpen_U.measurableSet
  have hEI := errorIbp_kernel K hη
  -- the transported pieces
  have pE := integrableOn_integral_comp_theta_mul hη (F := C.errorOp η K)
    (ψ := fun ξ => φ ξ * a ξ) (hEI.integrableOn_errorOp_mul (alphaT C hη ha φ))
  have pZ : ∀ i : Fin q, _ := fun i => integrableOn_integral_comp_theta_mul hη
    (F := fieldDerivative (zField C i.succ η) K) (ψ := fun ξ => φ ξ * fieldDerivative (C.Xl i.succ) a ξ)
    ((hEI.zg i (betaT C hη ha φ i)).1)
  have pK := integrableOn_integral_comp_theta_mul_test hη (F := (K : (Fin (n + m) → ℝ) → ℝ))
    (K.locallyIntegrable.locallyIntegrableOn _)
    (testMultiplierOn C.chartOpens (sumSquaresWithDrift C.Xl a)
      (contDiffOn_sumSquaresWithDrift_Xl ha) φ)
  have iE : IntegrableOn (fun ξ => C.errorOp η K (C.Θ η ξ) * (φ ξ * a ξ)) C.U := pE.1
  have iZ : ∀ i : Fin q, IntegrableOn (fun ξ => 2 * (fieldDerivative (zField C i.succ η) K
      (C.Θ η ξ) * (φ ξ * fieldDerivative (C.Xl i.succ) a ξ))) C.U := fun i => (pZ i).1.const_mul 2
  have iK : IntegrableOn (fun ξ => K (C.Θ η ξ) * (φ ξ * sumSquaresWithDrift C.Xl a ξ)) C.U :=
    pK.1
  -- a.e. identification of the integrand
  have h0 : ∀ᵐ ξ ∂(volume : Measure (Fin (n + m) → ℝ)), ξ ≠ η := by
    have : ({η} : Set (Fin (n + m) → ℝ))ᶜ ∈ ae (volume : Measure (Fin (n + m) → ℝ)) := by
      rw [compl_mem_ae_iff]
      simp
    exact this
  have hpt : (fun ξ => (a ξ * C.rightPoleError η K (C.Θ η ξ) +
        2 * ∑ i : Fin q, fieldDerivative (C.Xl i.succ) a ξ * C.zDeriv η i.succ K (C.Θ η ξ) +
        sumSquaresWithDrift C.Xl a ξ * K (C.Θ η ξ)) * φ ξ) =ᵐ[volume.restrict C.U]
      fun ξ => C.errorOp η K (C.Θ η ξ) * (φ ξ * a ξ) +
        ∑ i : Fin q, 2 * (fieldDerivative (zField C i.succ η) K (C.Θ η ξ) *
          (φ ξ * fieldDerivative (C.Xl i.succ) a ξ)) +
        K (C.Θ η ξ) * (φ ξ * sumSquaresWithDrift C.Xl a ξ) := by
    filter_upwards [(ae_restrict_iff' hmeas).2 (Filter.Eventually.of_forall fun ξ hξ => hξ),
      ae_restrict_of_ae h0] with ξ hξ hne
    have hΘ : C.Θ η ξ ≠ 0 := C.theta_ne_zero hη hξ hne
    have hE := C.rightPoleError_eq_errorOp hη (isOpen_compl_singleton (x := (0 : Fin (n + m) → ℝ)))
      K.smooth_off_zero hΘ (C.theta_mem_target hη hξ)
    have hz : ∀ i : Fin q, C.zDeriv η i.succ K (C.Θ η ξ) =
        fieldDerivative (zField C i.succ η) K (C.Θ η ξ) := fun i => by
      rw [zDeriv_eq_fieldDerivative]
    simp only [hz]
    rw [hE]
    have hs : (2 * ∑ i : Fin q, fieldDerivative (C.Xl i.succ) a ξ *
        fieldDerivative (zField C i.succ η) K (C.Θ η ξ)) * φ ξ =
        ∑ i : Fin q, 2 * (fieldDerivative (zField C i.succ η) K (C.Θ η ξ) *
          (φ ξ * fieldDerivative (C.Xl i.succ) a ξ)) := by
      rw [Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    calc _ = a ξ * C.errorOp η K (C.Θ η ξ) * φ ξ +
          (2 * ∑ i : Fin q, fieldDerivative (C.Xl i.succ) a ξ *
            fieldDerivative (zField C i.succ η) K (C.Θ η ξ)) * φ ξ +
          sumSquaresWithDrift C.Xl a ξ * K (C.Θ η ξ) * φ ξ := by ring
      _ = _ := by rw [hs]; ring
  have hint : IntegrableOn (fun ξ => (a ξ * C.rightPoleError η K (C.Θ η ξ) +
        2 * ∑ i : Fin q, fieldDerivative (C.Xl i.succ) a ξ * C.zDeriv η i.succ K (C.Θ η ξ) +
        sumSquaresWithDrift C.Xl a ξ * K (C.Θ η ξ)) * φ ξ) C.U :=
    ((iE.add (integrable_finsetSum _ (fun i _ => iZ i))).add iK).congr_fun_ae hpt.symm
  refine ⟨hint, ?_⟩
  have qE : (∫ ξ in C.U, C.errorOp η K (C.Θ η ξ) * (φ ξ * a ξ)) =
      ∫ u in (C.e η).target, C.errorOp η K u * alphaT C hη ha φ u := pE.2
  have qZ : ∀ i : Fin q, (∫ ξ in C.U, 2 * (fieldDerivative (zField C i.succ η) K (C.Θ η ξ) *
      (φ ξ * fieldDerivative (C.Xl i.succ) a ξ))) =
      ∫ u in (C.e η).target, 2 * (fieldDerivative (zField C i.succ η) K u *
        betaT C hη ha φ i u) := fun i => by
    have h2 : (∫ ξ in C.U, fieldDerivative (zField C i.succ η) K (C.Θ η ξ) *
        (φ ξ * fieldDerivative (C.Xl i.succ) a ξ)) =
        ∫ u in (C.e η).target, fieldDerivative (zField C i.succ η) K u * betaT C hη ha φ i u :=
      (pZ i).2
    rw [integral_const_mul, h2, integral_const_mul]
  have qK : (∫ ξ in C.U, K (C.Θ η ξ) * (φ ξ * sumSquaresWithDrift C.Xl a ξ)) =
      ∫ u in (C.e η).target, K u * lamT C hη ha φ u := pK.2
  have hS := modelTransport_eq_poleTranspose hη ha φ
  have hL : (∫ ξ in C.U, a ξ * K (C.Θ η ξ) * sumSquaresWithDriftTranspose C.Xl φ ξ) =
      ∫ u in (C.e η).target, K u * C.poleTranspose η (alphaT C hη ha φ)
        (fun i => betaT C hη ha φ i) (lamT C hη ha φ) u := by
    calc (∫ ξ in C.U, a ξ * K (C.Θ η ξ) * sumSquaresWithDriftTranspose C.Xl φ ξ)
        = ∫ ξ in C.U, K (C.Θ η ξ) * (sumSquaresWithDriftTranspose C.Xl φ ξ * a ξ) :=
          setIntegral_congr_fun hmeas (fun ξ _ => by ring)
      _ = ∫ u, K u * C.modelTransport η
            (fun ξ => sumSquaresWithDriftTranspose C.Xl φ ξ * a ξ) u :=
          integral_comp_theta_mul hη _ _
      _ = ∫ u in (C.e η).target, K u * C.modelTransport η
            (fun ξ => sumSquaresWithDriftTranspose C.Xl φ ξ * a ξ) u :=
          (setIntegral_eq_integral_of_forall_compl_eq_zero
            (fun u hu => by simp [modelTransport_of_notMem hu])).symm
      _ = ∫ u in (C.e η).target, K u * C.poleTranspose η (alphaT C hη ha φ)
            (fun i => betaT C hη ha φ i) (lamT C hη ha φ) u :=
          setIntegral_congr_fun (C.e η).open_target.measurableSet
            (fun u hu => by rw [hS u hu])
  have iZs : IntegrableOn (fun ξ => ∑ i : Fin q, 2 * (fieldDerivative (zField C i.succ η) K
      (C.Θ η ξ) * (φ ξ * fieldDerivative (C.Xl i.succ) a ξ))) C.U :=
    integrable_finsetSum _ (fun i _ => iZ i)
  have iEZ : IntegrableOn (fun ξ => C.errorOp η K (C.Θ η ξ) * (φ ξ * a ξ) +
      ∑ i : Fin q, 2 * (fieldDerivative (zField C i.succ η) K
      (C.Θ η ξ) * (φ ξ * fieldDerivative (C.Xl i.succ) a ξ))) C.U := iE.add iZs
  rw [hL, integral_kernel_mul_poleTranspose hq ν₀ K hη, alphaT_zero hη ha φ,
    integral_congr_ae hpt, integral_add iEZ iK, integral_add iE iZs,
    integral_finsetSum _ (fun i _ => iZ i), qE, qK]
  simp only [qZ]
  ring

end LiftedChart

end RothschildStein.P1
