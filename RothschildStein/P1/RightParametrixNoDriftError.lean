-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.RightParametrixError

/-!
# The error operator, without drift, of the right pole computation and its transpose

The no-drift counterpart of `RightParametrixError`. For a no-drift chart (alphabet `Fin q`, all
weights one, operator `L̃ = ∑ᵢ X̃ᵢ²` given by `sumSquares C.Xl`), `η ∈ C.U`, the error of the right pole formula
(`LiftedChart.rightPoleErrorNoDrift`) is rewritten in the composite form

`E g = ∑ᵢ (Yᵢ(Rᵢ g) + Rᵢ(Zᵢ g))`,  `Zᵢ = Yᵢ + Rᵢ`,  `Rᵢ = R_{[i],η}`

(`LiftedChart.errorOpNoDrift`, `rightPoleErrorNoDrift_eq_errorOp`), with transpose
`Eᵀ φ = ∑ᵢ (Rᵢᵀ(Yᵢᵀ φ) + Zᵢᵀ(Rᵢᵀ φ))` (`LiftedChart.errorTransposeNoDrift`). `ErrorIbpNoDrift η g`
collects the four first-order integration-by-parts pairs, and then `∫ (E g) φ = ∫ g (Eᵀ φ)`
(`ErrorIbpNoDrift.integral_errorOp_mul`). It holds for smooth `g` (`errorIbpNoDrift_of_smooth`) and,
by the cutoff-shell estimate (the remainder fields improve the weight by one), for
the H1 fundamental kernel `Γ` of the no-drift model (`errorIbp_kernel_noDrift`).

The model of a no-drift chart is `C.noDriftModel hq ν₀` with the zero drift `Fin.cons 0 C.Y`: the
zero field acts as `0` (`fieldDerivative_zero_field`, `fieldTranspose_zero_field`), so the H1
operators of the model are the no-drift ones (`sumSquaresWithDrift_cons_zero`,
`sumSquaresWithDriftTranspose_cons_zero`), the kernel is annihilated by `∑ᵢ Yᵢ²` off the origin
(`sumSquares_kernel_eq_zero_noDrift`) and has `∫ K · ∑ᵢ (Yᵢᵀ)² φ = φ(0)`
(`integral_kernel_mul_transpose_noDrift`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology
open RothschildStein.P2
namespace RothschildStein.P1

section ZeroDrift

variable {N q : ℕ}

/-- The derivative along the zero field vanishes. -/
theorem fieldDerivative_zero_field (f : (Fin N → ℝ) → ℝ) :
    fieldDerivative (0 : (Fin N → ℝ) → (Fin N → ℝ)) f = 0 := by
  funext x
  simp [fieldDerivative]

/-- The transpose of the zero field vanishes. -/
theorem fieldTranspose_zero_field (φ : (Fin N → ℝ) → ℝ) :
    fieldTranspose (0 : (Fin N → ℝ) → (Fin N → ℝ)) φ = 0 := by
  funext x
  simp [fieldTranspose, Hormander.Interface.euclideanDivergence]

/-- With the zero drift `Fin.cons 0 Y`, the operator with drift is
the no-drift operator `∑ᵢ Yᵢ²`. -/
theorem sumSquaresWithDrift_cons_zero (Y : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (f : (Fin N → ℝ) → ℝ) (x : Fin N → ℝ) :
    sumSquaresWithDrift (Fin.cons (0 : (Fin N → ℝ) → (Fin N → ℝ)) Y :
      Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ)) f x = sumSquares Y f x := by
  simp [sumSquaresWithDrift, sumSquares, fieldDerivative_zero_field]

/-- With the zero drift `Fin.cons 0 Y`, the transpose of the
operator with drift is the no-drift transpose `∑ᵢ (Yᵢᵀ)²`. -/
theorem sumSquaresWithDriftTranspose_cons_zero (Y : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (φ : (Fin N → ℝ) → ℝ) (x : Fin N → ℝ) :
    sumSquaresWithDriftTranspose (Fin.cons (0 : (Fin N → ℝ) → (Fin N → ℝ)) Y :
      Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ)) φ x = sumSquaresTranspose Y φ x := by
  simp [sumSquaresWithDriftTranspose, sumSquaresTranspose, fieldTranspose_zero_field]

/-- The no-drift transpose does not enlarge supports (as for the drift transpose, via
the zero-drift extension). -/
theorem tsupport_sumSquaresTranspose_subset_noDrift (Y : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (f : (Fin N → ℝ) → ℝ) : tsupport (sumSquaresTranspose Y f) ⊆ tsupport f := by
  have h : sumSquaresTranspose Y f = sumSquaresWithDriftTranspose
      (Fin.cons (0 : (Fin N → ℝ) → (Fin N → ℝ)) Y :
        Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ)) f :=
    funext fun x => (sumSquaresWithDriftTranspose_cons_zero Y f x).symm
  rw [h]
  exact H1.tsupport_sumSquaresTranspose_subset _ f

end ZeroDrift

namespace LiftedChart

section Model

variable {n q s m : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart (fun _ : Fin q => (1 : ℕ+)) s Ω hΩ X x₀ m}

/-- The H1 fundamental kernel of the no-drift model is annihilated by
`𝓛 = ∑ᵢ Yᵢ²` off the origin (the pointwise form of `𝓛 K = δ₀`; BB Thm 11.5(a), Thm 6.18, p. 264). -/
theorem sumSquares_kernel_eq_zero_noDrift {hq : 0 < q} {ν₀ : G2.HomogeneousNorm C.G}
    (K : H1.FundamentalKernel C.G (C.noDriftModel hq ν₀)) {x : Fin (n + m) → ℝ} (hx : x ≠ 0) :
    sumSquares C.Y K x = 0 := by
  have h := sumSquaresWithDrift_kernel_eq_zero K hx
  rw [LiftedChart.noDriftModel_fields, sumSquaresWithDrift_cons_zero] at h
  exact h

/-- The fundamental property of the kernel of the no-drift model in
no-drift form: `∫ K · ∑ᵢ (Yᵢᵀ)² φ = φ(0)` for tests `φ`. -/
theorem integral_kernel_mul_transpose_noDrift {hq : 0 < q} {ν₀ : G2.HomogeneousNorm C.G}
    (K : H1.FundamentalKernel C.G (C.noDriftModel hq ν₀)) (φ : (Fin (n + m) → ℝ) → ℝ)
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hc : HasCompactSupport φ) :
    (∫ x, K x * sumSquaresTranspose C.Y φ x) = φ 0 := by
  have h := K.fundamental φ hφ hc
  simp only [LiftedChart.noDriftModel_fields, sumSquaresWithDriftTranspose_cons_zero] at h
  exact h

end Model

variable {n q s m : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  (C : LiftedChart (fun _ : Fin q => (1 : ℕ+)) s Ω hΩ X x₀ m)

/-- The error operator of the right pole formula, no drift, in composite form
`E g = ∑ᵢ (Yᵢ(Rᵢ g) + Rᵢ(Zᵢ g))`, `Zᵢ = Yᵢ + Rᵢ`, `Rᵢ = R_{[i],η}`. -/
def errorOpNoDrift (η : Fin (n + m) → ℝ) (g : (Fin (n + m) → ℝ) → ℝ)
    (u : Fin (n + m) → ℝ) : ℝ :=
  ∑ i : Fin q, (fieldDerivative (C.Y i) (fieldDerivative (C.R [i] η) g) u +
    fieldDerivative (C.R [i] η) (fieldDerivative (zField C i η) g) u)

/-- The transpose of the no-drift error operator,
`Eᵀ φ = ∑ᵢ (Rᵢᵀ(Yᵢᵀ φ) + Zᵢᵀ(Rᵢᵀ φ))`. -/
def errorTransposeNoDrift (η : Fin (n + m) → ℝ) (φ : (Fin (n + m) → ℝ) → ℝ)
    (u : Fin (n + m) → ℝ) : ℝ :=
  ∑ i : Fin q, (fieldTranspose (C.R [i] η) (fieldTranspose (C.Y i) φ) u +
    fieldTranspose (zField C i η) (fieldTranspose (C.R [i] η) φ) u)

variable {C}

theorem fieldDerivative_zField_noDrift (i : Fin q) (η : Fin (n + m) → ℝ)
    (g : (Fin (n + m) → ℝ) → ℝ) (u : Fin (n + m) → ℝ) :
    fieldDerivative (zField C i η) g u =
      fieldDerivative (C.Y i) g u + fieldDerivative (C.R [i] η) g u := by
  unfold fieldDerivative zField
  rw [map_add]

theorem zDeriv_eq_fieldDerivative_noDrift (η : Fin (n + m) → ℝ) (i : Fin q)
    (g : (Fin (n + m) → ℝ) → ℝ) : C.zDeriv η i g = fieldDerivative (zField C i η) g := by
  funext u
  rw [fieldDerivative_zField_noDrift]
  rfl

/-- The no-drift error of the right pole formula equals the composite error
operator on functions smooth near a point of the target of `e η`. -/
theorem rightPoleErrorNoDrift_eq_errorOp {η : Fin (n + m) → ℝ} (hη : η ∈ C.U)
    {W : Set (Fin (n + m) → ℝ)} (hW : IsOpen W) {g : (Fin (n + m) → ℝ) → ℝ}
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g W) {u : Fin (n + m) → ℝ} (huW : u ∈ W)
    (hut : u ∈ (C.e η).target) : C.rightPoleErrorNoDrift η g u = C.errorOpNoDrift η g u := by
  unfold rightPoleErrorNoDrift errorOpNoDrift
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have h2 : ContDiffAt ℝ 2 g u := (hg.contDiffAt (hW.mem_nhds huW)).of_le (by simp)
  have hY : DifferentiableAt ℝ (C.Y i) u :=
    ((C.model_field_smooth i).differentiable (by simp)).differentiableAt
  have hR : DifferentiableAt ℝ (C.R [i] η) u :=
    differentiableAt_of_contDiffOn_isOpen (C.e η).open_target (C.contDiffOn_remainder hη _) hut
  have hA := H1.differentiableAt_fieldDerivative h2 hY
  have hB := H1.differentiableAt_fieldDerivative h2 hR
  have e1 : fieldDerivative (zField C i η) g =
      fun v => fieldDerivative (C.Y i) g v + fieldDerivative (C.R [i] η) g v :=
    funext (fieldDerivative_zField_noDrift i η g)
  rw [e1, fieldDerivative_fun_add_apply hA hB]
  ring

variable (C) in
/-- The four first-order integration-by-parts pairs of the no-drift
error operator `E g = ∑ (Yᵢ(Rᵢ g) + Rᵢ(Zᵢ g))` against tests on the target of `e η`, and local
integrability of `g`. -/
structure ErrorIbpNoDrift (η : Fin (n + m) → ℝ) (g : (Fin (n + m) → ℝ) → ℝ) : Prop where
  /-- `g` is locally integrable on the target of `e η`. -/
  loc : LocallyIntegrableOn g (C.e η).target
  /-- The pair `(Yᵢ, Rᵢ g)`. -/
  yr : ∀ i : Fin q, IbpPair (C.modelOpens η) (C.Y i) (fieldDerivative (C.R [i] η) g)
  /-- The pair `(Rᵢ, g)`. -/
  rg : ∀ i : Fin q, IbpPair (C.modelOpens η) (C.R [i] η) g
  /-- The pair `(Rᵢ, Zᵢ g)`. -/
  rz : ∀ i : Fin q, IbpPair (C.modelOpens η) (C.R [i] η) (fieldDerivative (zField C i η) g)
  /-- The pair `(Zᵢ, g)`. -/
  zg : ∀ i : Fin q, IbpPair (C.modelOpens η) (zField C i η) g

theorem contDiffOn_zField_noDrift {η : Fin (n + m) → ℝ} (hη : η ∈ C.U) (i : Fin q) :
    ContDiffOn ℝ (⊤ : ℕ∞) (zField C i η) (C.e η).target :=
  (C.model_field_smooth i).contDiffOn.add (C.contDiffOn_remainder hη [i])

/-- The model fields are smooth on the open set `C.modelOpens η`. -/
theorem contDiffOn_Y_model_noDrift {η : Fin (n + m) → ℝ} (i : Fin q) :
    ContDiffOn ℝ (⊤ : ℕ∞) (C.Y i)
      ((C.modelOpens η : Opens (Fin (n + m) → ℝ)) : Set (Fin (n + m) → ℝ)) :=
  (C.model_field_smooth i).contDiffOn

/-- The remainder fields are smooth on the open set `C.modelOpens η`. -/
theorem contDiffOn_R_model_noDrift {η : Fin (n + m) → ℝ} (hη : η ∈ C.U) (I : List (Fin q)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (C.R I η)
      ((C.modelOpens η : Opens (Fin (n + m) → ℝ)) : Set (Fin (n + m) → ℝ)) :=
  C.contDiffOn_remainder hη I

/-- The fields `Zᵢ = Yᵢ + Rᵢ` are smooth on the open set `C.modelOpens η`. -/
theorem contDiffOn_zField_model_noDrift {η : Fin (n + m) → ℝ} (hη : η ∈ C.U) (i : Fin q) :
    ContDiffOn ℝ (⊤ : ℕ∞) (zField C i η)
      ((C.modelOpens η : Opens (Fin (n + m) → ℝ)) : Set (Fin (n + m) → ℝ)) :=
  contDiffOn_zField_noDrift hη i

/-- `g · ψ` is integrable on the target of `e η` for a locally integrable `g`
and a test `ψ` whose underlying function is `F`. -/
theorem integrableOn_mul_test_target_noDrift {η : Fin (n + m) → ℝ}
    {g : (Fin (n + m) → ℝ) → ℝ} (hg : LocallyIntegrableOn g (C.e η).target)
    (ψ : TestFunction (C.modelOpens η) ℝ (⊤ : ℕ∞)) {F : (Fin (n + m) → ℝ) → ℝ}
    (hF : (ψ : (Fin (n + m) → ℝ) → ℝ) = F) :
    IntegrableOn (fun u => g u * F u) (C.e η).target := by
  subst hF
  exact (S.integrable_mul_test (C.modelOpens η) hg ψ).integrableOn

/-- `∫ (E g) φ = ∫ g (Eᵀ φ)` for tests `φ` on the target of
`e η`, given the four integration-by-parts pairs of `ErrorIbpNoDrift`. -/
theorem ErrorIbpNoDrift.integral_errorOp_mul {η : Fin (n + m) → ℝ} (hη : η ∈ C.U)
    {g : (Fin (n + m) → ℝ) → ℝ} (h : ErrorIbpNoDrift C η g)
    (φ : TestFunction (C.modelOpens η) ℝ (⊤ : ℕ∞)) :
    (∫ u in (C.e η).target, C.errorOpNoDrift η g u * φ u) =
      ∫ u in (C.e η).target, g u * C.errorTransposeNoDrift η φ u := by
  -- the test functions produced by the transposes
  let φY : Fin q → TestFunction (C.modelOpens η) ℝ (⊤ : ℕ∞) := fun i =>
    fieldTransposeTest (C.modelOpens η) (C.Y i) (contDiffOn_Y_model_noDrift i) φ
  let φR : Fin q → TestFunction (C.modelOpens η) ℝ (⊤ : ℕ∞) := fun i =>
    fieldTransposeTest (C.modelOpens η) (C.R [i] η) (contDiffOn_R_model_noDrift hη _) φ
  let φRY : Fin q → TestFunction (C.modelOpens η) ℝ (⊤ : ℕ∞) := fun i =>
    fieldTransposeTest (C.modelOpens η) (C.R [i] η) (contDiffOn_R_model_noDrift hη _) (φY i)
  let φZR : Fin q → TestFunction (C.modelOpens η) ℝ (⊤ : ℕ∞) := fun i =>
    fieldTransposeTest (C.modelOpens η) (zField C i η) (contDiffOn_zField_model_noDrift hη _)
      (φR i)
  have cY : ∀ i, (φY i : (Fin (n + m) → ℝ) → ℝ) = fieldTranspose (C.Y i) φ :=
    fun i => S.fieldTransposeTest_coe _ _ _ φ
  have cR : ∀ i, (φR i : (Fin (n + m) → ℝ) → ℝ) = fieldTranspose (C.R [i] η) φ :=
    fun i => S.fieldTransposeTest_coe _ _ _ φ
  have cRY : ∀ i, (φRY i : (Fin (n + m) → ℝ) → ℝ) =
      fieldTranspose (C.R [i] η) (fieldTranspose (C.Y i) φ) := fun i => by
    rw [S.fieldTransposeTest_coe _ _ _ (φY i), cY i]
  have cZR : ∀ i, (φZR i : (Fin (n + m) → ℝ) → ℝ) =
      fieldTranspose (zField C i η) (fieldTranspose (C.R [i] η) φ) := fun i => by
    rw [S.fieldTransposeTest_coe _ _ _ (φR i), cR i]
  -- the pairings, term by term
  have p1 : ∀ i : Fin q, (∫ u in (C.e η).target,
      fieldDerivative (C.Y i) (fieldDerivative (C.R [i] η) g) u * φ u) =
      ∫ u in (C.e η).target, g u *
        fieldTranspose (C.R [i] η) (fieldTranspose (C.Y i) φ) u := by
    intro i
    have h1 := (h.yr i φ).2
    have h2 := (h.rg i (φY i)).2
    rw [cY i] at h2
    exact h1.trans h2
  have p2 : ∀ i : Fin q, (∫ u in (C.e η).target,
      fieldDerivative (C.R [i] η) (fieldDerivative (zField C i η) g) u * φ u) =
      ∫ u in (C.e η).target, g u *
        fieldTranspose (zField C i η) (fieldTranspose (C.R [i] η) φ) u := by
    intro i
    have h1 := (h.rz i φ).2
    have h2 := (h.zg i (φR i)).2
    rw [cR i] at h2
    exact h1.trans h2
  -- assemble
  have e1 : ∀ u, C.errorOpNoDrift η g u * φ u =
      ∑ i : Fin q, (fieldDerivative (C.Y i) (fieldDerivative (C.R [i] η) g) u * φ u +
        fieldDerivative (C.R [i] η) (fieldDerivative (zField C i η) g) u * φ u) := by
    intro u
    simp only [errorOpNoDrift, add_mul, Finset.sum_mul]
  have e2 : ∀ u, g u * C.errorTransposeNoDrift η φ u =
      ∑ i : Fin q, (g u * fieldTranspose (C.R [i] η) (fieldTranspose (C.Y i) φ) u +
        g u * fieldTranspose (zField C i η) (fieldTranspose (C.R [i] η) φ) u) := by
    intro u
    simp only [errorTransposeNoDrift, mul_add, Finset.mul_sum]
  have i1 : ∀ i : Fin q, IntegrableOn (fun u =>
      fieldDerivative (C.Y i) (fieldDerivative (C.R [i] η) g) u * φ u)
      (C.e η).target := fun i => (h.yr i φ).1
  have i2 : ∀ i : Fin q, IntegrableOn (fun u =>
      fieldDerivative (C.R [i] η) (fieldDerivative (zField C i η) g) u * φ u)
      (C.e η).target := fun i => (h.rz i φ).1
  have j1 : ∀ i : Fin q, IntegrableOn (fun u => g u *
      fieldTranspose (C.R [i] η) (fieldTranspose (C.Y i) φ) u) (C.e η).target :=
    fun i => integrableOn_mul_test_target_noDrift h.loc (φRY i) (cRY i)
  have j2 : ∀ i : Fin q, IntegrableOn (fun u => g u *
      fieldTranspose (zField C i η) (fieldTranspose (C.R [i] η) φ) u)
      (C.e η).target := fun i => integrableOn_mul_test_target_noDrift h.loc (φZR i) (cZR i)
  have i12 : ∀ i : Fin q, IntegrableOn (fun u => fieldDerivative (C.Y i)
      (fieldDerivative (C.R [i] η) g) u * φ u + fieldDerivative (C.R [i] η)
      (fieldDerivative (zField C i η) g) u * φ u) (C.e η).target := fun i => (i1 i).add (i2 i)
  have j12 : ∀ i : Fin q, IntegrableOn (fun u => g u * fieldTranspose (C.R [i] η)
      (fieldTranspose (C.Y i) φ) u + g u * fieldTranspose (zField C i η)
      (fieldTranspose (C.R [i] η) φ) u) (C.e η).target := fun i => (j1 i).add (j2 i)
  simp_rw [e1, e2]
  rw [integral_finsetSum _ (fun i _ => i12 i), integral_finsetSum _ (fun i _ => j12 i)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [integral_add (i1 i) (i2 i), integral_add (j1 i) (j2 i), p1 i, p2 i]

/-- The integration-by-parts pairs of a smooth function. -/
theorem errorIbpNoDrift_of_smooth {η : Fin (n + m) → ℝ} (hη : η ∈ C.U)
    {g : (Fin (n + m) → ℝ) → ℝ} (hg : ContDiffOn ℝ (⊤ : ℕ∞) g (C.e η).target) :
    ErrorIbpNoDrift C η g := by
  have hg' : ContDiffOn ℝ (⊤ : ℕ∞) g
      ((C.modelOpens η : Opens (Fin (n + m) → ℝ)) : Set (Fin (n + m) → ℝ)) := hg
  exact ⟨hg.continuousOn.locallyIntegrableOn (C.e η).open_target.measurableSet,
    fun i => ibpPair_of_smooth (C.modelOpens η) (contDiffOn_Y_model_noDrift i)
      (S.contDiffOn_fieldDerivative (C.modelOpens η) _ g (contDiffOn_R_model_noDrift hη _) hg'),
    fun i => ibpPair_of_smooth (C.modelOpens η) (contDiffOn_R_model_noDrift hη _) hg',
    fun i => ibpPair_of_smooth (C.modelOpens η) (contDiffOn_R_model_noDrift hη _)
      (S.contDiffOn_fieldDerivative (C.modelOpens η) _ g (contDiffOn_zField_model_noDrift hη i)
        hg'),
    fun i => ibpPair_of_smooth (C.modelOpens η) (contDiffOn_zField_model_noDrift hη i) hg'⟩

/-- The integration-by-parts pairs of the H1 fundamental kernel `Γ`
against the no-drift error operator: the singularity of `Γ` is absorbed because the remainder
fields improve the weight by one (`R_{[i]}` has weight `≥ 0`: the cutoff-shell terms are `O(ε)`).
No property of `Γ` beyond its smoothness off the origin, its homogeneity of
degree `2 - Q` and local integrability is used. -/
theorem errorIbp_kernel_noDrift {H : H1.StandingHypotheses C.G q} (K : H1.FundamentalKernel C.G H)
    {η : Fin (n + m) → ℝ} (hη : η ∈ C.U) :
    ErrorIbpNoDrift C η (K : (Fin (n + m) → ℝ) → ℝ) := by
  obtain ⟨P⟩ := PoleSetting.nonempty C hη
  have hKc : IsCompact ({η} : Set (Fin (n + m) → ℝ)) := isCompact_singleton
  have hKU : ({η} : Set (Fin (n + m) → ℝ)) ⊆ C.U := singleton_subset_iff.2 hη
  have hTs : ∀ η' ∈ ({η} : Set (Fin (n + m) → ℝ)), ∀ u, P.ν u ≤ P.ρ → (η', u) ∈ C.T :=
    fun η' hη' u hu => by rw [mem_singleton_iff.1 hη']; exact P.chart u hu
  have hc := chartCtx_good C P.ν {η} P.ρ_pos P.ρ_le
  set Q : ℤ := (C.G.homogeneousDimension : ℤ) with hQ
  have hOpen : IsOpen ((C.e η).target ∩ {0}ᶜ) := (C.e η).open_target.inter isOpen_compl_singleton
  let Ω' : Opens (Fin (n + m) → ℝ) := ⟨(C.e η).target ∩ {0}ᶜ, hOpen⟩
  have hKs : ContDiffOn ℝ (⊤ : ℕ∞) (K : (Fin (n + m) → ℝ) → ℝ) (Ω' : Set (Fin (n + m) → ℝ)) :=
    K.smooth_off_zero.mono inter_subset_right
  have hYs : ∀ i : Fin q, ContDiffOn ℝ (⊤ : ℕ∞) (C.Y i) (C.e η).target :=
    fun i => (C.model_field_smooth i).contDiffOn
  have hRs : ∀ I : List (Fin q), ContDiffOn ℝ (⊤ : ℕ∞) (C.R I η) (C.e η).target :=
    fun I => C.contDiffOn_remainder hη I
  have hZs : ∀ i : Fin q, ContDiffOn ℝ (⊤ : ℕ∞) (zField C i η) (C.e η).target :=
    fun i => contDiffOn_zField_noDrift hη i
  -- symbol classes
  have hΓ : ∀ kk, Sym (chartCtx C P.ν {η} P.ρ) kk (2 - Q)
      (fun _ => (K : (Fin (n + m) → ℝ) → ℝ)) :=
    fun kk => sym_kernel C K P.ν {η} P.ρ kk
  have hZY : ∀ (i : Fin q) (j : Fin (n + m)) (kk : ℕ),
      Sym (chartCtx C P.ν {η} P.ρ) kk ((C.G.weight j : ℤ) - 1) (fun _ u => C.Y i u j) :=
    fun i j kk => sym_congr_degree (by simp) (sym_modelField C P.ν {η} P.ρ i j kk)
  have hZR : ∀ (i : Fin q) (j : Fin (n + m)) (kk : ℕ),
      Sym (chartCtx C P.ν {η} P.ρ) kk ((C.G.weight j : ℤ) - 0) (fun η' u => C.R [i] η' u j) :=
    fun i j kk => sym_congr_degree (by simp)
      (sym_remainderField C P.ν hKc hKU P.ρ_pos P.ρ_le hTs i j kk)
  have hZZ : ∀ (i : Fin q) (j : Fin (n + m)) (kk : ℕ),
      Sym (chartCtx C P.ν {η} P.ρ) kk ((C.G.weight j : ℤ) - 1) (fun η' u => zField C i η' u j) :=
    fun i j kk => sym_congr_degree (by simp)
      (zField_sym C P.ν hKc hKU P.ρ_pos P.ρ_le hTs i j kk)
  have hAR : ∀ (i : Fin q) (kk : ℕ), Sym (chartCtx C P.ν {η} P.ρ) kk (2 - Q)
      (fun η' u => fieldDerivative (C.R [i] η') (K : (Fin (n + m) → ℝ) → ℝ) u) :=
    fun i kk => sym_congr_degree (by ring)
      (Sym.fieldDeriv (chartCtx C P.ν {η} P.ρ) hc (Z := fun η' u => C.R [i] η' u) (w := 0)
        (fun j k => hZR i j k) (hΓ (kk + 1)))
  have hAZ : ∀ (i : Fin q) (kk : ℕ), Sym (chartCtx C P.ν {η} P.ρ) kk (1 - Q)
      (fun η' u => fieldDerivative (zField C i η') (K : (Fin (n + m) → ℝ) → ℝ) u) :=
    fun i kk => sym_congr_degree (by ring)
      (Sym.fieldDeriv (chartCtx C P.ν {η} P.ρ) hc (Z := fun η' u => zField C i η' u) (w := 1)
        (fun j k => hZZ i j k) (hΓ (kk + 1)))
  refine ⟨K.locallyIntegrable.locallyIntegrableOn _, fun i => ?_, fun i => ?_, fun i => ?_,
    fun i => ?_⟩
  · exact ibpPair_of_sym C P.ν P.smooth P.ρ_pos P.ρ_le (Z := fun _ => C.Y i) (e := 1)
      (by norm_num) (fun j kk => hZY i j kk) (hYs i) (hAR i)
      (A := fun η' u => fieldDerivative (C.R [i] η') (K : (Fin (n + m) → ℝ) → ℝ) u)
      (d := 2 - Q) (by omega)
      (S.contDiffOn_fieldDerivative Ω' _ _ ((hRs _).mono inter_subset_left) hKs)
  · exact ibpPair_of_sym C P.ν P.smooth P.ρ_pos P.ρ_le (Z := fun η' u => C.R [i] η' u)
      (e := 0) le_rfl (fun j kk => hZR i j kk) (hRs _)
      (A := fun _ => (K : (Fin (n + m) → ℝ) → ℝ)) (d := 2 - Q) hΓ (by omega) hKs
  · exact ibpPair_of_sym C P.ν P.smooth P.ρ_pos P.ρ_le (Z := fun η' u => C.R [i] η' u)
      (e := 0) le_rfl (fun j kk => hZR i j kk) (hRs _)
      (A := fun η' u => fieldDerivative (zField C i η') (K : (Fin (n + m) → ℝ) → ℝ) u)
      (d := 1 - Q) (hAZ i) (by omega)
      (S.contDiffOn_fieldDerivative Ω' _ _ ((hZs i).mono inter_subset_left) hKs)
  · exact ibpPair_of_sym C P.ν P.smooth P.ρ_pos P.ρ_le
      (Z := fun η' u => zField C i η' u) (e := 1) (by norm_num) (fun j kk => hZZ i j kk)
      (hZs i) (A := fun _ => (K : (Fin (n + m) → ℝ) → ℝ)) (d := 2 - Q) hΓ (by omega) hKs

end LiftedChart

end RothschildStein.P1
