-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.RightParametrixBounds
public import RothschildStein.P1.RightPoleComputationKernel
public import RothschildStein.P2.CutoffsGeometry

/-!
# The error operator of the right pole computation and its transpose

For a drift chart (alphabet `Fin (q + 1)`, drift letter `0`), `η ∈ C.U`, the error of the right pole formula
(`LiftedChart.rightPoleError`) is rewritten in the composite form

`E g = ∑_{i ≥ 1} (Yᵢ(Rᵢ g) + Rᵢ(Zᵢ g)) + R₀ g`,  `Zᵢ = Yᵢ + Rᵢ`,  `Rᵢ = R_{[i],η}`

(`LiftedChart.errorOp`, `rightPoleError_eq_errorOp`), with transpose
`Eᵀ φ = ∑ᵢ (Rᵢᵀ(Yᵢᵀ φ) + Zᵢᵀ(Rᵢᵀ φ)) + R₀ᵀ φ` (`LiftedChart.errorTranspose`). `ErrorIbp η g`
collects the five first-order integration-by-parts pairs, and then
`∫ (E g) φ = ∫ g (Eᵀ φ)` (`ErrorIbp.integral_errorOp_mul`). It holds for smooth `g`
(`errorIbp_of_smooth`) and, by the cutoff-shell estimate (the remainder fields
improve the weight by one), for the H1 fundamental kernel `Γ` (`errorIbp_kernel`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology
open RothschildStein.P2
namespace RothschildStein.P1

/-- Symbol classes depend only on the value of the degree. -/
theorem sym_congr_degree {N : ℕ} {c : SymCtx N} {kk : ℕ} {d d' : ℤ}
    {A : (Fin N → ℝ) → (Fin N → ℝ) → ℝ} (h : d = d') (hA : Sym c kk d A) : Sym c kk d' A :=
  h ▸ hA

/-- The data used by the cutoff-shell estimates at a centre `η`: a smooth
homogeneous norm and a gauge radius `ρ ∈ (0, 1]` whose closed ball lies in the domain of the
remainders (`P2.exists_chart_radius`). -/
structure PoleSetting {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
    {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
    (C : LiftedChart w s Ω hΩ X x₀ m) (η : Fin (n + m) → ℝ) where
  /-- The smooth homogeneous norm. -/
  ν : G2.HomogeneousNorm C.G
  /-- Smoothness off the origin. -/
  smooth : ν.Smooth
  /-- The radius. -/
  ρ : ℝ
  /-- The radius is positive. -/
  ρ_pos : 0 < ρ
  /-- The radius is at most one. -/
  ρ_le : ρ ≤ 1
  /-- The closed gauge ball lies in the domain of the remainders. -/
  chart : ∀ u, ν u ≤ ρ → (η, u) ∈ C.T

/-- A pole setting exists at every centre of the chart. -/
theorem PoleSetting.nonempty {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
    {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
    (C : LiftedChart w s Ω hΩ X x₀ m) {η : Fin (n + m) → ℝ} (hη : η ∈ C.U) :
    Nonempty (PoleSetting C η) := by
  obtain ⟨ρ, h0, h1, hT⟩ := exists_chart_radius C (G2.smoothNorm C.G) isCompact_singleton
    (singleton_subset_iff.2 hη)
  exact ⟨⟨G2.smoothNorm C.G, G2.smoothNorm_smooth C.G, ρ, h0, h1, fun u hu => hT η rfl u hu⟩⟩

namespace LiftedChart

variable {n q s m : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  (C : LiftedChart (fun i : Fin (q + 1) => if i = 0 then (2 : ℕ+) else 1) s Ω hΩ X x₀ m)

/-- The error operator of the right pole formula in composite form
`E g = ∑_{i ≥ 1} (Yᵢ(Rᵢ g) + Rᵢ(Zᵢ g)) + R₀ g`, `Zᵢ = Yᵢ + Rᵢ`, `Rᵢ = R_{[i],η}`. -/
def errorOp (η : Fin (n + m) → ℝ) (g : (Fin (n + m) → ℝ) → ℝ) (u : Fin (n + m) → ℝ) : ℝ :=
  ∑ i : Fin q, (fieldDerivative (C.Y i.succ) (fieldDerivative (C.R [i.succ] η) g) u +
    fieldDerivative (C.R [i.succ] η) (fieldDerivative (zField C i.succ η) g) u) +
  fieldDerivative (C.R [0] η) g u

/-- The transpose of the error operator,
`Eᵀ φ = ∑ᵢ (Rᵢᵀ(Yᵢᵀ φ) + Zᵢᵀ(Rᵢᵀ φ)) + R₀ᵀ φ`. -/
def errorTranspose (η : Fin (n + m) → ℝ) (φ : (Fin (n + m) → ℝ) → ℝ) (u : Fin (n + m) → ℝ) : ℝ :=
  ∑ i : Fin q, (fieldTranspose (C.R [i.succ] η) (fieldTranspose (C.Y i.succ) φ) u +
    fieldTranspose (zField C i.succ η) (fieldTranspose (C.R [i.succ] η) φ) u) +
  fieldTranspose (C.R [0] η) φ u

variable {C}

theorem fieldDerivative_zField (i : Fin (q + 1)) (η : Fin (n + m) → ℝ)
    (g : (Fin (n + m) → ℝ) → ℝ) (u : Fin (n + m) → ℝ) :
    fieldDerivative (zField C i η) g u =
      fieldDerivative (C.Y i) g u + fieldDerivative (C.R [i] η) g u := by
  unfold fieldDerivative zField
  rw [map_add]

theorem zDeriv_eq_fieldDerivative (η : Fin (n + m) → ℝ) (i : Fin (q + 1))
    (g : (Fin (n + m) → ℝ) → ℝ) : C.zDeriv η i g = fieldDerivative (zField C i η) g := by
  funext u
  rw [fieldDerivative_zField]
  rfl

/-- The error of the right pole formula equals the composite error operator on
functions smooth near a point of the target of `e η`. -/
theorem rightPoleError_eq_errorOp {η : Fin (n + m) → ℝ} (hη : η ∈ C.U)
    {W : Set (Fin (n + m) → ℝ)} (hW : IsOpen W) {g : (Fin (n + m) → ℝ) → ℝ}
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g W) {u : Fin (n + m) → ℝ} (huW : u ∈ W)
    (hut : u ∈ (C.e η).target) : C.rightPoleError η g u = C.errorOp η g u := by
  unfold rightPoleError errorOp
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have h2 : ContDiffAt ℝ 2 g u := (hg.contDiffAt (hW.mem_nhds huW)).of_le (by simp)
  have hY : DifferentiableAt ℝ (C.Y i.succ) u :=
    ((C.model_field_smooth i.succ).differentiable (by simp)).differentiableAt
  have hR : DifferentiableAt ℝ (C.R [i.succ] η) u :=
    differentiableAt_of_contDiffOn_isOpen (C.e η).open_target (C.contDiffOn_remainder hη _) hut
  have hA := H1.differentiableAt_fieldDerivative h2 hY
  have hB := H1.differentiableAt_fieldDerivative h2 hR
  have e1 : fieldDerivative (zField C i.succ η) g =
      fun v => fieldDerivative (C.Y i.succ) g v + fieldDerivative (C.R [i.succ] η) g v :=
    funext (fieldDerivative_zField i.succ η g)
  rw [e1, fieldDerivative_fun_add_apply hA hB]
  ring

variable (C) in
/-- The five first-order integration-by-parts pairs of the error
operator `E g = ∑ (Yᵢ(Rᵢ g) + Rᵢ(Zᵢ g)) + R₀ g` against tests on the target of `e η`, and local
integrability of `g`. -/
structure ErrorIbp (η : Fin (n + m) → ℝ) (g : (Fin (n + m) → ℝ) → ℝ) : Prop where
  /-- `g` is locally integrable on the target of `e η`. -/
  loc : LocallyIntegrableOn g (C.e η).target
  /-- The pair `(Yᵢ, Rᵢ g)`. -/
  yr : ∀ i : Fin q, IbpPair (C.modelOpens η) (C.Y i.succ) (fieldDerivative (C.R [i.succ] η) g)
  /-- The pair `(Rᵢ, g)`. -/
  rg : ∀ i : Fin q, IbpPair (C.modelOpens η) (C.R [i.succ] η) g
  /-- The pair `(Rᵢ, Zᵢ g)`. -/
  rz : ∀ i : Fin q, IbpPair (C.modelOpens η) (C.R [i.succ] η)
    (fieldDerivative (zField C i.succ η) g)
  /-- The pair `(Zᵢ, g)`. -/
  zg : ∀ i : Fin q, IbpPair (C.modelOpens η) (zField C i.succ η) g
  /-- The pair `(R₀, g)`. -/
  r0 : IbpPair (C.modelOpens η) (C.R [0] η) g

theorem contDiffOn_zField {η : Fin (n + m) → ℝ} (hη : η ∈ C.U) (i : Fin (q + 1)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (zField C i η) (C.e η).target :=
  (C.model_field_smooth i).contDiffOn.add (C.contDiffOn_remainder hη [i])

/-- The model fields are smooth on the open set `C.modelOpens η`. -/
theorem contDiffOn_Y_model {η : Fin (n + m) → ℝ} (i : Fin (q + 1)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (C.Y i)
      ((C.modelOpens η : Opens (Fin (n + m) → ℝ)) : Set (Fin (n + m) → ℝ)) :=
  (C.model_field_smooth i).contDiffOn

/-- The remainder fields are smooth on the open set `C.modelOpens η`. -/
theorem contDiffOn_R_model {η : Fin (n + m) → ℝ} (hη : η ∈ C.U) (I : List (Fin (q + 1))) :
    ContDiffOn ℝ (⊤ : ℕ∞) (C.R I η)
      ((C.modelOpens η : Opens (Fin (n + m) → ℝ)) : Set (Fin (n + m) → ℝ)) :=
  C.contDiffOn_remainder hη I

/-- The fields `Zᵢ = Yᵢ + Rᵢ` are smooth on the open set `C.modelOpens η`. -/
theorem contDiffOn_zField_model {η : Fin (n + m) → ℝ} (hη : η ∈ C.U) (i : Fin (q + 1)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (zField C i η)
      ((C.modelOpens η : Opens (Fin (n + m) → ℝ)) : Set (Fin (n + m) → ℝ)) :=
  contDiffOn_zField hη i

/-- `g · ψ` is integrable on the target of `e η` for a locally integrable `g`
and a test `ψ` whose underlying function is `F`. -/
theorem integrableOn_mul_test_target {η : Fin (n + m) → ℝ} {g : (Fin (n + m) → ℝ) → ℝ}
    (hg : LocallyIntegrableOn g (C.e η).target) (ψ : TestFunction (C.modelOpens η) ℝ (⊤ : ℕ∞))
    {F : (Fin (n + m) → ℝ) → ℝ} (hF : (ψ : (Fin (n + m) → ℝ) → ℝ) = F) :
    IntegrableOn (fun u => g u * F u) (C.e η).target := by
  subst hF
  exact (S.integrable_mul_test (C.modelOpens η) hg ψ).integrableOn

/-- `∫ (E g) φ = ∫ g (Eᵀ φ)` for tests `φ` on the target of
`e η`, given the five integration-by-parts pairs of `ErrorIbp`. -/
theorem ErrorIbp.integral_errorOp_mul {η : Fin (n + m) → ℝ} (hη : η ∈ C.U)
    {g : (Fin (n + m) → ℝ) → ℝ} (h : ErrorIbp C η g) (φ : TestFunction (C.modelOpens η) ℝ (⊤ : ℕ∞)) :
    (∫ u in (C.e η).target, C.errorOp η g u * φ u) =
      ∫ u in (C.e η).target, g u * C.errorTranspose η φ u := by
  -- the test functions produced by the transposes
  let φY : Fin q → TestFunction (C.modelOpens η) ℝ (⊤ : ℕ∞) := fun i =>
    fieldTransposeTest (C.modelOpens η) (C.Y i.succ) (contDiffOn_Y_model i.succ) φ
  let φR : Fin q → TestFunction (C.modelOpens η) ℝ (⊤ : ℕ∞) := fun i =>
    fieldTransposeTest (C.modelOpens η) (C.R [i.succ] η) (contDiffOn_R_model hη _) φ
  let φRY : Fin q → TestFunction (C.modelOpens η) ℝ (⊤ : ℕ∞) := fun i =>
    fieldTransposeTest (C.modelOpens η) (C.R [i.succ] η) (contDiffOn_R_model hη _) (φY i)
  let φZR : Fin q → TestFunction (C.modelOpens η) ℝ (⊤ : ℕ∞) := fun i =>
    fieldTransposeTest (C.modelOpens η) (zField C i.succ η) (contDiffOn_zField_model hη _) (φR i)
  let φ0 : TestFunction (C.modelOpens η) ℝ (⊤ : ℕ∞) :=
    fieldTransposeTest (C.modelOpens η) (C.R [0] η) (contDiffOn_R_model hη _) φ
  have cY : ∀ i, (φY i : (Fin (n + m) → ℝ) → ℝ) = fieldTranspose (C.Y i.succ) φ :=
    fun i => S.fieldTransposeTest_coe _ _ _ φ
  have cR : ∀ i, (φR i : (Fin (n + m) → ℝ) → ℝ) = fieldTranspose (C.R [i.succ] η) φ :=
    fun i => S.fieldTransposeTest_coe _ _ _ φ
  have cRY : ∀ i, (φRY i : (Fin (n + m) → ℝ) → ℝ) =
      fieldTranspose (C.R [i.succ] η) (fieldTranspose (C.Y i.succ) φ) := fun i => by
    rw [S.fieldTransposeTest_coe _ _ _ (φY i), cY i]
  have cZR : ∀ i, (φZR i : (Fin (n + m) → ℝ) → ℝ) =
      fieldTranspose (zField C i.succ η) (fieldTranspose (C.R [i.succ] η) φ) := fun i => by
    rw [S.fieldTransposeTest_coe _ _ _ (φR i), cR i]
  have c0 : (φ0 : (Fin (n + m) → ℝ) → ℝ) = fieldTranspose (C.R [0] η) φ :=
    S.fieldTransposeTest_coe _ _ _ φ
  -- the pairings, term by term
  have p1 : ∀ i : Fin q, (∫ u in (C.e η).target,
      fieldDerivative (C.Y i.succ) (fieldDerivative (C.R [i.succ] η) g) u * φ u) =
      ∫ u in (C.e η).target, g u *
        fieldTranspose (C.R [i.succ] η) (fieldTranspose (C.Y i.succ) φ) u := by
    intro i
    have h1 := (h.yr i φ).2
    have h2 := (h.rg i (φY i)).2
    rw [cY i] at h2
    exact h1.trans h2
  have p2 : ∀ i : Fin q, (∫ u in (C.e η).target,
      fieldDerivative (C.R [i.succ] η) (fieldDerivative (zField C i.succ η) g) u * φ u) =
      ∫ u in (C.e η).target, g u *
        fieldTranspose (zField C i.succ η) (fieldTranspose (C.R [i.succ] η) φ) u := by
    intro i
    have h1 := (h.rz i φ).2
    have h2 := (h.zg i (φR i)).2
    rw [cR i] at h2
    exact h1.trans h2
  have p3 : (∫ u in (C.e η).target, fieldDerivative (C.R [0] η) g u * φ u) =
      ∫ u in (C.e η).target, g u * fieldTranspose (C.R [0] η) φ u := by
    have := (h.r0 φ).2
    exact this
  -- assemble
  have e1 : ∀ u, C.errorOp η g u * φ u =
      ∑ i : Fin q, (fieldDerivative (C.Y i.succ) (fieldDerivative (C.R [i.succ] η) g) u * φ u +
        fieldDerivative (C.R [i.succ] η) (fieldDerivative (zField C i.succ η) g) u * φ u) +
      fieldDerivative (C.R [0] η) g u * φ u := by
    intro u
    simp only [errorOp, add_mul, Finset.sum_mul]
  have e2 : ∀ u, g u * C.errorTranspose η φ u =
      ∑ i : Fin q, (g u * fieldTranspose (C.R [i.succ] η) (fieldTranspose (C.Y i.succ) φ) u +
        g u * fieldTranspose (zField C i.succ η) (fieldTranspose (C.R [i.succ] η) φ) u) +
      g u * fieldTranspose (C.R [0] η) φ u := by
    intro u
    simp only [errorTranspose, mul_add, Finset.mul_sum]
  have i1 : ∀ i : Fin q, IntegrableOn (fun u =>
      fieldDerivative (C.Y i.succ) (fieldDerivative (C.R [i.succ] η) g) u * φ u)
      (C.e η).target := fun i => (h.yr i φ).1
  have i2 : ∀ i : Fin q, IntegrableOn (fun u =>
      fieldDerivative (C.R [i.succ] η) (fieldDerivative (zField C i.succ η) g) u * φ u)
      (C.e η).target := fun i => (h.rz i φ).1
  have i3 : IntegrableOn (fun u => fieldDerivative (C.R [0] η) g u * φ u) (C.e η).target :=
    (h.r0 φ).1
  have j1 : ∀ i : Fin q, IntegrableOn (fun u => g u *
      fieldTranspose (C.R [i.succ] η) (fieldTranspose (C.Y i.succ) φ) u) (C.e η).target :=
    fun i => integrableOn_mul_test_target h.loc (φRY i) (cRY i)
  have j2 : ∀ i : Fin q, IntegrableOn (fun u => g u *
      fieldTranspose (zField C i.succ η) (fieldTranspose (C.R [i.succ] η) φ) u)
      (C.e η).target := fun i => integrableOn_mul_test_target h.loc (φZR i) (cZR i)
  have j3 : IntegrableOn (fun u => g u * fieldTranspose (C.R [0] η) φ u) (C.e η).target :=
    integrableOn_mul_test_target h.loc φ0 c0
  have hs1 : IntegrableOn (fun u => ∑ i : Fin q, (fieldDerivative (C.Y i.succ)
      (fieldDerivative (C.R [i.succ] η) g) u * φ u + fieldDerivative (C.R [i.succ] η)
      (fieldDerivative (zField C i.succ η) g) u * φ u)) (C.e η).target :=
    integrable_finsetSum _ (fun i _ => (i1 i).add (i2 i))
  have hs2 : IntegrableOn (fun u => ∑ i : Fin q, (g u * fieldTranspose (C.R [i.succ] η)
      (fieldTranspose (C.Y i.succ) φ) u + g u * fieldTranspose (zField C i.succ η)
      (fieldTranspose (C.R [i.succ] η) φ) u)) (C.e η).target :=
    integrable_finsetSum _ (fun i _ => (j1 i).add (j2 i))
  have i12 : ∀ i : Fin q, IntegrableOn (fun u => fieldDerivative (C.Y i.succ)
      (fieldDerivative (C.R [i.succ] η) g) u * φ u + fieldDerivative (C.R [i.succ] η)
      (fieldDerivative (zField C i.succ η) g) u * φ u) (C.e η).target := fun i => (i1 i).add (i2 i)
  have j12 : ∀ i : Fin q, IntegrableOn (fun u => g u * fieldTranspose (C.R [i.succ] η)
      (fieldTranspose (C.Y i.succ) φ) u + g u * fieldTranspose (zField C i.succ η)
      (fieldTranspose (C.R [i.succ] η) φ) u) (C.e η).target := fun i => (j1 i).add (j2 i)
  simp_rw [e1, e2]
  rw [integral_add hs1 i3, integral_add hs2 j3, integral_finsetSum _ (fun i _ => i12 i),
    integral_finsetSum _ (fun i _ => j12 i), p3]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [integral_add (i1 i) (i2 i), integral_add (j1 i) (j2 i), p1 i, p2 i]

/-- The integration-by-parts pairs of a smooth function. -/
theorem errorIbp_of_smooth {η : Fin (n + m) → ℝ} (hη : η ∈ C.U) {g : (Fin (n + m) → ℝ) → ℝ}
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g (C.e η).target) : ErrorIbp C η g := by
  have hg' : ContDiffOn ℝ (⊤ : ℕ∞) g
      ((C.modelOpens η : Opens (Fin (n + m) → ℝ)) : Set (Fin (n + m) → ℝ)) := hg
  exact ⟨hg.continuousOn.locallyIntegrableOn (C.e η).open_target.measurableSet,
    fun i => ibpPair_of_smooth (C.modelOpens η) (contDiffOn_Y_model i.succ)
      (S.contDiffOn_fieldDerivative (C.modelOpens η) _ g (contDiffOn_R_model hη _) hg'),
    fun i => ibpPair_of_smooth (C.modelOpens η) (contDiffOn_R_model hη _) hg',
    fun i => ibpPair_of_smooth (C.modelOpens η) (contDiffOn_R_model hη _)
      (S.contDiffOn_fieldDerivative (C.modelOpens η) _ g (contDiffOn_zField_model hη i.succ) hg'),
    fun i => ibpPair_of_smooth (C.modelOpens η) (contDiffOn_zField_model hη i.succ) hg',
    ibpPair_of_smooth (C.modelOpens η) (contDiffOn_R_model hη _) hg'⟩

/-- The integration-by-parts pairs of the H1 fundamental kernel
`Γ` against the error operator: the singularity of `Γ` is absorbed because the remainder fields
improve the weight by one (`R_{[i]}` has weight `≥ 0`, `R_{[0]}` weight `≥ -1`: the cutoff-shell
terms are `O(ε)`). No property of `Γ` beyond its smoothness off the origin,
its homogeneity of degree `2 - Q` and local integrability is used. -/
theorem errorIbp_kernel {H : H1.StandingHypotheses C.G q} (K : H1.FundamentalKernel C.G H)
    {η : Fin (n + m) → ℝ} (hη : η ∈ C.U) : ErrorIbp C η (K : (Fin (n + m) → ℝ) → ℝ) := by
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
  have hYs : ∀ i : Fin q, ContDiffOn ℝ (⊤ : ℕ∞) (C.Y i.succ) (C.e η).target :=
    fun i => (C.model_field_smooth i.succ).contDiffOn
  have hRs : ∀ I : List (Fin (q + 1)), ContDiffOn ℝ (⊤ : ℕ∞) (C.R I η) (C.e η).target :=
    fun I => C.contDiffOn_remainder hη I
  have hZs : ∀ i : Fin q, ContDiffOn ℝ (⊤ : ℕ∞) (zField C i.succ η) (C.e η).target :=
    fun i => contDiffOn_zField hη i.succ
  -- symbol classes
  have hΓ : ∀ kk, Sym (chartCtx C P.ν {η} P.ρ) kk (2 - Q) (fun _ => (K : (Fin (n + m) → ℝ) → ℝ)) :=
    fun kk => sym_kernel C K P.ν {η} P.ρ kk
  have hZY : ∀ (i : Fin q) (j : Fin (n + m)) (kk : ℕ),
      Sym (chartCtx C P.ν {η} P.ρ) kk ((C.G.weight j : ℤ) - 1) (fun _ u => C.Y i.succ u j) :=
    fun i j kk => sym_congr_degree (by simp [Fin.succ_ne_zero])
      (sym_modelField C P.ν {η} P.ρ i.succ j kk)
  have hZR : ∀ (i : Fin q) (j : Fin (n + m)) (kk : ℕ),
      Sym (chartCtx C P.ν {η} P.ρ) kk ((C.G.weight j : ℤ) - 0) (fun η' u => C.R [i.succ] η' u j) :=
    fun i j kk => sym_congr_degree (by simp [Fin.succ_ne_zero])
      (sym_remainderField C P.ν hKc hKU P.ρ_pos P.ρ_le hTs i.succ j kk)
  have hZZ : ∀ (i : Fin q) (j : Fin (n + m)) (kk : ℕ),
      Sym (chartCtx C P.ν {η} P.ρ) kk ((C.G.weight j : ℤ) - 1) (fun η' u => zField C i.succ η' u j) :=
    fun i j kk => sym_congr_degree (by simp [Fin.succ_ne_zero])
      (zField_sym C P.ν hKc hKU P.ρ_pos P.ρ_le hTs i.succ j kk)
  have hZR0 : ∀ (j : Fin (n + m)) (kk : ℕ),
      Sym (chartCtx C P.ν {η} P.ρ) kk ((C.G.weight j : ℤ) - 1) (fun η' u => C.R [0] η' u j) :=
    fun j kk => sym_congr_degree (by simp)
      (sym_remainderField C P.ν hKc hKU P.ρ_pos P.ρ_le hTs 0 j kk)
  have hAR : ∀ (i : Fin q) (kk : ℕ), Sym (chartCtx C P.ν {η} P.ρ) kk (2 - Q)
      (fun η' u => fieldDerivative (C.R [i.succ] η') (K : (Fin (n + m) → ℝ) → ℝ) u) :=
    fun i kk => sym_congr_degree (by ring)
      (Sym.fieldDeriv (chartCtx C P.ν {η} P.ρ) hc (Z := fun η' u => C.R [i.succ] η' u) (w := 0)
        (fun j k => hZR i j k) (hΓ (kk + 1)))
  have hAZ : ∀ (i : Fin q) (kk : ℕ), Sym (chartCtx C P.ν {η} P.ρ) kk (1 - Q)
      (fun η' u => fieldDerivative (zField C i.succ η') (K : (Fin (n + m) → ℝ) → ℝ) u) :=
    fun i kk => sym_congr_degree (by ring)
      (Sym.fieldDeriv (chartCtx C P.ν {η} P.ρ) hc (Z := fun η' u => zField C i.succ η' u) (w := 1)
        (fun j k => hZZ i j k) (hΓ (kk + 1)))
  refine ⟨K.locallyIntegrable.locallyIntegrableOn _, fun i => ?_, fun i => ?_, fun i => ?_,
    fun i => ?_, ?_⟩
  · exact ibpPair_of_sym C P.ν P.smooth P.ρ_pos P.ρ_le (Z := fun _ => C.Y i.succ) (e := 1)
      (by norm_num) (fun j kk => hZY i j kk) (hYs i) (hAR i)
      (A := fun η' u => fieldDerivative (C.R [i.succ] η') (K : (Fin (n + m) → ℝ) → ℝ) u) (d := 2 - Q)
      (by omega)
      (S.contDiffOn_fieldDerivative Ω' _ _ ((hRs _).mono inter_subset_left) hKs)
  · exact ibpPair_of_sym C P.ν P.smooth P.ρ_pos P.ρ_le (Z := fun η' u => C.R [i.succ] η' u)
      (e := 0) le_rfl (fun j kk => hZR i j kk) (hRs _) (A := fun _ => (K : (Fin (n + m) → ℝ) → ℝ))
      (d := 2 - Q) hΓ (by omega) hKs
  · exact ibpPair_of_sym C P.ν P.smooth P.ρ_pos P.ρ_le (Z := fun η' u => C.R [i.succ] η' u)
      (e := 0) le_rfl (fun j kk => hZR i j kk) (hRs _)
      (A := fun η' u => fieldDerivative (zField C i.succ η') (K : (Fin (n + m) → ℝ) → ℝ) u)
      (d := 1 - Q) (hAZ i) (by omega)
      (S.contDiffOn_fieldDerivative Ω' _ _ ((hZs i).mono inter_subset_left) hKs)
  · exact ibpPair_of_sym C P.ν P.smooth P.ρ_pos P.ρ_le
      (Z := fun η' u => zField C i.succ η' u) (e := 1) (by norm_num) (fun j kk => hZZ i j kk)
      (hZs i) (A := fun _ => (K : (Fin (n + m) → ℝ) → ℝ)) (d := 2 - Q) hΓ (by omega) hKs
  · exact ibpPair_of_sym C P.ν P.smooth P.ρ_pos P.ρ_le (Z := fun η' u => C.R [0] η' u)
      (e := 1) (by norm_num) hZR0 (hRs _) (A := fun _ => (K : (Fin (n + m) → ℝ) → ℝ))
      (d := 2 - Q) hΓ (by omega) hKs

end LiftedChart

end RothschildStein.P1
