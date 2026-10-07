-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.LeftParametrixNoDriftPairing

/-!
# The pole limit without drift: the pole of the left parametrix contributes `a(η) φ(η)`

The no-drift counterpart of `LeftParametrixPole`. The left pole `Γ*(Θ(η, ξ))` tested in `ξ` against
`L̃φ` (`L̃ = ∑ᵢ X̃ᵢ²`, `sumSquares C.Xl`), with an output cutoff `a` (the pole computation, left
parametrix; BB pp. 560–563). Substituting `u = Θ(η, ξ)` (`LiftedChart.modelTransport`) and testing
against smooth compactly supported `g` of the model variable gives `∫ g · S = ∫ g · T*(α, β, λ)`
with `S` the transported `a L̃φ` and `α = (aφ)~`, `βᵢ = ((a dᵢ + X̃ᵢ a) φ)~`, `λ = ((L̃* a) φ)~`;
hence `S = T*(α, β, λ)` (`modelTransport_eq_leftPoleTransposeNoDrift`). For the fundamental kernel
`Γ*` of `𝓛* = 𝓛 = ∑ Yᵢ²` (no drift) one has `∫ Γ* 𝓛ᵀα = α(0) = c(η) a(η) φ(η)`, and the remaining
terms are the absolutely convergent errors:
`integral_kernel_comp_theta_mul_sumSquares_noDrift`. With `a ≡ 1` this is the pole limit
`∫ Γ*(Θ) L̃ψ = c(η) ψ(η) + ∫ (E_η Γ*)(Θ) ψ` with the divergence terms of the no-drift formal adjoint
(`integral_kernel_comp_theta_sumSquares_noDrift`).
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
  {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart (fun _ : Fin q => (1 : ℕ+)) s Ω hΩ X x₀ m}

/-- The pointwise form of the output product formula against a value `t` of the
test: `φ(ξ) · L̃*(a (g ∘ Θ η))(ξ)` splits into the model, error, first-order and zeroth-order
terms. -/
theorem sumSquaresTranspose_mul_comp_theta_mul_noDrift {η ξ : Fin (n + m) → ℝ} (hη : η ∈ C.U)
    (hξ : ξ ∈ C.U) {a g : (Fin (n + m) → ℝ) → ℝ} (ha : ContDiffOn ℝ (⊤ : ℕ∞) a C.U)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g (C.e η).target) (t : ℝ) :
    t * sumSquaresTranspose C.Xl (fun ξ' => a ξ' * g (C.Θ η ξ')) ξ =
      sumSquares C.Y g (C.Θ η ξ) * (t * a ξ) + C.errorOpNoDrift η g (C.Θ η ξ) * (t * a ξ) +
      ∑ i : Fin q, 2 * (fieldDerivative (zField C i η) g (C.Θ η ξ) *
        (t * C.leftBetaCoeffNoDrift a i ξ)) +
      g (C.Θ η ξ) * (t * sumSquaresTranspose C.Xl a ξ) := by
  have hmem := C.theta_mem_target hη hξ
  have h1 := C.sumSquaresTranspose_mul_comp_theta_noDrift hη (C.e η).open_target hg ha hξ hmem
  rw [h1, C.rightPoleErrorNoDrift_eq_errorOp hη (C.e η).open_target hg hmem hmem]
  have hz : ∀ i : Fin q, C.zDeriv η i g (C.Θ η ξ) =
      fieldDerivative (zField C i η) g (C.Θ η ξ) := fun i => by
    rw [zDeriv_eq_fieldDerivative_noDrift]
  simp only [hz, leftBetaCoeffNoDrift]
  have hs : t * (2 * ∑ i : Fin q, (a ξ * Hormander.Interface.euclideanDivergence (C.Xl i) ξ +
      fieldDerivative (C.Xl i) a ξ) * fieldDerivative (zField C i η) g (C.Θ η ξ)) =
      ∑ i : Fin q, 2 * (fieldDerivative (zField C i η) g (C.Θ η ξ) *
        (t * (a ξ * Hormander.Interface.euclideanDivergence (C.Xl i) ξ +
          fieldDerivative (C.Xl i) a ξ))) := by
    rw [Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)
  calc _ = t * (a ξ * (sumSquares C.Y g (C.Θ η ξ) + C.errorOpNoDrift η g (C.Θ η ξ))) +
        t * (2 * ∑ i : Fin q, (a ξ * Hormander.Interface.euclideanDivergence (C.Xl i) ξ +
          fieldDerivative (C.Xl i) a ξ) * fieldDerivative (zField C i η) g (C.Θ η ξ)) +
        t * (sumSquaresTranspose C.Xl a ξ * g (C.Θ η ξ)) := by ring
    _ = _ := by rw [hs]; ring

/-- Transport of the operator to the model, for test functions: for `η ∈ C.U`, a
test `φ` on `C.U`, `a` smooth on `C.U` and a test function `g` of the model variable,
`∫_U g(Θ η ξ) (L̃φ)(ξ) a(ξ) dξ = ∫ g T*(α, β, λ)` (duality for `L̃` against the pullback test
function `a (g∘Θ η)`, the no-drift formal adjoint formula via the chain rule, and the substitution
`u = Θ η ξ`). -/
theorem integral_comp_theta_mul_sumSquares_test_noDrift {η : Fin (n + m) → ℝ} (hη : η ∈ C.U)
    {a : (Fin (n + m) → ℝ) → ℝ} (ha : ContDiffOn ℝ (⊤ : ℕ∞) a C.U)
    (φ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞))
    (g : TestFunction (C.modelOpens η) ℝ (⊤ : ℕ∞)) :
    (∫ ξ in C.U, g (C.Θ η ξ) * (sumSquares C.Xl φ ξ * a ξ)) =
      ∫ u in (C.e η).target, g u * C.poleTransposeNoDrift η (alphaTNoDrift C hη ha φ)
        (fun i => betaLNoDrift C hη ha φ i) (lamLNoDrift C hη ha φ) u := by
  have hmeas : MeasurableSet C.U := C.isOpen_U.measurableSet
  have hg : ContDiffOn ℝ (⊤ : ℕ∞) g (C.e η).target := g.contDiff.contDiffOn
  have hYs : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (C.Y i) ((C.modelOpens η : Opens (Fin (n + m) → ℝ)) :
      Set (Fin (n + m) → ℝ)) := fun i => (C.model_field_smooth i).contDiffOn
  set h : TestFunction C.chartOpens ℝ (⊤ : ℕ∞) := pullbackTestNoDrift hη ha g with hh
  have hdual := C.integral_sumSquares_mul_test_U_noDrift (φ : (Fin (n + m) → ℝ) → ℝ)
    φ.contDiff.contDiffOn h
  -- the pointwise computation of `L̃* h` on `C.U`
  have hpt : ∀ ξ ∈ C.U, φ ξ * sumSquaresTranspose C.Xl h ξ =
      sumSquares C.Y g (C.Θ η ξ) * (φ ξ * a ξ) + C.errorOpNoDrift η g (C.Θ η ξ) * (φ ξ * a ξ) +
        ∑ i : Fin q, 2 * (fieldDerivative (zField C i η) g (C.Θ η ξ) *
          (φ ξ * C.leftBetaCoeffNoDrift a i ξ)) +
        g (C.Θ η ξ) * (φ ξ * sumSquaresTranspose C.Xl a ξ) := by
    intro ξ hξ
    have hev : (h : (Fin (n + m) → ℝ) → ℝ) =ᶠ[𝓝 ξ] fun ξ' => a ξ' * g (C.Θ η ξ') :=
      Filter.eventuallyEq_of_mem (C.isOpen_U.mem_nhds hξ)
        (fun y hy => pullbackTestNoDrift_apply hη ha g hy)
    rw [sumSquaresTranspose_congr_of_eventuallyEq C.Xl hev]
    exact sumSquaresTranspose_mul_comp_theta_mul_noDrift hη hξ ha hg (φ ξ)
  have hLHS : (∫ ξ in C.U, g (C.Θ η ξ) * (sumSquares C.Xl φ ξ * a ξ)) =
      ∫ ξ in C.U, φ ξ * sumSquaresTranspose C.Xl h ξ := by
    refine Eq.trans ?_ hdual
    refine setIntegral_congr_fun hmeas (fun ξ hξ => ?_)
    show _ = sumSquares C.Xl φ ξ * h ξ
    rw [hh, pullbackTestNoDrift_apply hη ha g hξ]
    ring
  rw [hLHS, setIntegral_congr_fun hmeas hpt, integral_smooth_mul_poleTransposeNoDrift hη hg]
  -- the transported pieces
  have pL := integrableOn_integral_comp_theta_mul_smooth_noDrift hη
    (contDiffOn_sumSquares_noDrift (C.modelOpens η) C.Y hYs hg)
    (testMultiplierOn C.chartOpens a ha φ)
  have pE := integrableOn_integral_comp_theta_mul_smooth_noDrift hη
    (contDiffOn_errorOp_noDrift hη hg) (testMultiplierOn C.chartOpens a ha φ)
  have pZ : ∀ i : Fin q, _ := fun i => integrableOn_integral_comp_theta_mul_smooth_noDrift hη
    (S.contDiffOn_fieldDerivative (C.modelOpens η) (zField C i η) g
      (contDiffOn_zField_noDrift hη i) hg)
    (testMultiplierOn C.chartOpens (C.leftBetaCoeffNoDrift a i)
      (contDiffOn_leftBetaCoeffNoDrift ha i) φ)
  have pG := integrableOn_integral_comp_theta_mul_smooth_noDrift hη hg
    (testMultiplierOn C.chartOpens (sumSquaresTranspose C.Xl a)
      (contDiffOn_sumSquaresTranspose_XlNoDrift ha) φ)
  have iL : IntegrableOn (fun ξ => sumSquares C.Y g (C.Θ η ξ) * (φ ξ * a ξ)) C.U := pL.1
  have iE : IntegrableOn (fun ξ => C.errorOpNoDrift η g (C.Θ η ξ) * (φ ξ * a ξ)) C.U := pE.1
  have iZ : ∀ i : Fin q, IntegrableOn (fun ξ => 2 * (fieldDerivative (zField C i η) g
      (C.Θ η ξ) * (φ ξ * C.leftBetaCoeffNoDrift a i ξ))) C.U := fun i => (pZ i).1.const_mul 2
  have iG : IntegrableOn (fun ξ => g (C.Θ η ξ) * (φ ξ * sumSquaresTranspose C.Xl a ξ)) C.U :=
    pG.1
  have iLE : IntegrableOn (fun ξ => sumSquares C.Y g (C.Θ η ξ) * (φ ξ * a ξ) +
      C.errorOpNoDrift η g (C.Θ η ξ) * (φ ξ * a ξ)) C.U := iL.add iE
  have iZs : IntegrableOn (fun ξ => ∑ i : Fin q, 2 * (fieldDerivative (zField C i η) g
      (C.Θ η ξ) * (φ ξ * C.leftBetaCoeffNoDrift a i ξ))) C.U :=
    integrable_finsetSum _ (fun i _ => iZ i)
  have iLEZ : IntegrableOn (fun ξ => sumSquares C.Y g (C.Θ η ξ) * (φ ξ * a ξ) +
      C.errorOpNoDrift η g (C.Θ η ξ) * (φ ξ * a ξ) + ∑ i : Fin q, 2 * (fieldDerivative
        (zField C i η) g (C.Θ η ξ) * (φ ξ * C.leftBetaCoeffNoDrift a i ξ))) C.U := iLE.add iZs
  have qL : (∫ ξ in C.U, sumSquares C.Y g (C.Θ η ξ) * (φ ξ * a ξ)) =
      ∫ u in (C.e η).target, sumSquares C.Y g u * alphaTNoDrift C hη ha φ u := pL.2
  have qE : (∫ ξ in C.U, C.errorOpNoDrift η g (C.Θ η ξ) * (φ ξ * a ξ)) =
      ∫ u in (C.e η).target, C.errorOpNoDrift η g u * alphaTNoDrift C hη ha φ u := pE.2
  have qZ : ∀ i : Fin q, (∫ ξ in C.U, fieldDerivative (zField C i η) g (C.Θ η ξ) *
      (φ ξ * C.leftBetaCoeffNoDrift a i ξ)) =
      ∫ u in (C.e η).target, fieldDerivative (zField C i η) g u * betaLNoDrift C hη ha φ i u :=
    fun i => (pZ i).2
  have qG : (∫ ξ in C.U, g (C.Θ η ξ) * (φ ξ * sumSquaresTranspose C.Xl a ξ)) =
      ∫ u in (C.e η).target, g u * lamLNoDrift C hη ha φ u := pG.2
  rw [integral_add iLEZ iG, integral_add iLE iZs, integral_add iL iE,
    integral_finsetSum _ (fun i _ => iZ i), qL, qE, qG]
  congr 2
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [integral_const_mul, qZ i, integral_const_mul]

/-- The transported test `(L̃φ) a` equals `T*(α, β, λ)` on the target of `e η`:
the transpose of the operator `L̃*` in the model variable (the pole computation, "the transformed test
is compactly supported"; both sides pair identically with every compactly supported smooth `g`). -/
theorem modelTransport_eq_leftPoleTransposeNoDrift {η : Fin (n + m) → ℝ} (hη : η ∈ C.U)
    {a : (Fin (n + m) → ℝ) → ℝ} (ha : ContDiffOn ℝ (⊤ : ℕ∞) a C.U)
    (φ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞)) :
    ∀ u ∈ (C.e η).target,
      C.modelTransport η (fun ξ => sumSquares C.Xl φ ξ * a ξ) u =
        C.poleTransposeNoDrift η (alphaTNoDrift C hη ha φ)
          (fun i => betaLNoDrift C hη ha φ i) (lamLNoDrift C hη ha φ) u := by
  set S' := C.modelTransport η (fun ξ => sumSquares C.Xl φ ξ * a ξ) with hS'
  set T := C.poleTransposeNoDrift η (alphaTNoDrift C hη ha φ)
    (fun i => betaLNoDrift C hη ha φ i) (lamLNoDrift C hη ha φ) with hT
  have hTc : Continuous T := continuous_poleTransposeNoDrift hη _ _ _
  have hS'c : Continuous S' := by
    let LφT : TestFunction C.chartOpens ℝ (⊤ : ℕ∞) :=
      sumSquaresTestNoDrift C.chartOpens C.Xl C.contDiffOn_Xl_U φ
    let ψ' : TestFunction C.chartOpens ℝ (⊤ : ℕ∞) := testMultiplierOn C.chartOpens a ha LφT
    have hψ' : (ψ' : (Fin (n + m) → ℝ) → ℝ) = fun ξ => sumSquares C.Xl φ ξ * a ξ := by
      funext ξ
      show LφT ξ * a ξ = _
      rw [show (LφT : (Fin (n + m) → ℝ) → ℝ) = sumSquares C.Xl φ from
        sumSquaresTestNoDrift_coe C.chartOpens C.Xl C.contDiffOn_Xl_U φ]
    have e : S' = (modelTransportTest hη ψ' : (Fin (n + m) → ℝ) → ℝ) := by
      rw [hS', ← hψ']
      rfl
    rw [e]
    exact (modelTransportTest hη ψ').continuous
  have key : ∀ g : (Fin (n + m) → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) g → HasCompactSupport g →
      tsupport g ⊆ (C.e η).target → ∫ x, g x • (S' x - T x) = 0 := by
    intro g hg hcs hts
    let gT : TestFunction (C.modelOpens η) ℝ (⊤ : ℕ∞) := ⟨g, hg, hcs, hts⟩
    have h1 := integral_comp_theta_mul_sumSquares_test_noDrift hη ha φ gT
    have h2 := integral_comp_theta_mul hη g (fun ξ => sumSquares C.Xl φ ξ * a ξ)
    have h1' : (∫ ξ in C.U, g (C.Θ η ξ) * (sumSquares C.Xl φ ξ * a ξ)) =
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
for the H1 fundamental kernel `Γ*` of the reversed no-drift model, `η ∈ C.U`, `a` smooth on `C.U`
and a test `φ` on `C.U`,
`∫_U a Γ*(Θ η ξ) L̃φ(ξ) dξ = c(η) a(η) φ(η) + ∫_U (a (E_η Γ*)(Θ η ξ) +
  2 ∑ᵢ (a dᵢ + X̃ᵢ a)(ξ) (Zᵢ Γ*)(Θ η ξ) + (L̃* a)(ξ) Γ*(Θ η ξ)) φ(ξ) dξ`,
`E_η = ∑ᵢ (Yᵢ Rᵢ + Rᵢ Yᵢ + Rᵢ²)` (`rightPoleErrorNoDrift`, no drift remainder) and the integrand
on the right is integrable (BB pp. 560–563; the pole computation: the density `c(η)` is the only pole
contribution, the cutoff-shell terms vanish in the limit). -/
theorem integral_kernel_comp_theta_mul_sumSquares_noDrift (hq : 0 < q)
    (ν₀ : G2.HomogeneousNorm C.G)
    (K : H1.FundamentalKernel C.G ((C.noDriftModel hq ν₀).reverseDrift C.G))
    {η : Fin (n + m) → ℝ} (hη : η ∈ C.U) {a : (Fin (n + m) → ℝ) → ℝ}
    (ha : ContDiffOn ℝ (⊤ : ℕ∞) a C.U) (φ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞)) :
    IntegrableOn (fun ξ => C.leftErrBracketNoDrift K a η ξ * φ ξ) C.U ∧
    (∫ ξ in C.U, a ξ * K (C.Θ η ξ) * sumSquares C.Xl φ ξ) =
      C.c η * (a η * φ η) + ∫ ξ in C.U, C.leftErrBracketNoDrift K a η ξ * φ ξ := by
  have hNZ : NeZero (n + m) := ⟨C.G.dimension_pos.ne'⟩
  have hmeas : MeasurableSet C.U := C.isOpen_U.measurableSet
  have hEI := errorIbp_kernel_noDrift K hη
  -- the transported pieces
  have pE := integrableOn_integral_comp_theta_mul hη (F := C.errorOpNoDrift η K)
    (ψ := fun ξ => φ ξ * a ξ) (hEI.integrableOn_errorOp_mul (alphaTNoDrift C hη ha φ))
  have pZ : ∀ i : Fin q, _ := fun i => integrableOn_integral_comp_theta_mul hη
    (F := fieldDerivative (zField C i η) K) (ψ := fun ξ => φ ξ * C.leftBetaCoeffNoDrift a i ξ)
    ((hEI.zg i (betaLNoDrift C hη ha φ i)).1)
  have pK := integrableOn_integral_comp_theta_mul_test hη (F := (K : (Fin (n + m) → ℝ) → ℝ))
    (K.locallyIntegrable.locallyIntegrableOn _)
    (testMultiplierOn C.chartOpens (sumSquaresTranspose C.Xl a)
      (contDiffOn_sumSquaresTranspose_XlNoDrift ha) φ)
  have iE : IntegrableOn (fun ξ => C.errorOpNoDrift η K (C.Θ η ξ) * (φ ξ * a ξ)) C.U := pE.1
  have iZ : ∀ i : Fin q, IntegrableOn (fun ξ => 2 * (fieldDerivative (zField C i η) K
      (C.Θ η ξ) * (φ ξ * C.leftBetaCoeffNoDrift a i ξ))) C.U := fun i => (pZ i).1.const_mul 2
  have iK : IntegrableOn (fun ξ => K (C.Θ η ξ) * (φ ξ * sumSquaresTranspose C.Xl a ξ)) C.U :=
    pK.1
  -- a.e. identification of the integrand
  have h0 : ∀ᵐ ξ ∂(volume : Measure (Fin (n + m) → ℝ)), ξ ≠ η := by
    have : ({η} : Set (Fin (n + m) → ℝ))ᶜ ∈ ae (volume : Measure (Fin (n + m) → ℝ)) := by
      rw [compl_mem_ae_iff]
      simp
    exact this
  have hpt : (fun ξ => C.leftErrBracketNoDrift K a η ξ * φ ξ) =ᵐ[volume.restrict C.U]
      fun ξ => C.errorOpNoDrift η K (C.Θ η ξ) * (φ ξ * a ξ) +
        ∑ i : Fin q, 2 * (fieldDerivative (zField C i η) K (C.Θ η ξ) *
          (φ ξ * C.leftBetaCoeffNoDrift a i ξ)) +
        K (C.Θ η ξ) * (φ ξ * sumSquaresTranspose C.Xl a ξ) := by
    filter_upwards [(ae_restrict_iff' hmeas).2 (Filter.Eventually.of_forall fun ξ hξ => hξ),
      ae_restrict_of_ae h0] with ξ hξ hne
    have hΘ : C.Θ η ξ ≠ 0 := C.theta_ne_zero hη hξ hne
    have hE := C.rightPoleErrorNoDrift_eq_errorOp hη
      (isOpen_compl_singleton (x := (0 : Fin (n + m) → ℝ))) K.smooth_off_zero hΘ
      (C.theta_mem_target hη hξ)
    have hz : ∀ i : Fin q, C.zDeriv η i K (C.Θ η ξ) =
        fieldDerivative (zField C i η) K (C.Θ η ξ) := fun i => by
      rw [zDeriv_eq_fieldDerivative_noDrift]
    simp only [leftErrBracketNoDrift, hz, hE]
    have hs : (2 * ∑ i : Fin q, C.leftBetaCoeffNoDrift a i ξ *
        fieldDerivative (zField C i η) K (C.Θ η ξ)) * φ ξ =
        ∑ i : Fin q, 2 * (fieldDerivative (zField C i η) K (C.Θ η ξ) *
          (φ ξ * C.leftBetaCoeffNoDrift a i ξ)) := by
      rw [Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    calc _ = a ξ * C.errorOpNoDrift η K (C.Θ η ξ) * φ ξ +
          (2 * ∑ i : Fin q, C.leftBetaCoeffNoDrift a i ξ *
            fieldDerivative (zField C i η) K (C.Θ η ξ)) * φ ξ +
          sumSquaresTranspose C.Xl a ξ * K (C.Θ η ξ) * φ ξ := by ring
      _ = _ := by rw [hs]; ring
  have hint : IntegrableOn (fun ξ => C.leftErrBracketNoDrift K a η ξ * φ ξ) C.U :=
    ((iE.add (integrable_finsetSum _ (fun i _ => iZ i))).add iK).congr_fun_ae hpt.symm
  refine ⟨hint, ?_⟩
  have qE : (∫ ξ in C.U, C.errorOpNoDrift η K (C.Θ η ξ) * (φ ξ * a ξ)) =
      ∫ u in (C.e η).target, C.errorOpNoDrift η K u * alphaTNoDrift C hη ha φ u := pE.2
  have qZ : ∀ i : Fin q, (∫ ξ in C.U, 2 * (fieldDerivative (zField C i η) K (C.Θ η ξ) *
      (φ ξ * C.leftBetaCoeffNoDrift a i ξ))) =
      ∫ u in (C.e η).target, 2 * (fieldDerivative (zField C i η) K u *
        betaLNoDrift C hη ha φ i u) := fun i => by
    have h2 : (∫ ξ in C.U, fieldDerivative (zField C i η) K (C.Θ η ξ) *
        (φ ξ * C.leftBetaCoeffNoDrift a i ξ)) =
        ∫ u in (C.e η).target, fieldDerivative (zField C i η) K u *
          betaLNoDrift C hη ha φ i u :=
      (pZ i).2
    rw [integral_const_mul, h2, integral_const_mul]
  have qK : (∫ ξ in C.U, K (C.Θ η ξ) * (φ ξ * sumSquaresTranspose C.Xl a ξ)) =
      ∫ u in (C.e η).target, K u * lamLNoDrift C hη ha φ u := pK.2
  have hS := modelTransport_eq_leftPoleTransposeNoDrift hη ha φ
  have hL : (∫ ξ in C.U, a ξ * K (C.Θ η ξ) * sumSquares C.Xl φ ξ) =
      ∫ u in (C.e η).target, K u * C.poleTransposeNoDrift η (alphaTNoDrift C hη ha φ)
        (fun i => betaLNoDrift C hη ha φ i) (lamLNoDrift C hη ha φ) u := by
    calc (∫ ξ in C.U, a ξ * K (C.Θ η ξ) * sumSquares C.Xl φ ξ)
        = ∫ ξ in C.U, K (C.Θ η ξ) * (sumSquares C.Xl φ ξ * a ξ) :=
          setIntegral_congr_fun hmeas (fun ξ _ => by ring)
      _ = ∫ u, K u * C.modelTransport η (fun ξ => sumSquares C.Xl φ ξ * a ξ) u :=
          integral_comp_theta_mul hη _ _
      _ = ∫ u in (C.e η).target, K u * C.modelTransport η
            (fun ξ => sumSquares C.Xl φ ξ * a ξ) u :=
          (setIntegral_eq_integral_of_forall_compl_eq_zero
            (fun u hu => by simp [modelTransport_of_notMem hu])).symm
      _ = ∫ u in (C.e η).target, K u * C.poleTransposeNoDrift η (alphaTNoDrift C hη ha φ)
            (fun i => betaLNoDrift C hη ha φ i) (lamLNoDrift C hη ha φ) u :=
          setIntegral_congr_fun (C.e η).open_target.measurableSet
            (fun u hu => by rw [hS u hu])
  have iZs : IntegrableOn (fun ξ => ∑ i : Fin q, 2 * (fieldDerivative (zField C i η) K
      (C.Θ η ξ) * (φ ξ * C.leftBetaCoeffNoDrift a i ξ))) C.U :=
    integrable_finsetSum _ (fun i _ => iZ i)
  have iEZ : IntegrableOn (fun ξ => C.errorOpNoDrift η K (C.Θ η ξ) * (φ ξ * a ξ) +
      ∑ i : Fin q, 2 * (fieldDerivative (zField C i η) K
      (C.Θ η ξ) * (φ ξ * C.leftBetaCoeffNoDrift a i ξ))) C.U := iE.add iZs
  rw [hL, integral_kernel_mul_leftPoleTransposeNoDrift K hη, alphaTNoDrift_zero hη ha φ,
    integral_congr_ae hpt, integral_add iEZ iK, integral_add iE iZs,
    integral_finsetSum _ (fun i _ => iZ i), qE, qK]
  simp only [qZ]
  ring

end LiftedChart

end RothschildStein.P1
