-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.LeftParametrixNoDriftSigned
public import RothschildStein.P1.ParametrixStatementsPrincipal

/-!
# Parametrix identity assembly, no drift: `SignedParametrixNoDrift` for the lifted frame from `ParametrixErrorTypesNoDrift`

For a lifted no-drift chart `C` (alphabet `Fin q`, all weights one, `L̃ = sumSquares C.Xl`), the H1
fundamental kernel `Γ` of its no-drift model `C.noDriftModel hq ν₀` with reflection `Γ* = Γ ∘ inv`
(a fundamental kernel of the reversed no-drift model), and a kernel frame `F` with `F.Θ = C.Θ`,
`V ⊆ C.U`, `F.Γ = Γ`, `F.Γs = Γ*` (the lifted frame; `C.IsLiftedFrame F` gives `F.Θ = C.Θ` and
`V ⊆ C.U`), the operator-level statement `SignedParametrixNoDrift F C.Xl C.c a b` follows from
`ParametrixErrorTypesNoDrift` (BB pp. 560–564, Thm 11.25, without drift). This is the no-drift
counterpart of `signedParametrix_of_errorTypes`:

* `P₁, P₂` are the single principal terms `a(ξ) Γ*(Θ(η, ξ)) (b/c)(η)` and
  `(b/c)(ξ) a(η) Γ(Θ(η, ξ))` with `D = id`, degree `0`, hence of type 2 unconditionally
  (`isTypeKernelOn_of_eq_principal`);
* `F₁, F₂` are the negated error kernels of `leftChartErrorNoDrift`, `leftChartErrorTNoDrift`, of
  type 1 by `ParametrixErrorTypesNoDrift`;
* the transposition `P₂ = P₁ᵗ` is `leftParametrixTKernelNoDrift_eq` (antisymmetry of `Θ` and
  `Γ*(u) = Γ(-u)`), and `F₂ = F₁ᵗ` holds by definition of the kernels;
* the identities follow from `integral_leftParametrix_mul_sumSquares_noDrift` and
  `leftParametrixTNoDrift_sumSquares_add_chartErrorTNoDrift` of the no-drift left parametrix,
  transferred from the chart domain `C.U` to `V` (all integrands vanish outside the supports of the
  cutoffs and tests).

`ParametrixErrorTypesNoDrift` is the type bound for the no-drift error kernel
(`LiftedChart.leftErrorKernelNoDrift`, `F₁ = -E₁`), stated exactly as `ParametrixErrorTypes`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology
open RothschildStein.P2
namespace RothschildStein.P1

section ErrorTypes

variable {n q s m : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}

/-- The types of the error terms without drift: for the H1 fundamental kernel
`Γ` of the no-drift model of a lifted chart `C`, its reflection `Γ* = Γ ∘ inv`, cutoffs
`a, b ∈ C_c^∞(V)` with `a b = a`, the explicit error kernel of `F₁ = -E₁`
(`LiftedChart.leftErrorKernelNoDrift`, so that `leftChartErrorNoDrift = -leftErrorNoDrift`) is a
type-1 kernel modeled on `Γ*` for the frame `F`, and its transpose, the kernel of `F₂ = F₁ᵗ`, is a
type-1 kernel modeled on `Γ` (BB pp. 561–563, the pole computation: local degrees at most
`1, 1, 0, 1`, hence types at least `1, 1, 2, 1`; divergence and cross-cutoff terms have type 1). -/
def ParametrixErrorTypesNoDrift
    (C : LiftedChart (fun _ : Fin q => (1 : ℕ+)) s Ω hΩ X x₀ m)
    (F : KernelFrame (n + m)) (hq : 0 < q) (ν₀ : G2.HomogeneousNorm C.G)
    (Γ : H1.FundamentalKernel C.G (C.noDriftModel hq ν₀))
    (hQ : 2 < (C.G.homogeneousDimension : ℝ)) (a b : TestFunction F.V ℝ (⊤ : ℕ∞)) : Prop :=
  (∀ ξ, a ξ * b ξ = a ξ) →
    IsTypeKernelOn F true 1 (fun ξ η => -C.leftErrorKernelNoDrift (Γ.reflection hQ) a b ξ η) ∧
    IsTypeKernelOn F false 1 (fun ξ η => -C.leftErrorKernelNoDrift (Γ.reflection hQ) a b η ξ)

end ErrorTypes

namespace LiftedChart

variable {n q s m : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart (fun _ : Fin q => (1 : ℕ+)) s Ω hΩ X x₀ m}

/-- A test function on an open subset `V ≤ C.chartOpens` of the chart domain, as a test
function on the chart domain. -/
def testOfLeNoDrift (V : Opens (Fin (n + m) → ℝ)) (hV : V ≤ C.chartOpens)
    (t : TestFunction V ℝ (⊤ : ℕ∞)) : TestFunction C.chartOpens ℝ (⊤ : ℕ∞) :=
  ⟨t, t.contDiff, t.hasCompactSupport, t.tsupport_subset.trans hV⟩

@[simp] theorem coe_testOfLeNoDrift (V : Opens (Fin (n + m) → ℝ)) (hV : V ≤ C.chartOpens)
    (t : TestFunction V ℝ (⊤ : ℕ∞)) : (testOfLeNoDrift V hV t : (Fin (n + m) → ℝ) → ℝ) = t := rfl

@[simp] theorem testOfLeNoDrift_apply (V : Opens (Fin (n + m) → ℝ)) (hV : V ≤ C.chartOpens)
    (t : TestFunction V ℝ (⊤ : ℕ∞)) (x : Fin (n + m) → ℝ) : testOfLeNoDrift V hV t x = t x := rfl

/-- The left parametrix pairing `P₁ f · g` is integrable on the chart domain
(the Fubini integrability underlying `integral_leftParametrix_mul_test_noDrift`). -/
theorem integrableOn_leftParametrixNoDrift_mul_test (hq : 0 < q) (ν₀ : G2.HomogeneousNorm C.G)
    (K : H1.FundamentalKernel C.G ((C.noDriftModel hq ν₀).reverseDrift C.G))
    (a b f g : TestFunction C.chartOpens ℝ (⊤ : ℕ∞)) :
    IntegrableOn (fun ξ => C.leftParametrixNoDrift K a b f ξ * g ξ) C.U := by
  have hNZ : NeZero (n + m) := ⟨C.G.dimension_pos.ne'⟩
  have hU : IsOpen C.U := C.isOpen_U
  have hUm : MeasurableSet C.U := hU.measurableSet
  have hKa : IsCompact (tsupport (a : (Fin (n + m) → ℝ) → ℝ)) := a.hasCompactSupport
  have hKb : IsCompact (tsupport (b : (Fin (n + m) → ℝ) → ℝ)) := b.hasCompactSupport
  have hKaU : tsupport (a : (Fin (n + m) → ℝ) → ℝ) ⊆ C.U := a.tsupport_subset
  have hKbU : tsupport (b : (Fin (n + m) → ℝ) → ℝ) ⊆ C.U := b.tsupport_subset
  have ht₁c : Continuous (fun ξ => a ξ * g ξ) := a.continuous.mul g.continuous
  have ht₁0 : ∀ ξ ∉ tsupport (a : (Fin (n + m) → ℝ) → ℝ), a ξ * g ξ = 0 := fun ξ hξ => by
    simp [image_eq_zero_of_notMem_tsupport hξ]
  have hwc : ContinuousOn (fun η => b η / C.c η * f η) C.U :=
    (b.continuous.continuousOn.div C.density_smooth.continuousOn
      (fun η hη => (C.density_pos η hη).ne')).mul f.continuous.continuousOn
  have hw0 : ∀ η ∉ tsupport (b : (Fin (n + m) → ℝ) → ℝ), b η / C.c η * f η = 0 := fun η hη => by
    simp [image_eq_zero_of_notMem_tsupport hη]
  have hκ : ContinuousOn (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) =>
      (K : (Fin (n + m) → ℝ) → ℝ) (C.Θ p.2 p.1)) {p | p.1 ∈ C.U ∧ p.2 ∈ C.U ∧ p.1 ≠ p.2} :=
    K.smooth_off_zero.continuousOn.comp contDiffOn_theta_swap_noDrift.continuousOn
      (fun p hp => C.theta_ne_zero hp.2.1 hp.1 hp.2.2)
  obtain ⟨M₁, hM₁, hmass₁⟩ := exists_lintegral_bound_kernel_of_standing_noDrift K hKa hKb hKaU hKbU
  have hint := (integrable_and_integral_swap_of_mass hU hKa hKb hKaU hKbU
      (κ := fun ξ η => (K : (Fin (n + m) → ℝ) → ℝ) (C.Θ η ξ)) (t := fun ξ => a ξ * g ξ)
      (w := fun η => b η / C.c η * f η) hκ ht₁c.continuousOn hwc ht₁0 hw0 hM₁ hmass₁).1
  refine (hint.integral_prod_left).congr (Filter.Eventually.of_forall fun ξ => ?_)
  simp only [leftParametrixNoDrift]
  calc (∫ η in C.U, (a ξ * g ξ) * (K : (Fin (n + m) → ℝ) → ℝ) (C.Θ η ξ) *
        (b η / C.c η * f η))
      = ∫ η in C.U, (a ξ * g ξ) *
          ((K : (Fin (n + m) → ℝ) → ℝ) (C.Θ η ξ) * (b η / C.c η * f η)) :=
        integral_congr_ae (Filter.Eventually.of_forall fun η => by ring)
    _ = (a ξ * g ξ) *
          ∫ η in C.U, (K : (Fin (n + m) → ℝ) → ℝ) (C.Θ η ξ) * (b η / C.c η * f η) :=
        integral_const_mul _ _
    _ = (a ξ * ∫ η in C.U, (K : (Fin (n + m) → ℝ) → ℝ) (C.Θ η ξ) * (b η / C.c η * f η)) * g ξ := by
        ring

end LiftedChart

variable {n q s m : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}

/-- Assembly of the signed parametrix for the lifted frame without drift from the error type bounds:
for the H1 fundamental kernel `Γ` of the no-drift model of a lifted chart `C`, with reflection
`Γ*`, a frame `F` with `F.Θ = C.Θ`, `V ⊆ C.U`, `F.Γ = Γ`, `F.Γs = Γ*`, `ParametrixErrorTypesNoDrift`
implies the operator-level statement `SignedParametrixNoDrift F C.Xl C.c` (`L̃ = sumSquares C.Xl`).
`P₁, P₂` are single principal terms with `D = id` of degree `0`, hence of type 2 unconditionally;
the identities follow from the no-drift left parametrix theorems
(`integral_leftParametrix_mul_sumSquares_noDrift`,
`leftParametrixTNoDrift_sumSquares_add_chartErrorTNoDrift`). -/
theorem signedParametrixNoDrift_of_errorTypesNoDrift
    (C : LiftedChart (fun _ : Fin q => (1 : ℕ+)) s Ω hΩ X x₀ m)
    {F : KernelFrame (n + m)} (hΘ : F.Θ = C.Θ) (hV : (F.V : Set (Fin (n + m) → ℝ)) ⊆ C.U)
    (hq : 0 < q) (ν₀ : G2.HomogeneousNorm C.G)
    (Γ : H1.FundamentalKernel C.G (C.noDriftModel hq ν₀))
    (hQ : 2 < (C.G.homogeneousDimension : ℝ))
    (hΓ : F.Γ = ⇑Γ) (hΓs : F.Γs = ⇑(Γ.reflection hQ))
    (a b : TestFunction F.V ℝ (⊤ : ℕ∞)) (hErr : ParametrixErrorTypesNoDrift C F hq ν₀ Γ hQ a b) :
    SignedParametrixNoDrift F C.Xl C.c a b := by
  intro hc hc0 hab
  obtain ⟨hE1, hE2⟩ := hErr hab
  have hVle : F.V ≤ C.chartOpens := hV
  have hUm : MeasurableSet C.U := C.isOpen_U.measurableSet
  have hbc : ∀ ξ, divTest F C.c hc hc0 b ξ = b ξ / C.c ξ := divTest_apply F C.c hc hc0 b
  -- vanishing of test functions outside the cutoff region
  have hf0 : ∀ (t : TestFunction F.V ℝ (⊤ : ℕ∞)) (η : Fin (n + m) → ℝ), η ∉ C.U → t η = 0 :=
    fun t η hη => t.zero_on_compl (show η ∈ ((F.V : Set (Fin (n + m) → ℝ)))ᶜ from fun h => hη (hV h))
  -- the four operators
  obtain ⟨P₁, hP₁⟩ : ∃ P : TypeOperator F 2,
      P.kernel = fun ξ η => a ξ * F.Γs (F.Θ η ξ) * (b η / C.c η) :=
    ⟨⟨fun ξ η => a ξ * F.Γs (F.Θ η ξ) * (b η / C.c η),
      (isTypeKernelOn_of_eq_principal F (le_refl 2) a (divTest F C.c hc hc0 b) true _
        (fun ξ η => by rw [hbc]; simp [KernelFrame.pole]; ring)).isTypeKernel, 0, fun _ => rfl⟩, rfl⟩
  obtain ⟨P₂, hP₂⟩ : ∃ P : TypeOperator F 2,
      P.kernel = fun ξ η => b ξ / C.c ξ * (a η * F.Γ (F.Θ η ξ)) :=
    ⟨⟨fun ξ η => b ξ / C.c ξ * (a η * F.Γ (F.Θ η ξ)),
      (isTypeKernelOn_of_eq_principal F (le_refl 2) (divTest F C.c hc hc0 b) a false _
        (fun ξ η => by rw [hbc]; simp [KernelFrame.pole]; ring)).isTypeKernel, 0, fun _ => rfl⟩, rfl⟩
  obtain ⟨F₁, hF₁⟩ : ∃ P : TypeOperator F 1,
      P.kernel = fun ξ η => -C.leftErrorKernelNoDrift (Γ.reflection hQ) a b ξ η :=
    ⟨⟨_, hE1.isTypeKernel, 0, fun _ => rfl⟩, rfl⟩
  obtain ⟨F₂, hF₂⟩ : ∃ P : TypeOperator F 1,
      P.kernel = fun ξ η => -C.leftErrorKernelNoDrift (Γ.reflection hQ) a b η ξ :=
    ⟨⟨_, hE2.isTypeKernel, 0, fun _ => rfl⟩, rfl⟩
  have hP₁apply : ∀ (f : TestFunction F.V ℝ (⊤ : ℕ∞)) (ξ : Fin (n + m) → ℝ),
      P₁.apply f ξ = C.leftParametrixNoDrift (Γ.reflection hQ) a b f ξ := by
    intro f ξ
    rw [TypeOperator.apply_of_ne_zero P₁ (by norm_num) _ ξ, hP₁]
    simp only [hΓs, hΘ]
    unfold LiftedChart.leftParametrixNoDrift
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := C.U)
      (fun η hη => by rw [hf0 f η hη, mul_zero]), ← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun η => by ring)
  have hF₁apply : ∀ (f : TestFunction F.V ℝ (⊤ : ℕ∞)) (ξ : Fin (n + m) → ℝ),
      F₁.apply f ξ = -C.leftErrorNoDrift (Γ.reflection hQ) a b f ξ := by
    intro f ξ
    rw [TypeOperator.apply_of_ne_zero F₁ (by norm_num) _ ξ, hF₁]
    unfold LiftedChart.leftErrorNoDrift
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := C.U)
      (fun η hη => by rw [hf0 f η hη, mul_zero]), ← integral_neg]
    exact integral_congr_ae (Filter.Eventually.of_forall fun η => by ring)
  have hP₂apply : ∀ (g : (Fin (n + m) → ℝ) → ℝ) (ξ : Fin (n + m) → ℝ),
      P₂.apply g ξ = C.leftParametrixTNoDrift Γ a b g ξ := by
    intro g ξ
    rw [TypeOperator.apply_of_ne_zero P₂ (by norm_num) _ ξ, hP₂]
    simp only [hΓ, hΘ]
    unfold LiftedChart.leftParametrixTNoDrift
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := C.U)
      (fun η hη => by rw [hf0 a η hη]; ring), ← integral_const_mul]
    exact integral_congr_ae (Filter.Eventually.of_forall fun η => by ring)
  have hF₂apply : ∀ (f : TestFunction F.V ℝ (⊤ : ℕ∞)) (ξ : Fin (n + m) → ℝ),
      F₂.apply f ξ = C.leftChartErrorTNoDrift (Γ.reflection hQ) a b f ξ := by
    intro f ξ
    rw [TypeOperator.apply_of_ne_zero F₂ (by norm_num) _ ξ, hF₂]
    unfold LiftedChart.leftChartErrorTNoDrift LiftedChart.leftErrorTNoDrift LiftedChart.leftErrorKernelNoDrift
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := C.U)
      (fun η hη => by rw [hf0 f η hη, mul_zero]), ← integral_const_mul, ← integral_neg]
    exact integral_congr_ae (Filter.Eventually.of_forall fun η => by ring)
  refine ⟨P₁, P₂, F₁, F₂, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ξ η _
    rw [hP₁]
  · intro ξ η _
    rw [hP₂]
  · -- `P₂ = P₁ᵗ`: antisymmetry of `Θ` and `Γ*(u) = Γ(-u)`
    intro ξ η _
    rw [hP₁, hP₂]
    by_cases hη : η ∈ C.U
    · by_cases hξ : ξ ∈ C.U
      · simp only [hΓ, hΓs, hΘ]
        have := LiftedChart.reflection_theta_noDrift Γ hQ (η := ξ) (ξ := η) hξ hη
        change b ξ / C.c ξ * (a η * Γ (C.Θ η ξ)) = a η * (Γ.reflection hQ) (C.Θ ξ η) * (b ξ / C.c ξ)
        rw [this]
        ring
      · have hb : b ξ = 0 := by
          have := hf0 b ξ hξ
          exact this
        simp [hb]
    · have ha : a η = 0 := hf0 a η hη
      simp [ha]
  · intro ξ η _
    rw [hF₁, hF₂]
  · rw [hF₁]
    exact hE1
  · rw [hF₂]
    exact hE2
  · intro f φ
    have ha0 : ∀ ξ ∈ C.U \ (F.V : Set (Fin (n + m) → ℝ)), a ξ = 0 := fun ξ hξ => a.zero_on_compl hξ.2
    have hφ0 : ∀ ξ ∈ C.U \ (F.V : Set (Fin (n + m) → ℝ)), φ ξ = 0 := fun ξ hξ => φ.zero_on_compl hξ.2
    have hVU : ∀ g : (Fin (n + m) → ℝ) → ℝ, (∀ ξ ∈ C.U \ (F.V : Set (Fin (n + m) → ℝ)), g ξ = 0) →
        ∫ ξ in (F.V : Set (Fin (n + m) → ℝ)), g ξ = ∫ ξ in C.U, g ξ := fun g hg =>
      (setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hUm hV hg).symm
    obtain ⟨hI, hmain⟩ := LiftedChart.integral_leftParametrix_mul_sumSquares_noDrift hq ν₀ (Γ.reflection hQ)
      (LiftedChart.testOfLeNoDrift F.V hVle a) (LiftedChart.testOfLeNoDrift F.V hVle b)
      (LiftedChart.testOfLeNoDrift F.V hVle f) (LiftedChart.testOfLeNoDrift F.V hVle φ) hab
    have hL : (sumSquaresTestNoDrift C.chartOpens C.Xl C.contDiffOn_Xl_U
        (LiftedChart.testOfLeNoDrift F.V hVle φ) : (Fin (n + m) → ℝ) → ℝ) =
        sumSquares C.Xl φ :=
      sumSquaresTestNoDrift_coe C.chartOpens C.Xl C.contDiffOn_Xl_U (LiftedChart.testOfLeNoDrift F.V hVle φ)
    have hI₁ := LiftedChart.integrableOn_leftParametrixNoDrift_mul_test hq ν₀ (Γ.reflection hQ)
      (LiftedChart.testOfLeNoDrift F.V hVle a) (LiftedChart.testOfLeNoDrift F.V hVle b)
      (LiftedChart.testOfLeNoDrift F.V hVle f)
      (sumSquaresTestNoDrift C.chartOpens C.Xl C.contDiffOn_Xl_U (LiftedChart.testOfLeNoDrift F.V hVle φ))
    rw [hL] at hI₁
    simp only [LiftedChart.coe_testOfLeNoDrift] at hI₁ hI hmain
    have hmain' : (∫ ξ in C.U, C.leftParametrixNoDrift (Γ.reflection hQ) a b f ξ *
          sumSquares C.Xl φ ξ) =
        (∫ ξ in C.U, a ξ * f ξ * φ ξ) + ∫ ξ in C.U, C.leftErrorNoDrift (Γ.reflection hQ) a b f ξ * φ ξ :=
      hmain
    have hI' : IntegrableOn (fun ξ => C.leftErrorNoDrift (Γ.reflection hQ) a b f ξ * φ ξ) C.U := hI
    refine ⟨?_, ?_, ?_⟩
    · simp_rw [hP₁apply]
      exact hI₁.mono_set hV
    · refine (hI'.neg.congr_fun (fun ξ _ => ?_) hUm).mono_set hV
      simp only [Pi.neg_apply]
      rw [hF₁apply]
      ring
    · have e1 : (∫ ξ in (F.V : Set (Fin (n + m) → ℝ)),
            P₁.apply f ξ * sumSquares C.Xl φ ξ) =
          ∫ ξ in C.U, C.leftParametrixNoDrift (Γ.reflection hQ) a b f ξ * sumSquares C.Xl φ ξ := by
        simp_rw [hP₁apply]
        exact hVU _ (fun ξ hξ => by simp [LiftedChart.leftParametrixNoDrift, ha0 ξ hξ])
      have e2 : (∫ ξ in (F.V : Set (Fin (n + m) → ℝ)), a ξ * f ξ * φ ξ) =
          ∫ ξ in C.U, a ξ * f ξ * φ ξ := hVU _ (fun ξ hξ => by simp [ha0 ξ hξ])
      have e3 : (∫ ξ in (F.V : Set (Fin (n + m) → ℝ)), F₁.apply f ξ * φ ξ) =
          ∫ ξ in C.U, F₁.apply f ξ * φ ξ := hVU _ (fun ξ hξ => by simp [hφ0 ξ hξ])
      have e4 : (∫ ξ in C.U, F₁.apply f ξ * φ ξ) =
          -∫ ξ in C.U, C.leftErrorNoDrift (Γ.reflection hQ) a b f ξ * φ ξ := by
        rw [← integral_neg]
        refine setIntegral_congr_fun hUm (fun ξ _ => ?_)
        rw [hF₁apply]
        ring
      rw [e1, e2, e3, e4, hmain']
      ring
  · intro f ξ hξ
    have h := LiftedChart.leftParametrixTNoDrift_sumSquares_add_chartErrorTNoDrift_of_le F.V hVle hq ν₀ Γ hQ a b f
      hab (hV hξ)
    rw [hP₂apply, hF₂apply]
    exact h.symm

end RothschildStein.P1
