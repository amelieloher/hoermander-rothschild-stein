-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.RightParametrixLp
public import RothschildStein.P1.RightParametrixNoDriftMass

/-!
# The signed right parametrix identity without drift: `L̃ P_R = M_a + E_R`, `F_R^chart = -E_R`

The right parametrix of a lifted no-drift chart (alphabet `Fin q`, all weights one, `L̃ = ∑ᵢ X̃ᵢ²`,
given by `sumSquares C.Xl`; BB p. 605, Prop. 11.61, without drift, with the roles of Thm. 11.25
exchanged): for the H1 fundamental kernel `Γ` of the no-drift model
(`LiftedChart.noDriftModel`, zero drift) and cutoffs `a, b ∈ C_c^∞(C.U)` with `a b = a`,

`P_R f(ξ) = a(ξ) ∫_U Γ(Θ(η, ξ)) (b(η) / c(η)) f(η) dη`   (`LiftedChart.rightParametrixNoDrift`),
`E_R f(ξ) = ∫_U e(ξ, η) f(η) dη`,
`e(ξ, η) = (b(η) / c(η)) [a(ξ) (E_η Γ)(Θ(η, ξ)) + 2 ∑ᵢ (X̃ᵢ a)(ξ) (Zᵢ Γ)(Θ(η, ξ)) +
  (L̃ a)(ξ) Γ(Θ(η, ξ))]`   (`rightErrorKernelNoDrift`, `rightErrorNoDrift`).

For `f` locally integrable on `C.U` (in particular a test function, or `f ∈ L^p`) and a test `φ`,
`∫ P_R f · L̃ᵀφ = ∫ a f φ + ∫ (E_R f) φ`, that is `L̃ P_R f = a f + E_R f` in the sense of
distributions (`integral_rightParametrix_mul_transpose_of_locallyIntegrable_noDrift`), and with
`F_R^chart := -E_R`, `∫ P_R f · L̃ᵀφ = ∫ (a f - F_R^chart f) φ`
(`integral_rightParametrix_mul_transpose_chartError_of_locallyIntegrable_noDrift`). The statements for test inputs (`integral_rightParametrix_mul_transpose_noDrift`,
`_chartError_noDrift`, `_of_le_noDrift`) follow since a test function is locally integrable. The
proof applies the pole limit `integral_kernel_comp_theta_mul_transpose_noDrift` for each `η` and
exchanges the order of integration (Fubini) for the kernel and for the error kernel, whose lower
integrals over the support of the test are bounded uniformly in `η` (`RightParametrixNoDriftMass`);
the input enters only through the integrable weight `w = (b / c) f` (the generic Fubini lemma
`integrable_prod_of_mass_bound_of_integrable`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology ENNReal
open RothschildStein.P2
namespace RothschildStein.P1
namespace LiftedChart

variable {n q s m : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  (C : LiftedChart (fun _ : Fin q => (1 : ℕ+)) s Ω hΩ X x₀ m)

/-- The right parametrix `P_R f(ξ) = a(ξ) ∫_U Γ(Θ(η, ξ)) (b(η) / c(η)) f(η) dη`
(BB p. 605, proof of Prop 11.61). -/
def rightParametrixNoDrift (K a b f : (Fin (n + m) → ℝ) → ℝ) (ξ : Fin (n + m) → ℝ) : ℝ :=
  a ξ * ∫ η in C.U, K (C.Θ η ξ) * (b η / C.c η * f η)

/-- The error kernel `e(ξ, η) = (b(η) / c(η)) [a(ξ) (E_η Γ)(Θ(η, ξ)) +
2 ∑ᵢ (X̃ᵢ a)(ξ) (Zᵢ Γ)(Θ(η, ξ)) + (L̃ a)(ξ) Γ(Θ(η, ξ))]` (the right pole computation). -/
def rightErrorKernelNoDrift (K a b : (Fin (n + m) → ℝ) → ℝ) (ξ η : Fin (n + m) → ℝ) : ℝ :=
  b η / C.c η * C.errBracketNoDrift K a η ξ

/-- The error operator `E_R f(ξ) = ∫_U e(ξ, η) f(η) dη`. -/
def rightErrorNoDrift (K a b f : (Fin (n + m) → ℝ) → ℝ) (ξ : Fin (n + m) → ℝ) : ℝ :=
  ∫ η in C.U, C.rightErrorKernelNoDrift K a b ξ η * f η

/-- The chart error `F_R^chart = -E_R`, so that `L̃ P_R = M_a + E_R` reads
`M_a = L̃ P_R + F_R^chart`. -/
def rightChartErrorNoDrift (K a b f : (Fin (n + m) → ℝ) → ℝ) (ξ : Fin (n + m) → ℝ) : ℝ :=
  -C.rightErrorNoDrift K a b f ξ

variable {C}

/-- For tests `a, φ` of the chart and `f` locally integrable on
`C.U`, `a f φ` is integrable on `C.U` (`a` has compact support in `C.U`). -/
theorem integrableOn_cutoff_mul_test_noDrift (a φ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞))
    {f : (Fin (n + m) → ℝ) → ℝ} (hf : LocallyIntegrableOn f C.U) :
    IntegrableOn (fun η => a η * f η * φ η) C.U := by
  have hKa : IsCompact (tsupport (a : (Fin (n + m) → ℝ) → ℝ)) := a.hasCompactSupport
  have hfa : IntegrableOn f (tsupport (a : (Fin (n + m) → ℝ) → ℝ)) :=
    hf.integrableOn_compact_subset a.tsupport_subset hKa
  have hg : ContinuousOn (fun η => a η * φ η) (tsupport (a : (Fin (n + m) → ℝ) → ℝ)) :=
    (a.continuous.mul φ.continuous).continuousOn
  have h1 : IntegrableOn (fun η => f η * (a η * φ η)) (tsupport (a : (Fin (n + m) → ℝ) → ℝ)) :=
    hfa.mul_continuousOn hg hKa
  have h2 : IntegrableOn (fun η => f η * (a η * φ η)) C.U :=
    h1.of_forall_sdiff_eq_zero C.isOpen_U.measurableSet (fun η hη => by
      have : η ∉ tsupport (a : (Fin (n + m) → ℝ) → ℝ) := hη.2
      simp [image_eq_zero_of_notMem_tsupport this])
  refine h2.congr_fun (fun η _ => ?_) C.isOpen_U.measurableSet
  ring

/-- **The signed identity `L̃ P_R = M_a + E_R` for locally integrable
inputs.** For the H1 fundamental kernel `Γ`, tests `a, b, φ` on `C.U` with `a b = a`, and `f`
locally integrable on `C.U`: `(E_R f) φ` is integrable on `C.U` and
`∫_U P_R f · L̃ᵀφ = ∫_U a f φ + ∫_U (E_R f) φ` (the statement of
`integral_rightParametrix_mul_transpose` with the test input `f` replaced by `f ∈ L^1_loc(C.U)`;
same Fubini proof with the integrable factor `w = (b / c) f`). -/
theorem integral_rightParametrix_mul_transpose_of_locallyIntegrable_noDrift (hq : 0 < q)
    (ν₀ : G2.HomogeneousNorm C.G) (K : H1.FundamentalKernel C.G (C.noDriftModel hq ν₀))
    (a b φ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞)) {f : (Fin (n + m) → ℝ) → ℝ}
    (hf : LocallyIntegrableOn f C.U) (hab : ∀ ξ, a ξ * b ξ = a ξ) :
    IntegrableOn (fun ξ => C.rightErrorNoDrift K a b f ξ * φ ξ) C.U ∧
    (∫ ξ in C.U, C.rightParametrixNoDrift K a b f ξ * sumSquaresTranspose C.Xl φ ξ) =
      (∫ ξ in C.U, a ξ * f ξ * φ ξ) + ∫ ξ in C.U, C.rightErrorNoDrift K a b f ξ * φ ξ := by
  have hNZ : NeZero (n + m) := ⟨C.G.dimension_pos.ne'⟩
  have hU : IsOpen C.U := C.isOpen_U
  have hUm : MeasurableSet C.U := hU.measurableSet
  have haU : ContDiffOn ℝ (⊤ : ℕ∞) a C.U := a.contDiff.contDiffOn
  -- compact supports
  have hKa : IsCompact (tsupport (a : (Fin (n + m) → ℝ) → ℝ)) := a.hasCompactSupport
  have hKb : IsCompact (tsupport (b : (Fin (n + m) → ℝ) → ℝ)) := b.hasCompactSupport
  have hKφ : IsCompact (tsupport (φ : (Fin (n + m) → ℝ) → ℝ)) := φ.hasCompactSupport
  have hKaU : tsupport (a : (Fin (n + m) → ℝ) → ℝ) ⊆ C.U := a.tsupport_subset
  have hKbU : tsupport (b : (Fin (n + m) → ℝ) → ℝ) ⊆ C.U := b.tsupport_subset
  have hKφU : tsupport (φ : (Fin (n + m) → ℝ) → ℝ) ⊆ C.U := φ.tsupport_subset
  -- the test functions in `ξ` and the weight in `η`
  have hT : Continuous (sumSquaresTranspose C.Xl φ) := by
    have e := sumSquaresTransposeTest_coe_noDrift C.chartOpens C.Xl C.contDiffOn_Xl_U φ
    rw [← e]
    exact (sumSquaresTransposeTest C.chartOpens C.Xl C.contDiffOn_Xl_U φ).continuous
  set t₁ : (Fin (n + m) → ℝ) → ℝ := fun ξ => a ξ * sumSquaresTranspose C.Xl φ ξ with ht₁
  have ht₁c : Continuous t₁ := a.continuous.mul hT
  have ht₁cs : HasCompactSupport t₁ := a.hasCompactSupport.mul_right
  obtain ⟨Bt₁, hBt₁⟩ := ht₁c.bounded_above_of_compact_support ht₁cs
  have ht₁0 : ∀ ξ ∉ tsupport (a : (Fin (n + m) → ℝ) → ℝ), t₁ ξ = 0 := fun ξ hξ => by
    simp [ht₁, image_eq_zero_of_notMem_tsupport hξ]
  obtain ⟨Bt₂, hBt₂⟩ := φ.continuous.bounded_above_of_compact_support φ.hasCompactSupport
  have ht₂0 : ∀ ξ ∉ tsupport (φ : (Fin (n + m) → ℝ) → ℝ), φ ξ = 0 := fun ξ hξ =>
    image_eq_zero_of_notMem_tsupport hξ
  set w : (Fin (n + m) → ℝ) → ℝ := fun η => b η / C.c η * f η with hw
  have hbc : ContinuousOn (fun η => b η / C.c η) C.U :=
    b.continuous.continuousOn.div C.density_smooth.continuousOn
      (fun η hη => (C.density_pos η hη).ne')
  have hw_meas : AEStronglyMeasurable w (volume.restrict C.U) :=
    (hbc.aestronglyMeasurable hUm).mul hf.aestronglyMeasurable
  have hw0 : ∀ η ∉ tsupport (b : (Fin (n + m) → ℝ) → ℝ), w η = 0 := fun η hη => by
    simp [hw, image_eq_zero_of_notMem_tsupport hη]
  have hwI : ∫⁻ η in tsupport (b : (Fin (n + m) → ℝ) → ℝ), ‖w η‖ₑ < ⊤ :=
    (IntegrableOn.continuousOn_mul (hbc.mono hKbU) (hf.integrableOn_compact_subset hKbU hKb) hKb).2
  -- kernels
  have hκ₁ : AEStronglyMeasurable (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) =>
      (K : (Fin (n + m) → ℝ) → ℝ) (C.Θ p.2 p.1))
      ((volume.restrict C.U).prod (volume.restrict C.U)) :=
    aestronglyMeasurable_prod_of_continuousOn hU
      (K.smooth_off_zero.continuousOn.comp contDiffOn_theta_swap_noDrift.continuousOn
        (fun p hp => C.theta_ne_zero hp.2.1 hp.1 hp.2.2))
  have hκ₂ : AEStronglyMeasurable (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) =>
      C.errBracketNoDrift K a p.2 p.1) ((volume.restrict C.U).prod (volume.restrict C.U)) :=
    aestronglyMeasurable_prod_of_continuousOn hU (continuousOn_errBracketNoDrift K haU)
  obtain ⟨M₁, hM₁, hmass₁⟩ := exists_lintegral_bound_kernel_noDrift hq ν₀ K hKa hKb hKaU hKbU
  obtain ⟨M₂, hM₂, hmass₂⟩ := exists_lintegral_bound_errBracketNoDrift hq ν₀ K hKφ hKb hKφU hKbU haU
  have hint₁ : Integrable (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) =>
      t₁ p.1 * (K : (Fin (n + m) → ℝ) → ℝ) (C.Θ p.2 p.1) * w p.2)
      ((volume.restrict C.U).prod (volume.restrict C.U)) :=
    integrable_prod_of_mass_bound_of_integrable (κ := fun ξ η => (K : (Fin (n + m) → ℝ) → ℝ) (C.Θ η ξ))
      hKaU hKbU hKa.isClosed.measurableSet hKb.isClosed.measurableSet hκ₁
      ht₁c.aestronglyMeasurable hw_meas (fun ξ _ => by simpa [Real.norm_eq_abs] using hBt₁ ξ)
      hwI ht₁0 hw0 hM₁ hmass₁
  have hint₂ : Integrable (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) =>
      φ p.1 * C.errBracketNoDrift K a p.2 p.1 * w p.2)
      ((volume.restrict C.U).prod (volume.restrict C.U)) :=
    integrable_prod_of_mass_bound_of_integrable (κ := fun ξ η => C.errBracketNoDrift K a η ξ)
      hKφU hKbU hKφ.isClosed.measurableSet hKb.isClosed.measurableSet hκ₂
      φ.continuous.aestronglyMeasurable hw_meas
      (fun ξ _ => by simpa [Real.norm_eq_abs] using hBt₂ ξ) hwI ht₂0 hw0 hM₂ hmass₂
  -- Step A: the left side as an iterated integral
  have stepA : (∫ ξ in C.U, C.rightParametrixNoDrift K a b f ξ * sumSquaresTranspose C.Xl φ ξ) =
      ∫ ξ in C.U, ∫ η in C.U, t₁ ξ * (K : (Fin (n + m) → ℝ) → ℝ) (C.Θ η ξ) * w η := by
    refine setIntegral_congr_fun hUm (fun ξ _ => ?_)
    simp only [rightParametrixNoDrift]
    calc (a ξ * ∫ η in C.U, (K : (Fin (n + m) → ℝ) → ℝ) (C.Θ η ξ) * (b η / C.c η * f η)) *
          sumSquaresTranspose C.Xl φ ξ
        = (a ξ * sumSquaresTranspose C.Xl φ ξ) *
          ∫ η in C.U, (K : (Fin (n + m) → ℝ) → ℝ) (C.Θ η ξ) * (b η / C.c η * f η) := by ring
      _ = ∫ η in C.U, (a ξ * sumSquaresTranspose C.Xl φ ξ) *
          ((K : (Fin (n + m) → ℝ) → ℝ) (C.Θ η ξ) * (b η / C.c η * f η)) :=
          (integral_const_mul _ _).symm
      _ = ∫ η in C.U, t₁ ξ * (K : (Fin (n + m) → ℝ) → ℝ) (C.Θ η ξ) * w η :=
          integral_congr_ae (Filter.Eventually.of_forall fun η => by simp only [ht₁, hw]; ring)
  -- Step B: Fubini for the kernel
  have stepB := integral_integral_swap (μ := volume.restrict C.U) (ν := volume.restrict C.U)
    (f := fun ξ η => t₁ ξ * (K : (Fin (n + m) → ℝ) → ℝ) (C.Θ η ξ) * w η) hint₁
  -- Step C: the pole limit for each `η`
  have stepC : ∀ η ∈ C.U, (∫ ξ in C.U, t₁ ξ * (K : (Fin (n + m) → ℝ) → ℝ) (C.Θ η ξ) * w η) =
      w η * (C.c η * (a η * φ η)) + w η * ∫ ξ in C.U, C.errBracketNoDrift K a η ξ * φ ξ := by
    intro η hη
    have h := (integral_kernel_comp_theta_mul_transpose_noDrift hq ν₀ K hη haU φ).2
    calc (∫ ξ in C.U, t₁ ξ * (K : (Fin (n + m) → ℝ) → ℝ) (C.Θ η ξ) * w η)
        = ∫ ξ in C.U, w η * (a ξ * (K : (Fin (n + m) → ℝ) → ℝ) (C.Θ η ξ) *
            sumSquaresTranspose C.Xl φ ξ) :=
          integral_congr_ae (Filter.Eventually.of_forall fun ξ => by simp only [ht₁]; ring)
      _ = w η * ∫ ξ in C.U, a ξ * (K : (Fin (n + m) → ℝ) → ℝ) (C.Θ η ξ) *
            sumSquaresTranspose C.Xl φ ξ := integral_const_mul _ _
      _ = w η * (C.c η * (a η * φ η) + ∫ ξ in C.U, C.errBracketNoDrift K a η ξ * φ ξ) := by
          rw [h]
          rfl
      _ = _ := by ring
  -- integrability of the two terms of Step C
  have hI₁ : IntegrableOn (fun η => w η * (C.c η * (a η * φ η))) C.U := by
    refine (integrableOn_cutoff_mul_test_noDrift a φ hf).congr_fun (fun η hη => ?_) hUm
    have hc : C.c η ≠ 0 := (C.density_pos η hη).ne'
    have e : b η / C.c η * f η * (C.c η * (a η * φ η)) = (a η * b η) * f η * φ η := by
      field_simp
    show a η * f η * φ η = b η / C.c η * f η * (C.c η * (a η * φ η))
    rw [e, hab η]
  have hI₂ : IntegrableOn (fun η => w η * ∫ ξ in C.U, C.errBracketNoDrift K a η ξ * φ ξ) C.U := by
    refine (hint₂.integral_prod_right).congr (Filter.Eventually.of_forall fun η => ?_)
    show ∫ ξ in C.U, φ ξ * C.errBracketNoDrift K a η ξ * w η =
      w η * ∫ ξ in C.U, C.errBracketNoDrift K a η ξ * φ ξ
    rw [mul_comm (w η), ← integral_mul_const]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ξ => by ring)
  have stepD : (∫ η in C.U, ∫ ξ in C.U, t₁ ξ * (K : (Fin (n + m) → ℝ) → ℝ) (C.Θ η ξ) * w η) =
      (∫ η in C.U, w η * (C.c η * (a η * φ η))) +
        ∫ η in C.U, w η * ∫ ξ in C.U, C.errBracketNoDrift K a η ξ * φ ξ := by
    rw [← integral_add hI₁ hI₂]
    exact setIntegral_congr_fun hUm stepC
  -- Step E: Fubini for the error kernel
  have h1 : (∫ η in C.U, w η * ∫ ξ in C.U, C.errBracketNoDrift K a η ξ * φ ξ) =
      ∫ η in C.U, ∫ ξ in C.U, φ ξ * C.errBracketNoDrift K a η ξ * w η := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
    show w η * ∫ ξ in C.U, C.errBracketNoDrift K a η ξ * φ ξ =
      ∫ ξ in C.U, φ ξ * C.errBracketNoDrift K a η ξ * w η
    rw [mul_comm (w η), ← integral_mul_const]
    exact (integral_congr_ae (Filter.Eventually.of_forall fun ξ => by ring)).symm
  have h2 := (integral_integral_swap (μ := volume.restrict C.U) (ν := volume.restrict C.U)
    (f := fun ξ η => φ ξ * C.errBracketNoDrift K a η ξ * w η) hint₂).symm
  have hE : ∀ ξ, (∫ η in C.U, φ ξ * C.errBracketNoDrift K a η ξ * w η) =
      C.rightErrorNoDrift K a b f ξ * φ ξ := by
    intro ξ
    simp only [rightErrorNoDrift, rightErrorKernelNoDrift]
    calc (∫ η in C.U, φ ξ * C.errBracketNoDrift K a η ξ * w η)
        = ∫ η in C.U, φ ξ * (b η / C.c η * C.errBracketNoDrift K a η ξ * f η) :=
          integral_congr_ae (Filter.Eventually.of_forall fun η => by simp only [hw]; ring)
      _ = φ ξ * ∫ η in C.U, b η / C.c η * C.errBracketNoDrift K a η ξ * f η := integral_const_mul _ _
      _ = _ := mul_comm _ _
  have stepE : (∫ η in C.U, w η * ∫ ξ in C.U, C.errBracketNoDrift K a η ξ * φ ξ) =
      ∫ ξ in C.U, C.rightErrorNoDrift K a b f ξ * φ ξ := by
    rw [h1, h2]
    exact setIntegral_congr_fun hUm (fun ξ _ => hE ξ)
  refine ⟨(hint₂.integral_prod_left).congr (Filter.Eventually.of_forall fun ξ => ?_), ?_⟩
  · exact hE ξ
  · rw [stepA, stepB, stepD, stepE]
    congr 1
    refine setIntegral_congr_fun hUm (fun η hη => ?_)
    have hc : C.c η ≠ 0 := (C.density_pos η hη).ne'
    have e : b η / C.c η * f η * (C.c η * (a η * φ η)) = (a η * b η) * f η * φ η := by
      field_simp
    show b η / C.c η * f η * (C.c η * (a η * φ η)) = a η * f η * φ η
    rw [e, hab η]

/-- **The signed right parametrix identity for locally integrable inputs.** With
`F_R^chart = -E_R`: for `f` locally integrable on `C.U`, tests `a, b, φ` with `a b = a`,
`∫_U P_R f · L̃ᵀφ = ∫_U (a f - F_R^chart f) φ`, that is `L̃ P_R f = a f - F_R^chart f` in the sense
of distributions on `C.U`. -/
theorem integral_rightParametrix_mul_transpose_chartError_of_locallyIntegrable_noDrift (hq : 0 < q)
    (ν₀ : G2.HomogeneousNorm C.G) (K : H1.FundamentalKernel C.G (C.noDriftModel hq ν₀))
    (a b φ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞)) {f : (Fin (n + m) → ℝ) → ℝ}
    (hf : LocallyIntegrableOn f C.U) (hab : ∀ ξ, a ξ * b ξ = a ξ) :
    (∫ ξ in C.U, C.rightParametrixNoDrift K a b f ξ * sumSquaresTranspose C.Xl φ ξ) =
      ∫ ξ in C.U, (a ξ * f ξ - C.rightChartErrorNoDrift K a b f ξ) * φ ξ := by
  obtain ⟨hI, h⟩ := integral_rightParametrix_mul_transpose_of_locallyIntegrable_noDrift hq ν₀ K a b φ hf
    hab
  have hI' : IntegrableOn (fun ξ => a ξ * f ξ * φ ξ) C.U := integrableOn_cutoff_mul_test_noDrift a φ hf
  rw [h, ← integral_add hI' hI]
  refine setIntegral_congr_fun C.isOpen_U.measurableSet (fun ξ _ => ?_)
  simp only [rightChartErrorNoDrift]
  ring

end LiftedChart

end RothschildStein.P1
