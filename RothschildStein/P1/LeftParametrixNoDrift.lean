-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.LeftParametrixNoDriftMass
public import RothschildStein.P1.LeftParametrix

/-!
# The signed left parametrix identity without drift: `L̃* P₁ = M_a + E₁`, `F₁ = -E₁`

The signed left parametrix of a lifted no-drift chart (alphabet `Fin q`, all weights one,
`L̃ = ∑ᵢ X̃ᵢ²` given by `sumSquares C.Xl`; BB pp. 560–564, Thm. 11.25, without drift): for the
H1 fundamental kernel `Γ*` of the
reversed no-drift model `(C.noDriftModel hq ν₀).reverseDrift C.G` (the drift is `0`, so this model
has the fields `Fin.cons 0 C.Y` again) and cutoffs `a, b ∈ C_c^∞(C.U)` with `a b = a`,

`P₁ f(ξ) = a(ξ) ∫_U Γ*(Θ(η, ξ)) (b(η) / c(η)) f(η) dη`   (`LiftedChart.leftParametrixNoDrift`),
`E₁ f(ξ) = ∫_U e(ξ, η) f(η) dη`,
`e(ξ, η) = (b(η) / c(η)) [a(ξ) (E_η Γ*)(Θ(η, ξ)) + 2 ∑ᵢ (a dᵢ + X̃ᵢ a)(ξ) (Zᵢ Γ*)(Θ(η, ξ)) +
  (L̃* a)(ξ) Γ*(Θ(η, ξ))]`   (`leftErrorKernelNoDrift`, `leftErrorNoDrift`).

For tests `f, φ` on `C.U`, `∫ P₁ f · L̃φ = ∫ a f φ + ∫ (E₁ f) φ`, that is
`L̃* P₁ f = a f + E₁ f` in the sense of distributions
(`integral_leftParametrix_mul_sumSquares_noDrift`), and with `F₁ := -E₁`,
`∫ P₁ f · L̃φ = ∫ (a f - F₁ f) φ` (`integral_leftParametrix_mul_sumSquares_chartError_noDrift`). The proof applies the pole limit
`integral_kernel_comp_theta_mul_sumSquares_noDrift` for each `η` and exchanges the order of
integration (Fubini) for the kernel and for the error kernel, whose lower integrals over the support
of the test are bounded uniformly in `η` (`LeftParametrixNoDriftMass`).
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

/-- The left parametrix without drift,
`P₁ f(ξ) = a(ξ) ∫_U Γ*(Θ(η, ξ)) (b(η) / c(η)) f(η) dη` (BB pp. 560–564, Thm 11.25). -/
def leftParametrixNoDrift (K a b f : (Fin (n + m) → ℝ) → ℝ) (ξ : Fin (n + m) → ℝ) : ℝ :=
  a ξ * ∫ η in C.U, K (C.Θ η ξ) * (b η / C.c η * f η)

/-- The error kernel `e(ξ, η) = (b(η) / c(η)) [a(ξ) (E_η Γ*)(Θ(η, ξ)) +
2 ∑ᵢ (a dᵢ + X̃ᵢ a)(ξ) (Zᵢ Γ*)(Θ(η, ξ)) + (L̃* a)(ξ) Γ*(Θ(η, ξ))]` (the pole computation). -/
def leftErrorKernelNoDrift (K a b : (Fin (n + m) → ℝ) → ℝ) (ξ η : Fin (n + m) → ℝ) : ℝ :=
  b η / C.c η * C.leftErrBracketNoDrift K a η ξ

/-- The error operator `E₁ f(ξ) = ∫_U e(ξ, η) f(η) dη`. -/
def leftErrorNoDrift (K a b f : (Fin (n + m) → ℝ) → ℝ) (ξ : Fin (n + m) → ℝ) : ℝ :=
  ∫ η in C.U, C.leftErrorKernelNoDrift K a b ξ η * f η

variable {C}

/-- Fubini for the left parametrix against any test `g`:
`∫_U P₁ f · g = ∫_U (b f / c)(η) (∫_U a(ξ) Γ*(Θ(η, ξ)) g(ξ) dξ) dη`. -/
theorem integral_leftParametrix_mul_test_noDrift (hq : 0 < q) (ν₀ : G2.HomogeneousNorm C.G)
    (K : H1.FundamentalKernel C.G ((C.noDriftModel hq ν₀).reverseDrift C.G))
    (a b f g : TestFunction C.chartOpens ℝ (⊤ : ℕ∞)) :
    (∫ ξ in C.U, C.leftParametrixNoDrift K a b f ξ * g ξ) =
      ∫ η in C.U, (b η / C.c η * f η) * ∫ ξ in C.U, a ξ * K (C.Θ η ξ) * g ξ := by
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
  have hswap : (∫ ξ in C.U, ∫ η in C.U, (a ξ * g ξ) * (K : (Fin (n + m) → ℝ) → ℝ) (C.Θ η ξ) *
      (b η / C.c η * f η)) =
      ∫ η in C.U, ∫ ξ in C.U, (a ξ * g ξ) * (K : (Fin (n + m) → ℝ) → ℝ) (C.Θ η ξ) *
        (b η / C.c η * f η) :=
    (integrable_and_integral_swap_of_mass hU hKa hKb hKaU hKbU
      (κ := fun ξ η => (K : (Fin (n + m) → ℝ) → ℝ) (C.Θ η ξ)) (t := fun ξ => a ξ * g ξ)
      (w := fun η => b η / C.c η * f η) hκ ht₁c.continuousOn hwc ht₁0 hw0 hM₁ hmass₁).2
  have stepA : (∫ ξ in C.U, C.leftParametrixNoDrift K a b f ξ * g ξ) =
      ∫ ξ in C.U, ∫ η in C.U, (a ξ * g ξ) * (K : (Fin (n + m) → ℝ) → ℝ) (C.Θ η ξ) *
        (b η / C.c η * f η) := by
    refine setIntegral_congr_fun hUm (fun ξ _ => ?_)
    simp only [leftParametrixNoDrift]
    calc (a ξ * ∫ η in C.U, (K : (Fin (n + m) → ℝ) → ℝ) (C.Θ η ξ) * (b η / C.c η * f η)) * g ξ
        = (a ξ * g ξ) *
          ∫ η in C.U, (K : (Fin (n + m) → ℝ) → ℝ) (C.Θ η ξ) * (b η / C.c η * f η) := by ring
      _ = ∫ η in C.U, (a ξ * g ξ) *
          ((K : (Fin (n + m) → ℝ) → ℝ) (C.Θ η ξ) * (b η / C.c η * f η)) :=
          (integral_const_mul _ _).symm
      _ = _ := integral_congr_ae (Filter.Eventually.of_forall fun η => by ring)
  rw [stepA, hswap]
  refine setIntegral_congr_fun hUm (fun η _ => ?_)
  calc (∫ ξ in C.U, (a ξ * g ξ) * (K : (Fin (n + m) → ℝ) → ℝ) (C.Θ η ξ) * (b η / C.c η * f η))
      = ∫ ξ in C.U, (b η / C.c η * f η) * (a ξ * (K : (Fin (n + m) → ℝ) → ℝ) (C.Θ η ξ) * g ξ) :=
        integral_congr_ae (Filter.Eventually.of_forall fun ξ => by ring)
    _ = _ := integral_const_mul _ _

/-- Fubini for the error operator `E₁` against any test `g`:
`E₁ f · g` is integrable on `C.U` and
`∫_U (E₁ f) g = ∫_U (b f / c)(η) (∫_U e*(η, ξ) g(ξ) dξ) dη`, `e*(η, ξ) = leftErrBracket η ξ`;
the inner function of `η` is integrable. -/
theorem integral_leftError_mul_test_noDrift (hq : 0 < q) (ν₀ : G2.HomogeneousNorm C.G)
    (K : H1.FundamentalKernel C.G ((C.noDriftModel hq ν₀).reverseDrift C.G))
    (a b f g : TestFunction C.chartOpens ℝ (⊤ : ℕ∞)) :
    IntegrableOn (fun ξ => C.leftErrorNoDrift K a b f ξ * g ξ) C.U ∧
    IntegrableOn (fun η => (b η / C.c η * f η) * ∫ ξ in C.U, C.leftErrBracketNoDrift K a η ξ * g ξ)
      C.U ∧
    (∫ ξ in C.U, C.leftErrorNoDrift K a b f ξ * g ξ) =
      ∫ η in C.U, (b η / C.c η * f η) * ∫ ξ in C.U, C.leftErrBracketNoDrift K a η ξ * g ξ := by
  have hNZ : NeZero (n + m) := ⟨C.G.dimension_pos.ne'⟩
  have hU : IsOpen C.U := C.isOpen_U
  have hUm : MeasurableSet C.U := hU.measurableSet
  have haU : ContDiffOn ℝ (⊤ : ℕ∞) a C.U := a.contDiff.contDiffOn
  have hKg : IsCompact (tsupport (g : (Fin (n + m) → ℝ) → ℝ)) := g.hasCompactSupport
  have hKb : IsCompact (tsupport (b : (Fin (n + m) → ℝ) → ℝ)) := b.hasCompactSupport
  have hKgU : tsupport (g : (Fin (n + m) → ℝ) → ℝ) ⊆ C.U := g.tsupport_subset
  have hKbU : tsupport (b : (Fin (n + m) → ℝ) → ℝ) ⊆ C.U := b.tsupport_subset
  have hwc : ContinuousOn (fun η => b η / C.c η * f η) C.U :=
    (b.continuous.continuousOn.div C.density_smooth.continuousOn
      (fun η hη => (C.density_pos η hη).ne')).mul f.continuous.continuousOn
  have hw0 : ∀ η ∉ tsupport (b : (Fin (n + m) → ℝ) → ℝ), b η / C.c η * f η = 0 := fun η hη => by
    simp [image_eq_zero_of_notMem_tsupport hη]
  have hg0 : ∀ ξ ∉ tsupport (g : (Fin (n + m) → ℝ) → ℝ), g ξ = 0 := fun ξ hξ =>
    image_eq_zero_of_notMem_tsupport hξ
  obtain ⟨M₂, hM₂, hmass₂⟩ := exists_lintegral_bound_leftErrBracketNoDrift K hKg hKb hKgU hKbU haU
  have hsw := integrable_and_integral_swap_of_mass hU hKg hKb hKgU hKbU
    (κ := fun ξ η => C.leftErrBracketNoDrift K a η ξ) (t := g) (w := fun η => b η / C.c η * f η)
    (continuousOn_leftErrBracketNoDrift K haU) g.continuous.continuousOn hwc hg0 hw0 hM₂ hmass₂
  have hint : Integrable (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) =>
      g p.1 * C.leftErrBracketNoDrift K a p.2 p.1 * (b p.2 / C.c p.2 * f p.2))
      ((volume.restrict C.U).prod (volume.restrict C.U)) := hsw.1
  have hswap : (∫ ξ in C.U, ∫ η in C.U, g ξ * C.leftErrBracketNoDrift K a η ξ * (b η / C.c η * f η)) =
      ∫ η in C.U, ∫ ξ in C.U, g ξ * C.leftErrBracketNoDrift K a η ξ * (b η / C.c η * f η) := hsw.2
  have hE : ∀ ξ, (∫ η in C.U, g ξ * C.leftErrBracketNoDrift K a η ξ * (b η / C.c η * f η)) =
      C.leftErrorNoDrift K a b f ξ * g ξ := by
    intro ξ
    simp only [leftErrorNoDrift, leftErrorKernelNoDrift]
    calc (∫ η in C.U, g ξ * C.leftErrBracketNoDrift K a η ξ * (b η / C.c η * f η))
        = ∫ η in C.U, g ξ * (b η / C.c η * C.leftErrBracketNoDrift K a η ξ * f η) :=
          integral_congr_ae (Filter.Eventually.of_forall fun η => by ring)
      _ = g ξ * ∫ η in C.U, b η / C.c η * C.leftErrBracketNoDrift K a η ξ * f η :=
          integral_const_mul _ _
      _ = _ := mul_comm _ _
  have hin : ∀ η, (∫ ξ in C.U, g ξ * C.leftErrBracketNoDrift K a η ξ * (b η / C.c η * f η)) =
      (b η / C.c η * f η) * ∫ ξ in C.U, C.leftErrBracketNoDrift K a η ξ * g ξ := by
    intro η
    rw [mul_comm (b η / C.c η * f η), ← integral_mul_const]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ξ => by ring)
  refine ⟨(hint.integral_prod_left).congr (Filter.Eventually.of_forall fun ξ => hE ξ),
    (hint.integral_prod_right).congr (Filter.Eventually.of_forall fun η => hin η), ?_⟩
  calc (∫ ξ in C.U, C.leftErrorNoDrift K a b f ξ * g ξ)
      = ∫ ξ in C.U, ∫ η in C.U, g ξ * C.leftErrBracketNoDrift K a η ξ * (b η / C.c η * f η) :=
        (setIntegral_congr_fun hUm (fun ξ _ => hE ξ)).symm
    _ = ∫ η in C.U, ∫ ξ in C.U, g ξ * C.leftErrBracketNoDrift K a η ξ * (b η / C.c η * f η) := hswap
    _ = _ := setIntegral_congr_fun hUm (fun η _ => hin η)

/-- The signed identity `L̃* P₁ = M_a + E₁` in the sense of distributions on
tests: for the H1 fundamental kernel `Γ*` of the reversed no-drift model, tests `a, b, f, φ` on `C.U`
with `a b = a`, `(E₁ f) φ` is integrable on `C.U` and
`∫_U P₁ f · L̃φ = ∫_U a f φ + ∫_U (E₁ f) φ` (the pole computation: "the pole density `c(η)` is
canceled by `1/c(η)` in `P₁`, leaving `a b f = a f`; `E₁` is the sum of the positive-type
differential, divergence and cutoff errors"). -/
theorem integral_leftParametrix_mul_sumSquares_noDrift (hq : 0 < q) (ν₀ : G2.HomogeneousNorm C.G)
    (K : H1.FundamentalKernel C.G ((C.noDriftModel hq ν₀).reverseDrift C.G))
    (a b f φ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞)) (hab : ∀ ξ, a ξ * b ξ = a ξ) :
    IntegrableOn (fun ξ => C.leftErrorNoDrift K a b f ξ * φ ξ) C.U ∧
    (∫ ξ in C.U, C.leftParametrixNoDrift K a b f ξ * sumSquares C.Xl φ ξ) =
      (∫ ξ in C.U, a ξ * f ξ * φ ξ) + ∫ ξ in C.U, C.leftErrorNoDrift K a b f ξ * φ ξ := by
  have hU : IsOpen C.U := C.isOpen_U
  have hUm : MeasurableSet C.U := hU.measurableSet
  have haU : ContDiffOn ℝ (⊤ : ℕ∞) a C.U := a.contDiff.contDiffOn
  have hLφc : (sumSquaresTestNoDrift C.chartOpens C.Xl C.contDiffOn_Xl_U φ :
      (Fin (n + m) → ℝ) → ℝ) = sumSquares C.Xl φ :=
    sumSquaresTestNoDrift_coe C.chartOpens C.Xl C.contDiffOn_Xl_U φ
  obtain ⟨hI, hIw, hE⟩ := integral_leftError_mul_test_noDrift hq ν₀ K a b f φ
  have hF1 := integral_leftParametrix_mul_test_noDrift hq ν₀ K a b f
    (sumSquaresTestNoDrift C.chartOpens C.Xl C.contDiffOn_Xl_U φ)
  rw [hLφc] at hF1
  -- the pole limit for each `η`
  have stepC : ∀ η ∈ C.U, ((b η / C.c η * f η) *
      ∫ ξ in C.U, a ξ * K (C.Θ η ξ) * sumSquares C.Xl φ ξ) =
      (b η / C.c η * f η) * (C.c η * (a η * φ η)) +
        (b η / C.c η * f η) * ∫ ξ in C.U, C.leftErrBracketNoDrift K a η ξ * φ ξ := by
    intro η hη
    rw [(integral_kernel_comp_theta_mul_sumSquares_noDrift hq ν₀ K hη haU φ).2]
    ring
  have hI₁ : IntegrableOn (fun η => (b η / C.c η * f η) * (C.c η * (a η * φ η))) C.U := by
    have h1 : Continuous (fun η => a η * f η * φ η) :=
      (a.continuous.mul f.continuous).mul φ.continuous
    have h2 : HasCompactSupport (fun η => a η * f η * φ η) :=
      (a.hasCompactSupport.mul_right).mul_right
    refine (h1.integrable_of_hasCompactSupport h2).integrableOn.congr_fun (fun η hη => ?_) hUm
    have hc : C.c η ≠ 0 := (C.density_pos η hη).ne'
    have e : b η / C.c η * f η * (C.c η * (a η * φ η)) = (a η * b η) * f η * φ η := by
      field_simp
    show a η * f η * φ η = b η / C.c η * f η * (C.c η * (a η * φ η))
    rw [e, hab η]
  have hsplit : (∫ η in C.U, (b η / C.c η * f η) *
        ∫ ξ in C.U, a ξ * K (C.Θ η ξ) * sumSquares C.Xl φ ξ) =
      (∫ η in C.U, (b η / C.c η * f η) * (C.c η * (a η * φ η))) +
        ∫ η in C.U, (b η / C.c η * f η) * ∫ ξ in C.U, C.leftErrBracketNoDrift K a η ξ * φ ξ := by
    rw [← integral_add hI₁ hIw]
    exact setIntegral_congr_fun hUm stepC
  refine ⟨hI, ?_⟩
  rw [hF1, hsplit, hE]
  congr 1
  refine setIntegral_congr_fun hUm (fun η hη => ?_)
  have hc : C.c η ≠ 0 := (C.density_pos η hη).ne'
  have e : b η / C.c η * f η * (C.c η * (a η * φ η)) = (a η * b η) * f η * φ η := by
    field_simp
  show b η / C.c η * f η * (C.c η * (a η * φ η)) = a η * f η * φ η
  rw [e, hab η]

end LiftedChart

end RothschildStein.P1
