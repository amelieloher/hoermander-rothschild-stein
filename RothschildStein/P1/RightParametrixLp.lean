-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.RightParametrix

/-!
# The signed right parametrix identity for locally integrable inputs

The signed identity `L̃ P_R f = a f - F_R^chart f` of `RightParametrix`
(`integral_rightParametrix_mul_transpose_chartError`) is proved there for a *test* input `f`. The
proof only uses the input through `w = (b / c) f`, to know that the product
`t(ξ) κ(ξ, η) w(η)` is integrable for the kernels `κ` of the pole and error terms (Fubini) and that
`a f φ` is integrable. Both follow when `f` is merely locally integrable on the chart domain `V`:

* `integrable_prod_of_mass_bound_of_integrable`: if the lower integrals of `κ(·, η)` over `Kt` are
  uniformly bounded for `η ∈ Kw`, `t` is bounded and supported in `Kt`, and `w` is integrable and
  supported in `Kw`, then `t(ξ) κ(ξ, η) w(η)` is integrable on the product;
* `integral_rightParametrix_mul_transpose_of_locallyIntegrable`: for tests `a, b, φ` with
  `a b = a` and `f` locally integrable on `C.U`,
  `∫_U P_R f · L̃ᵀφ = ∫_U a f φ + ∫_U (E_R f) φ` (and `(E_R f) φ` is integrable);
* `integral_rightParametrix_mul_transpose_chartError_of_locallyIntegrable`: with
  `F_R^chart = -E_R`, `∫_U P_R f · L̃ᵀφ = ∫_U (a f - F_R^chart f) φ`, i.e. `M_a = L̃ P_R + F_R^chart`;
* `locallyIntegrableOn_of_memLp`: `f ∈ L^p(U)`, `1 ≤ p ≤ ∞`, is locally integrable on the open `U`.

In particular, the identity holds for every `f ∈ L^p(V)`, `1 ≤ p ≤ ∞`. The same conclusion
can also be reached by test approximation `f_n → f` in `L^p` and the
`L^p` continuity of `P_R` and `F_R^chart`; here the density step is replaced by running Fubini on
the identity directly for the integrable input, which needs only the *column* integral bounds of
the kernels already used on tests (`RightParametrixMass`) and no Schur estimate.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology ENNReal
namespace RothschildStein.P1

section Product

variable {N : ℕ}

/-- Integrability on the product of `t(ξ) κ(ξ, η) w(η)` from a uniform
bound of the lower integrals of `κ(·, η)` over the support `Kt` of the bounded factor `t`, for `η`
in the support `Kw` of the *integrable* factor `w` (the version of `integrable_prod_of_mass_bound`
without a bound on `w`). -/
theorem integrable_prod_of_mass_bound_of_integrable [NeZero N] {U Kt Kw : Set (Fin N → ℝ)}
    (hKtU : Kt ⊆ U) (hKwU : Kw ⊆ U) (hKt : MeasurableSet Kt) (hKw : MeasurableSet Kw)
    {κ : (Fin N → ℝ) → (Fin N → ℝ) → ℝ} {t w : (Fin N → ℝ) → ℝ} {Bt : ℝ}
    (hκ : AEStronglyMeasurable (fun p : (Fin N → ℝ) × (Fin N → ℝ) => κ p.1 p.2)
      ((volume.restrict U).prod (volume.restrict U)))
    (ht : AEStronglyMeasurable t (volume.restrict U))
    (hw : AEStronglyMeasurable w (volume.restrict U))
    (htB : ∀ ξ ∈ Kt, |t ξ| ≤ Bt) (hwI : ∫⁻ η in Kw, ‖w η‖ₑ < ⊤)
    (ht0 : ∀ ξ ∉ Kt, t ξ = 0) (hw0 : ∀ η ∉ Kw, w η = 0) {M : ℝ≥0∞} (hM : M < ⊤)
    (hmass : ∀ η ∈ Kw, ∫⁻ ξ in Kt, ‖κ ξ η‖ₑ ≤ M) :
    Integrable (fun p : (Fin N → ℝ) × (Fin N → ℝ) => t p.1 * κ p.1 p.2 * w p.2)
      ((volume.restrict U).prod (volume.restrict U)) := by
  set μ : Measure (Fin N → ℝ) := volume.restrict U with hμ
  have h1 : AEStronglyMeasurable (fun p : (Fin N → ℝ) × (Fin N → ℝ) => t p.1) (μ.prod μ) :=
    ht.comp_fst
  have h2 : AEStronglyMeasurable (fun p : (Fin N → ℝ) × (Fin N → ℝ) => w p.2) (μ.prod μ) :=
    hw.comp_snd
  have hmeas : AEStronglyMeasurable (fun p : (Fin N → ℝ) × (Fin N → ℝ) =>
      t p.1 * κ p.1 p.2 * w p.2) (μ.prod μ) := (h1.mul hκ).mul h2
  refine ⟨hmeas, ?_⟩
  unfold HasFiniteIntegral
  rw [lintegral_prod_symm _ hmeas.enorm]
  have hinner : ∀ η : Fin N → ℝ, ∫⁻ ξ, ‖t ξ * κ ξ η * w η‖ₑ ∂μ ≤
      Kw.indicator (fun η => ENNReal.ofReal Bt * M * ‖w η‖ₑ) η := by
    intro η
    by_cases hη : η ∈ Kw
    · rw [Set.indicator_of_mem hη]
      have h1 : ∀ ξ, ‖t ξ * κ ξ η * w η‖ₑ ≤
          Kt.indicator (fun ξ => ENNReal.ofReal Bt * ‖w η‖ₑ * ‖κ ξ η‖ₑ) ξ := by
        intro ξ
        by_cases hξ : ξ ∈ Kt
        · rw [Set.indicator_of_mem hξ, enorm_mul, enorm_mul]
          have e1 : ‖t ξ‖ₑ ≤ ENNReal.ofReal Bt := by
            rw [Real.enorm_eq_ofReal_abs]
            exact ENNReal.ofReal_le_ofReal (htB ξ hξ)
          calc ‖t ξ‖ₑ * ‖κ ξ η‖ₑ * ‖w η‖ₑ ≤ ENNReal.ofReal Bt * ‖κ ξ η‖ₑ * ‖w η‖ₑ := by
                gcongr
            _ = ENNReal.ofReal Bt * ‖w η‖ₑ * ‖κ ξ η‖ₑ := by ring
        · rw [Set.indicator_of_notMem hξ, ht0 ξ hξ]
          simp
      calc ∫⁻ ξ, ‖t ξ * κ ξ η * w η‖ₑ ∂μ
          ≤ ∫⁻ ξ, Kt.indicator (fun ξ => ENNReal.ofReal Bt * ‖w η‖ₑ * ‖κ ξ η‖ₑ) ξ ∂μ :=
            lintegral_mono h1
        _ = ∫⁻ ξ in Kt, ENNReal.ofReal Bt * ‖w η‖ₑ * ‖κ ξ η‖ₑ ∂μ :=
            lintegral_indicator hKt _
        _ = ∫⁻ ξ in Kt, ENNReal.ofReal Bt * ‖w η‖ₑ * ‖κ ξ η‖ₑ := by
            rw [hμ, Measure.restrict_restrict hKt, inter_eq_left.2 hKtU]
        _ = ENNReal.ofReal Bt * ‖w η‖ₑ * ∫⁻ ξ in Kt, ‖κ ξ η‖ₑ :=
            lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top enorm_ne_top)
        _ ≤ ENNReal.ofReal Bt * ‖w η‖ₑ * M := by gcongr; exact hmass η hη
        _ = ENNReal.ofReal Bt * M * ‖w η‖ₑ := by ring
    · rw [Set.indicator_of_notMem hη, hw0 η hη]
      simp
  calc ∫⁻ η, ∫⁻ ξ, ‖t ξ * κ ξ η * w η‖ₑ ∂μ ∂μ
      ≤ ∫⁻ η, Kw.indicator (fun η => ENNReal.ofReal Bt * M * ‖w η‖ₑ) η ∂μ :=
        lintegral_mono hinner
    _ = ∫⁻ η in Kw, ENNReal.ofReal Bt * M * ‖w η‖ₑ ∂μ := lintegral_indicator hKw _
    _ = ∫⁻ η in Kw, ENNReal.ofReal Bt * M * ‖w η‖ₑ := by
        rw [hμ, Measure.restrict_restrict hKw, inter_eq_left.2 hKwU]
    _ = ENNReal.ofReal Bt * M * ∫⁻ η in Kw, ‖w η‖ₑ :=
        lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hM.ne)
    _ < ⊤ := ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hM) hwI

/-- A function of `L^p(U)`, `1 ≤ p ≤ ∞`, is locally integrable on
the open set `U` (it is integrable on every compact subset of `U`). -/
theorem locallyIntegrableOn_of_memLp {U : Set (Fin N → ℝ)} (hU : IsOpen U) {p : ℝ≥0∞}
    (hp : 1 ≤ p) {f : (Fin N → ℝ) → ℝ} (hf : MemLp f p (volume.restrict U)) :
    LocallyIntegrableOn f U := by
  rw [locallyIntegrableOn_iff hU.isLocallyClosed]
  intro k hkU hk
  have h := (hf.locallyIntegrable hp).integrableOn_isCompact hk
  rwa [IntegrableOn, Measure.restrict_restrict_of_subset hkU] at h

end Product

namespace LiftedChart

variable {n q s m : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart (fun i : Fin (q + 1) => if i = 0 then (2 : ℕ+) else 1) s Ω hΩ X x₀ m}

/-- For tests `a, φ` of the chart and `f` locally integrable on
`C.U`, `a f φ` is integrable on `C.U` (`a` has compact support in `C.U`). -/
theorem integrableOn_cutoff_mul_test (a φ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞))
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
theorem integral_rightParametrix_mul_transpose_of_locallyIntegrable (hq : 0 < q)
    (ν₀ : G2.HomogeneousNorm C.G) (K : H1.FundamentalKernel C.G (C.driftModel hq ν₀))
    (a b φ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞)) {f : (Fin (n + m) → ℝ) → ℝ}
    (hf : LocallyIntegrableOn f C.U) (hab : ∀ ξ, a ξ * b ξ = a ξ) :
    IntegrableOn (fun ξ => C.rightError K a b f ξ * φ ξ) C.U ∧
    (∫ ξ in C.U, C.rightParametrix K a b f ξ * sumSquaresWithDriftTranspose C.Xl φ ξ) =
      (∫ ξ in C.U, a ξ * f ξ * φ ξ) + ∫ ξ in C.U, C.rightError K a b f ξ * φ ξ := by
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
  have hT : Continuous (sumSquaresWithDriftTranspose C.Xl φ) := by
    have e := sumSquaresWithDriftTransposeTest_coe C.chartOpens C.Xl C.contDiffOn_Xl_U φ
    rw [← e]
    exact (sumSquaresWithDriftTransposeTest C.chartOpens C.Xl C.contDiffOn_Xl_U φ).continuous
  set t₁ : (Fin (n + m) → ℝ) → ℝ := fun ξ => a ξ * sumSquaresWithDriftTranspose C.Xl φ ξ with ht₁
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
      (K.smooth_off_zero.continuousOn.comp contDiffOn_theta_swap.continuousOn
        (fun p hp => C.theta_ne_zero hp.2.1 hp.1 hp.2.2))
  have hκ₂ : AEStronglyMeasurable (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) =>
      C.errBracket K a p.2 p.1) ((volume.restrict C.U).prod (volume.restrict C.U)) :=
    aestronglyMeasurable_prod_of_continuousOn hU (continuousOn_errBracket K haU)
  obtain ⟨M₁, hM₁, hmass₁⟩ := exists_lintegral_bound_kernel hq ν₀ K hKa hKb hKaU hKbU
  obtain ⟨M₂, hM₂, hmass₂⟩ := exists_lintegral_bound_errBracket hq ν₀ K hKφ hKb hKφU hKbU haU
  have hint₁ : Integrable (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) =>
      t₁ p.1 * (K : (Fin (n + m) → ℝ) → ℝ) (C.Θ p.2 p.1) * w p.2)
      ((volume.restrict C.U).prod (volume.restrict C.U)) :=
    integrable_prod_of_mass_bound_of_integrable (κ := fun ξ η => (K : (Fin (n + m) → ℝ) → ℝ) (C.Θ η ξ))
      hKaU hKbU hKa.isClosed.measurableSet hKb.isClosed.measurableSet hκ₁
      ht₁c.aestronglyMeasurable hw_meas (fun ξ _ => by simpa [Real.norm_eq_abs] using hBt₁ ξ)
      hwI ht₁0 hw0 hM₁ hmass₁
  have hint₂ : Integrable (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) =>
      φ p.1 * C.errBracket K a p.2 p.1 * w p.2)
      ((volume.restrict C.U).prod (volume.restrict C.U)) :=
    integrable_prod_of_mass_bound_of_integrable (κ := fun ξ η => C.errBracket K a η ξ)
      hKφU hKbU hKφ.isClosed.measurableSet hKb.isClosed.measurableSet hκ₂
      φ.continuous.aestronglyMeasurable hw_meas
      (fun ξ _ => by simpa [Real.norm_eq_abs] using hBt₂ ξ) hwI ht₂0 hw0 hM₂ hmass₂
  -- Step A: the left side as an iterated integral
  have stepA : (∫ ξ in C.U, C.rightParametrix K a b f ξ * sumSquaresWithDriftTranspose C.Xl φ ξ) =
      ∫ ξ in C.U, ∫ η in C.U, t₁ ξ * (K : (Fin (n + m) → ℝ) → ℝ) (C.Θ η ξ) * w η := by
    refine setIntegral_congr_fun hUm (fun ξ _ => ?_)
    simp only [rightParametrix]
    calc (a ξ * ∫ η in C.U, (K : (Fin (n + m) → ℝ) → ℝ) (C.Θ η ξ) * (b η / C.c η * f η)) *
          sumSquaresWithDriftTranspose C.Xl φ ξ
        = (a ξ * sumSquaresWithDriftTranspose C.Xl φ ξ) *
          ∫ η in C.U, (K : (Fin (n + m) → ℝ) → ℝ) (C.Θ η ξ) * (b η / C.c η * f η) := by ring
      _ = ∫ η in C.U, (a ξ * sumSquaresWithDriftTranspose C.Xl φ ξ) *
          ((K : (Fin (n + m) → ℝ) → ℝ) (C.Θ η ξ) * (b η / C.c η * f η)) :=
          (integral_const_mul _ _).symm
      _ = ∫ η in C.U, t₁ ξ * (K : (Fin (n + m) → ℝ) → ℝ) (C.Θ η ξ) * w η :=
          integral_congr_ae (Filter.Eventually.of_forall fun η => by simp only [ht₁, hw]; ring)
  -- Step B: Fubini for the kernel
  have stepB := integral_integral_swap (μ := volume.restrict C.U) (ν := volume.restrict C.U)
    (f := fun ξ η => t₁ ξ * (K : (Fin (n + m) → ℝ) → ℝ) (C.Θ η ξ) * w η) hint₁
  -- Step C: the pole limit for each `η`
  have stepC : ∀ η ∈ C.U, (∫ ξ in C.U, t₁ ξ * (K : (Fin (n + m) → ℝ) → ℝ) (C.Θ η ξ) * w η) =
      w η * (C.c η * (a η * φ η)) + w η * ∫ ξ in C.U, C.errBracket K a η ξ * φ ξ := by
    intro η hη
    have h := (integral_kernel_comp_theta_mul_transpose hq ν₀ K hη haU φ).2
    calc (∫ ξ in C.U, t₁ ξ * (K : (Fin (n + m) → ℝ) → ℝ) (C.Θ η ξ) * w η)
        = ∫ ξ in C.U, w η * (a ξ * (K : (Fin (n + m) → ℝ) → ℝ) (C.Θ η ξ) *
            sumSquaresWithDriftTranspose C.Xl φ ξ) :=
          integral_congr_ae (Filter.Eventually.of_forall fun ξ => by simp only [ht₁]; ring)
      _ = w η * ∫ ξ in C.U, a ξ * (K : (Fin (n + m) → ℝ) → ℝ) (C.Θ η ξ) *
            sumSquaresWithDriftTranspose C.Xl φ ξ := integral_const_mul _ _
      _ = w η * (C.c η * (a η * φ η) + ∫ ξ in C.U, C.errBracket K a η ξ * φ ξ) := by
          rw [h]
          rfl
      _ = _ := by ring
  -- integrability of the two terms of Step C
  have hI₁ : IntegrableOn (fun η => w η * (C.c η * (a η * φ η))) C.U := by
    refine (integrableOn_cutoff_mul_test a φ hf).congr_fun (fun η hη => ?_) hUm
    have hc : C.c η ≠ 0 := (C.density_pos η hη).ne'
    have e : b η / C.c η * f η * (C.c η * (a η * φ η)) = (a η * b η) * f η * φ η := by
      field_simp
    show a η * f η * φ η = b η / C.c η * f η * (C.c η * (a η * φ η))
    rw [e, hab η]
  have hI₂ : IntegrableOn (fun η => w η * ∫ ξ in C.U, C.errBracket K a η ξ * φ ξ) C.U := by
    refine (hint₂.integral_prod_right).congr (Filter.Eventually.of_forall fun η => ?_)
    show ∫ ξ in C.U, φ ξ * C.errBracket K a η ξ * w η =
      w η * ∫ ξ in C.U, C.errBracket K a η ξ * φ ξ
    rw [mul_comm (w η), ← integral_mul_const]
    exact integral_congr_ae (Filter.Eventually.of_forall fun ξ => by ring)
  have stepD : (∫ η in C.U, ∫ ξ in C.U, t₁ ξ * (K : (Fin (n + m) → ℝ) → ℝ) (C.Θ η ξ) * w η) =
      (∫ η in C.U, w η * (C.c η * (a η * φ η))) +
        ∫ η in C.U, w η * ∫ ξ in C.U, C.errBracket K a η ξ * φ ξ := by
    rw [← integral_add hI₁ hI₂]
    exact setIntegral_congr_fun hUm stepC
  -- Step E: Fubini for the error kernel
  have h1 : (∫ η in C.U, w η * ∫ ξ in C.U, C.errBracket K a η ξ * φ ξ) =
      ∫ η in C.U, ∫ ξ in C.U, φ ξ * C.errBracket K a η ξ * w η := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun η => ?_)
    show w η * ∫ ξ in C.U, C.errBracket K a η ξ * φ ξ =
      ∫ ξ in C.U, φ ξ * C.errBracket K a η ξ * w η
    rw [mul_comm (w η), ← integral_mul_const]
    exact (integral_congr_ae (Filter.Eventually.of_forall fun ξ => by ring)).symm
  have h2 := (integral_integral_swap (μ := volume.restrict C.U) (ν := volume.restrict C.U)
    (f := fun ξ η => φ ξ * C.errBracket K a η ξ * w η) hint₂).symm
  have hE : ∀ ξ, (∫ η in C.U, φ ξ * C.errBracket K a η ξ * w η) =
      C.rightError K a b f ξ * φ ξ := by
    intro ξ
    simp only [rightError, rightErrorKernel]
    calc (∫ η in C.U, φ ξ * C.errBracket K a η ξ * w η)
        = ∫ η in C.U, φ ξ * (b η / C.c η * C.errBracket K a η ξ * f η) :=
          integral_congr_ae (Filter.Eventually.of_forall fun η => by simp only [hw]; ring)
      _ = φ ξ * ∫ η in C.U, b η / C.c η * C.errBracket K a η ξ * f η := integral_const_mul _ _
      _ = _ := mul_comm _ _
  have stepE : (∫ η in C.U, w η * ∫ ξ in C.U, C.errBracket K a η ξ * φ ξ) =
      ∫ ξ in C.U, C.rightError K a b f ξ * φ ξ := by
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
theorem integral_rightParametrix_mul_transpose_chartError_of_locallyIntegrable (hq : 0 < q)
    (ν₀ : G2.HomogeneousNorm C.G) (K : H1.FundamentalKernel C.G (C.driftModel hq ν₀))
    (a b φ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞)) {f : (Fin (n + m) → ℝ) → ℝ}
    (hf : LocallyIntegrableOn f C.U) (hab : ∀ ξ, a ξ * b ξ = a ξ) :
    (∫ ξ in C.U, C.rightParametrix K a b f ξ * sumSquaresWithDriftTranspose C.Xl φ ξ) =
      ∫ ξ in C.U, (a ξ * f ξ - C.rightChartError K a b f ξ) * φ ξ := by
  obtain ⟨hI, h⟩ := integral_rightParametrix_mul_transpose_of_locallyIntegrable hq ν₀ K a b φ hf
    hab
  have hI' : IntegrableOn (fun ξ => a ξ * f ξ * φ ξ) C.U := integrableOn_cutoff_mul_test a φ hf
  rw [h, ← integral_add hI' hI]
  refine setIntegral_congr_fun C.isOpen_U.measurableSet (fun ξ _ => ?_)
  simp only [rightChartError]
  ring

end LiftedChart

end RothschildStein.P1
