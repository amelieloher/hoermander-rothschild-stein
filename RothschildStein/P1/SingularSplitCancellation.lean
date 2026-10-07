-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.SingularSplitRadius
public import RothschildStein.H1.AssemblyInputs
public import Mathlib.MeasureTheory.Function.Jacobian

/-!
# Annular cancellation of `K₀`

For `ξ ∈ U` and `0 < r < t` with the model shell `{r < ν u < t}` contained in the image of
`η ↦ Θ(η, ξ)` on `U`, the substitution `u = Θ(η, ξ)` has the exact absolute Jacobian
`(c(ξ)(1 + ω₋(ξ, u)))⁻¹` (lifted-chart field `jacobian`), which cancels the denominator of
`K₀`:

`∫_{r < ρ(ξ,η) < t} K₀(ξ, η) dη = c(ξ) ∫_{r < ν u < t} (D^{ξ,ξ} Γ)(u) φ(ν u) du = 0`

by the weighted shell cancellation of H1 (`KernelShellCancellation`, BB Cor 6.31 as audited).
(BB p. 574, (11.58).) The integrability of `K₀` on the annulus is part of the
conclusion.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory
namespace RothschildStein.P1
namespace LiftedChart

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  (C : LiftedChart w s Ω hΩ X x₀ m)

/-- For `ξ ∈ U` the map `ζ ↦ Θ(ζ, ξ)` is smooth on `U`. -/
theorem contDiffOn_Θ_fst {ξ : Fin (n + m) → ℝ} (hξ : ξ ∈ C.U) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun ζ => C.Θ ζ ξ) C.U :=
  C.theta_smooth.comp (contDiffOn_id.prodMk contDiffOn_const) (fun _ hζ => ⟨hζ, hξ⟩)

/-- The Fréchet derivative of `ζ ↦ Θ(ζ, ξ)` exists at every `ζ ∈ U`. -/
theorem hasFDerivAt_Θ_fst {ξ ζ : Fin (n + m) → ℝ} (hξ : ξ ∈ C.U) (hζ : ζ ∈ C.U) :
    HasFDerivAt (fun ζ => C.Θ ζ ξ) (fderiv ℝ (fun ζ => C.Θ ζ ξ) ζ) ζ :=
  (((C.contDiffOn_Θ_fst hξ).differentiableOn (by simp)).differentiableAt
    (C.isOpen_U.mem_nhds hζ)).hasFDerivAt

/-- For `ξ ∈ U` the map `ζ ↦ Θ(ζ, ξ)` is injective on `U`: it is minus the chart
`e ξ`, by antisymmetry. -/
theorem injOn_Θ_fst {ξ : Fin (n + m) → ℝ} (hξ : ξ ∈ C.U) :
    InjOn (fun ζ => C.Θ ζ ξ) C.U := by
  intro a ha b hb hab
  obtain ⟨hsrc, hval, -, -, -⟩ := C.chart ξ hξ
  have h1 := C.theta_antisymm a ha ξ hξ
  have h2 := C.theta_antisymm b hb ξ hξ
  have hab' : C.Θ a ξ = C.Θ b ξ := hab
  have : C.e ξ a = C.e ξ b := by rw [hval a ha, hval b hb, h1, h2, hab']
  exact (C.e ξ).injOn (by rw [hsrc]; exact ha) (by rw [hsrc]; exact hb) this

/-- The annulus `{η ∈ U | r < ρ(ξ, η) < t}` is open when `ν` is continuous. -/
theorem isOpen_rhoAnnulus {ν : (Fin (n + m) → ℝ) → ℝ} (hν : Continuous ν)
    {ξ : Fin (n + m) → ℝ} (hξ : ξ ∈ C.U) (r t : ℝ) : IsOpen (C.rhoAnnulus ν ξ r t) := by
  have hc : ContinuousOn (fun η => ν (C.Θ η ξ)) C.U :=
    hν.comp_continuousOn (C.contDiffOn_Θ_fst hξ).continuousOn
  have h := hc.isOpen_inter_preimage C.isOpen_U (isOpen_Ioo (a := r) (b := t))
  convert h using 1
  ext η
  simp only [rhoAnnulus, rhoGauge, mem_inter_iff, mem_preimage, mem_Ioo, mem_ofPred_eq]

/-- Under the covering hypothesis (the model ball `{ν u < t}` lies in the image of
`η ↦ Θ(η, ξ)`), the chart image of the annulus is the full model shell
`{r < ν u < t}`. -/
theorem image_rhoAnnulus {ν : (Fin (n + m) → ℝ) → ℝ} {ξ : Fin (n + m) → ℝ} {r t : ℝ}
    (hcover : ∀ u, ν u < t → ∃ η ∈ C.U, C.Θ η ξ = u) :
    (fun ζ => C.Θ ζ ξ) '' C.rhoAnnulus ν ξ r t = {u | r < ν u ∧ ν u < t} := by
  ext u
  constructor
  · rintro ⟨ζ, ⟨-, h1, h2⟩, rfl⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    obtain ⟨η, hη, rfl⟩ := hcover u h2
    exact ⟨η, ⟨hη, h1, h2⟩, rfl⟩

/-- The absolute Jacobian `absoluteJacobian` is the absolute value of the determinant of the
Fréchet derivative. -/
theorem absoluteJacobian_eq_abs_det {N : ℕ} (f : (Fin N → ℝ) → (Fin N → ℝ)) (x : Fin N → ℝ) :
    absoluteJacobian f x = |(fderiv ℝ f x).det| := by
  unfold absoluteJacobian
  rw [LinearMap.det_toMatrix]

/-- Exact density cancellation: for `ξ ∈ U`, `0 < r < t`,
a degree-2 homogeneous `D^{ξ,ξ}` and a radial profile `φ` continuous on `[r, t]`,
`∫_{r < ρ(ξ,η) < t} K₀(ξ, η) dη = 0`, and `K₀(ξ, ·)` is integrable on the annulus. The
hypothesis `hcover` says the model ball `{ν u < t}` is covered by the chart, e.g. `t` below the
uniform image radius of `exists_gauge_image_radius` (BB p. 574, (11.58)). -/
theorem integral_splitK0_annulus {q : ℕ} {H : H1.StandingHypotheses C.G q}
    (Γ : H1.FundamentalKernel C.G H) (hΓ : H1.KernelShellCancellation Γ)
    (D : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → SmoothDifferentialOperator (n + m))
    (φ : ℝ → ℝ) {ξ : Fin (n + m) → ℝ} (hξ : ξ ∈ C.U) (hD : (D ξ ξ).IsHomogeneous C.G 2)
    {r t : ℝ} (hr : 0 < r) (hrt : r < t) (hφ : ContinuousOn φ (Icc r t))
    (hcover : ∀ u, H.norm u < t → ∃ η ∈ C.U, C.Θ η ξ = u) :
    IntegrableOn (C.splitK0 H.norm D Γ φ ξ) (C.rhoAnnulus H.norm ξ r t) ∧
      ∫ η in C.rhoAnnulus H.norm ξ r t, C.splitK0 H.norm D Γ φ ξ η = 0 := by
  have hν : Continuous H.norm := H.norm.gauge.1
  have hs : MeasurableSet (C.rhoAnnulus H.norm ξ r t) := (C.isOpen_rhoAnnulus hν hξ r t).measurableSet
  have hD' : ∀ ζ ∈ C.rhoAnnulus H.norm ξ r t,
      HasFDerivWithinAt (fun ζ => C.Θ ζ ξ) (fderiv ℝ (fun ζ => C.Θ ζ ξ) ζ)
        (C.rhoAnnulus H.norm ξ r t) ζ :=
    fun ζ hζ => (C.hasFDerivAt_Θ_fst hξ hζ.1).hasFDerivWithinAt
  have hinj : InjOn (fun ζ => C.Θ ζ ξ) (C.rhoAnnulus H.norm ξ r t) :=
    (C.injOn_Θ_fst hξ).mono (fun ζ hζ => hζ.1)
  have himg := C.image_rhoAnnulus (ν := H.norm) (ξ := ξ) (r := r) hcover
  obtain ⟨hint, hzero⟩ := hΓ (D ξ ξ) hD r t hr hrt φ hφ
  have hcξ : C.c ξ ≠ 0 := (C.density_pos ξ hξ).ne'
  let g : (Fin (n + m) → ℝ) → ℝ := fun u => C.c ξ * ((D ξ ξ).apply Γ u * φ (H.norm u))
  have hpt : ∀ ζ ∈ C.rhoAnnulus H.norm ξ r t,
      |(fderiv ℝ (fun ζ => C.Θ ζ ξ) ζ).det| • g (C.Θ ζ ξ) = C.splitK0 H.norm D Γ φ ξ ζ := by
    intro ζ hζ
    have hj := (C.jacobian ζ hζ.1 ξ hξ).2.2.2
    rw [absoluteJacobian_eq_abs_det] at hj
    have hω : 1 + C.ωm ξ (C.Θ ζ ξ) ≠ 0 := (C.jacobian ζ hζ.1 ξ hξ).2.1.ne'
    simp only [smul_eq_mul, g]
    rw [hj]
    unfold splitK0 cutoffKernel
    field_simp
  have hg : IntegrableOn g ((fun ζ => C.Θ ζ ξ) '' C.rhoAnnulus H.norm ξ r t) := by
    rw [himg]
    exact hint.const_mul _
  have hI := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume hs hD' hinj g).mp hg
  refine ⟨hI.congr_fun hpt hs, ?_⟩
  have hch := integral_image_eq_integral_abs_det_fderiv_smul volume hs hD' hinj g
  rw [himg, integral_const_mul, hzero, mul_zero] at hch
  rw [← setIntegral_congr_fun hs hpt]
  exact hch.symm

/-- `K₀` vanishes where the radial profile does: `φ (ρ(ξ, η)) = 0 → K₀(ξ, η) = 0`. -/
theorem splitK0_eq_zero_of_profile {ν : (Fin (n + m) → ℝ) → ℝ}
    {D : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → SmoothDifferentialOperator (n + m)}
    {Γ : (Fin (n + m) → ℝ) → ℝ} {φ : ℝ → ℝ} {ξ η : Fin (n + m) → ℝ}
    (h : φ (C.rhoGauge ν ξ η) = 0) : C.splitK0 ν D Γ φ ξ η = 0 := by
  unfold splitK0 cutoffKernel
  rw [show ν (C.Θ η ξ) = C.rhoGauge ν ξ η from rfl, h, mul_zero, zero_div]

/-- With the radial profile continuous and
vanishing beyond `R₀`, and the model ball `{ν u < R₀}` covered by the chart, the cancellation
`∫_{r < ρ(ξ,η) < t} K₀ dη = 0` holds for every `0 < r < t`, not only for `t ≤ R₀`: the integrand
vanishes where `ρ ≥ R₀` (BB p. 574; this is the form needed for Data D3). -/
theorem integral_splitK0_annulus_of_support {q : ℕ} {H : H1.StandingHypotheses C.G q}
    (Γ : H1.FundamentalKernel C.G H) (hΓ : H1.KernelShellCancellation Γ)
    (D : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → SmoothDifferentialOperator (n + m))
    {φ : ℝ → ℝ} (hφc : Continuous φ) {R₀ : ℝ} (hφs : ∀ s, R₀ < s → φ s = 0)
    {ξ : Fin (n + m) → ℝ} (hξ : ξ ∈ C.U) (hD : (D ξ ξ).IsHomogeneous C.G 2)
    (hcover : ∀ u, H.norm u < R₀ → ∃ η ∈ C.U, C.Θ η ξ = u)
    {r t : ℝ} (hr : 0 < r) (hrt : r < t) :
    IntegrableOn (C.splitK0 H.norm D Γ φ ξ) (C.rhoAnnulus H.norm ξ r t) ∧
      ∫ η in C.rhoAnnulus H.norm ξ r t, C.splitK0 H.norm D Γ φ ξ η = 0 := by
  have hν : Continuous H.norm := H.norm.gauge.1
  have hs : MeasurableSet (C.rhoAnnulus H.norm ξ r t) := (C.isOpen_rhoAnnulus hν hξ r t).measurableSet
  -- the profile vanishes at `R₀` and beyond, by continuity
  have hφ0 : ∀ x, R₀ ≤ x → φ x = 0 := by
    intro x hx
    rcases hx.eq_or_lt with h | hlt
    · rw [← h]
      have h1 : Filter.Tendsto φ (nhdsWithin R₀ (Ioi R₀)) (nhds (φ R₀)) :=
        hφc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
      have h2 : Filter.Tendsto φ (nhdsWithin R₀ (Ioi R₀)) (nhds 0) :=
        tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall (fun y hy => (hφs y hy).symm))
      exact tendsto_nhds_unique h1 h2
    · exact hφs x hlt
  have hz : ∀ ζ, R₀ ≤ C.rhoGauge H.norm ξ ζ → C.splitK0 H.norm D Γ φ ξ ζ = 0 :=
    fun ζ hζ => C.splitK0_eq_zero_of_profile (hφ0 _ hζ)
  by_cases hrR : r < R₀
  · have hmain := C.integral_splitK0_annulus Γ hΓ D φ hξ hD hr (lt_min hrt hrR)
      hφc.continuousOn (fun u hu => hcover u (hu.trans_le (min_le_right _ _)))
    have hsub : C.rhoAnnulus H.norm ξ r (min t R₀) ⊆ C.rhoAnnulus H.norm ξ r t :=
      fun ζ hζ => ⟨hζ.1, hζ.2.1, hζ.2.2.trans_le (min_le_left _ _)⟩
    have hdiff : ∀ ζ ∈ C.rhoAnnulus H.norm ξ r t \ C.rhoAnnulus H.norm ξ r (min t R₀),
        C.splitK0 H.norm D Γ φ ξ ζ = 0 := by
      rintro ζ ⟨⟨hζU, hζ1, hζ2⟩, hnot⟩
      apply hz
      by_contra hlt
      exact hnot ⟨hζU, hζ1, lt_min hζ2 (not_le.mp hlt)⟩
    refine ⟨hmain.1.of_forall_sdiff_eq_zero hs hdiff, ?_⟩
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero hs hsub hdiff]
    exact hmain.2
  · have hall : ∀ ζ ∈ C.rhoAnnulus H.norm ξ r t, C.splitK0 H.norm D Γ φ ξ ζ = 0 :=
      fun ζ hζ => hz ζ ((not_lt.mp hrR).trans hζ.2.1.le)
    refine ⟨(integrableOn_zero).congr_fun (fun ζ hζ => (hall ζ hζ).symm) hs, ?_⟩
    rw [setIntegral_congr_fun hs hall]
    simp

end LiftedChart
end RothschildStein.P1
