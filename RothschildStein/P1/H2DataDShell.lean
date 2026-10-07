-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.H2DataDMeasurable

/-!
# Data D1 and D3 on the doubled ball: support and shell cancellation

* **D1** (`carrierKernel_eq_zero_of_le_d'`): a kernel that carries the radial profile factor
  `φ(ρ)`, with `φ = 0` on `[R', ∞)`, vanishes on the carrier where `d'(x, y) ≥ R'`, since
  `d' < R'` forces `d' = ρ < R'` (the truncation certificate and `IsAdmissibleRadius`).
* **D3** (`integral_carrierKernel_splitK0_shell`): for `x ∈ U_j = B(z, r)` and *every*
  `0 < t₁ < t₂ < ∞`,
  `∫_{y ∈ U_j^{(2)}, t₁ < d'(x,y) < t₂} K₀(x, y) dy = 0`. The integrand is
  supported in `d' < R'`, where `d' = ρ` and the shell lies in `B(x, r/4) ⊆ U_j^{(2)}`; so the
  carrier integral is the ambient integral over `{t₁ < ρ(x, η) < t₂}`, the annular cancellation of
  `K₀` (`integral_splitK0_annulus_of_support`, BB Thm 11.5(d) with the Jacobian cancellation) holds for
 every `t₂`, since the radial profile vanishes beyond `R'` (BB p. 574, (11.58)). The transposed splitting has its own cancellation (`integral_..._transpose_shell`); none is
  claimed for the raw `K₀ᵗ`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set Metric MeasureTheory
namespace RothschildStein.P1
namespace LiftedChart

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  {C : LiftedChart w s Ω hΩ X x₀ m}

/-- Integrals over carrier sets are integrals over their images in the ambient
space: the measure of the carrier is the restriction of Lebesgue measure to `U`. -/
theorem setIntegral_carrier_eq_image (g : (Fin (n + m) → ℝ) → ℝ) {B : Set C.Carrier}
    (hB : MeasurableSet B) :
    ∫ y in B, g y.val ∂(volume : Measure C.Carrier) = ∫ ξ in Carrier.val '' B, g ξ := by
  have hemb := Carrier.measurableEmbedding_val (C := C)
  have hmap : Measure.map Carrier.val (volume : Measure C.Carrier) =
      volume.restrict (range (Carrier.val : C.Carrier → Fin (n + m) → ℝ)) := by
    show Measure.map Carrier.val (Measure.comap Carrier.val volume) = _
    exact hemb.map_comap volume
  have h1 := hemb.setIntegral_map (μ := (volume : Measure C.Carrier)) g (Carrier.val '' B)
  rw [hmap, Measure.restrict_restrict (hemb.measurableSet_image.mpr hB),
    inter_eq_left.mpr (image_subset_range _ _), preimage_image_eq _ Carrier.val_injective] at h1
  exact h1.symm

/-- A kernel of the carrier that carries the radial profile as a factor
(`κ ξ η = 0` as soon as `φ(ν(Θ(η, ξ))) = 0`, `φ = 0` on `[R', ∞)`) and is nonzero at `(x, y)`
satisfies `x ≠ y`, `d'(x, y) < R'` and `d'(x, y) = ρ(x, y)`. -/
theorem carrierKernel_ne_zero_imp {ν : (Fin (n + m) → ℝ) → ℝ} {φ : ℝ → ℝ} {R' r τ : ℝ}
    {κ : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ}
    (hκ : ∀ ξ η, φ (ν (C.Θ η ξ)) = 0 → κ ξ η = 0) (hφ0 : ∀ t, R' ≤ t → φ t = 0)
    {S : H2.LocDoubling C.Carrier} {T : H2.TruncDist S} (hT : C.IsRhoTruncation S ν τ T)
    (hR : C.IsAdmissibleRadius S T ν τ r R') {x y : C.Carrier}
    (h : C.carrierKernel κ x y ≠ 0) :
    x ≠ y ∧ T.d' x y < R' ∧ T.d' x y = C.rho ν x y := by
  have hxy : x ≠ y := by
    rintro rfl
    exact h (carrierKernel_self _)
  have hy' : κ x.val y.val ≠ 0 := by
    rwa [carrierKernel_of_ne hxy] at h
  have hφy : φ (ν (C.Θ y.val x.val)) ≠ 0 := fun h0 => hy' (hκ _ _ h0)
  have hρ : C.rho ν x y < R' := by
    by_contra hcon
    exact hφy (hφ0 _ (not_lt.mp hcon))
  have hd' : T.d' x y < R' := (hR.d'_lt_iff_rho_lt hT).mpr hρ
  refine ⟨hxy, hd', hT.near x y ?_⟩
  have hθ := T.θ₁_pos
  have h1 := hR.lt_trunc
  have h2 := hR.pos
  exact hT.dist_lt_of_d'_lt (by linarith)

/-- **Data D1.** Such a kernel vanishes on the carrier where
`d'(x, y) ≥ R'`. -/
theorem carrierKernel_eq_zero_of_le_d' {ν : (Fin (n + m) → ℝ) → ℝ} {φ : ℝ → ℝ} {R' r τ : ℝ}
    {κ : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ}
    (hκ : ∀ ξ η, φ (ν (C.Θ η ξ)) = 0 → κ ξ η = 0) (hφ0 : ∀ t, R' ≤ t → φ t = 0)
    {S : H2.LocDoubling C.Carrier} {T : H2.TruncDist S} (hT : C.IsRhoTruncation S ν τ T)
    (hR : C.IsAdmissibleRadius S T ν τ r R') {x y : C.Carrier} (h : R' ≤ T.d' x y) :
    C.carrierKernel κ x y = 0 := by
  by_contra hne
  have := (carrierKernel_ne_zero_imp hκ hφ0 hT hR hne).2.1
  linarith

/-- **Data D3** (shell cancellation). For `x ∈ U_j = B(z, r)` and every `0 < t₁ < t₂`,
the carrier integral of `K₀ = splitK0` over the shell `{y ∈ U_j^{(2)} : t₁ < d'(x, y) < t₂}`
vanishes (BB p. 574, (11.58); the shell beyond `R'` meets the support only inside `d' < R'`). -/
theorem integral_carrierKernel_splitK0_shell {q : ℕ} {H : H1.StandingHypotheses C.G q}
    (Γ : H1.FundamentalKernel C.G H) (hΓ : H1.KernelShellCancellation Γ)
    {D : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → SmoothDifferentialOperator (n + m)}
    (hD : ∀ ξ ∈ C.U, (D ξ ξ).IsHomogeneous C.G 2)
    {φ : ℝ → ℝ} (hφc : Continuous φ) {R' : ℝ} (hφ0 : ∀ t, R' ≤ t → φ t = 0)
    {S : H2.LocDoubling C.Carrier} {τ : ℝ} {T : H2.TruncDist S}
    (hT : C.IsRhoTruncation S H.norm τ T) {r : ℝ}
    (hR : C.IsAdmissibleRadius S T H.norm τ r R') (hr : 0 < r)
    {z x : C.Carrier} (hx : x ∈ ball z r) (hxΩ : x ∈ closure S.Ω₂)
    {t₁ t₂ : ℝ} (ht₁ : 0 < t₁) (ht : t₁ < t₂) :
    ∫ y in ball z (2 * r) ∩ {y | t₁ < T.d' x y ∧ T.d' x y < t₂},
      C.carrierKernel (C.splitK0 H.norm D Γ φ) x y ∂(volume : Measure C.Carrier) = 0 := by
  classical
  have hνc : Continuous H.norm := H.norm.gauge.1
  have hν0 : H.norm 0 = 0 := (H.norm.gauge.2.2.1 0).mpr rfl
  have hdm : Measurable (fun y : C.Carrier => T.d' x y) :=
    T.meas.comp measurable_prodMk_left
  have hρm : Measurable (fun y : C.Carrier => C.rho H.norm x y) :=
    ((C.continuous_rho hνc).comp (continuous_const.prodMk continuous_id)).measurable
  have hAm : MeasurableSet (ball z (2 * r) ∩ {y : C.Carrier | t₁ < T.d' x y ∧ T.d' x y < t₂}) :=
    isOpen_ball.measurableSet.inter
      ((measurableSet_lt measurable_const hdm).inter (measurableSet_lt hdm measurable_const))
  have hBm : MeasurableSet {y : C.Carrier | t₁ < C.rho H.norm x y ∧ C.rho H.norm x y < t₂} :=
    (measurableSet_lt measurable_const hρm).inter (measurableSet_lt hρm measurable_const)
  have hκ : ∀ ξ η, φ (H.norm (C.Θ η ξ)) = 0 → C.splitK0 H.norm D Γ φ ξ η = 0 :=
    fun _ _ h => C.splitK0_eq_zero_of_cutoff_eq_zero h
  have hAB : ∀ y, C.carrierKernel (C.splitK0 H.norm D Γ φ) x y ≠ 0 →
      (y ∈ ball z (2 * r) ∩ {y : C.Carrier | t₁ < T.d' x y ∧ T.d' x y < t₂} ↔
        y ∈ {y : C.Carrier | t₁ < C.rho H.norm x y ∧ C.rho H.norm x y < t₂}) := by
    intro y hy
    obtain ⟨-, hd', hdr⟩ := carrierKernel_ne_zero_imp hκ hφ0 hT hR hy
    constructor
    · rintro ⟨-, h1, h2⟩
      exact ⟨by rwa [← hdr], by rwa [← hdr]⟩
    · rintro ⟨h1, h2⟩
      exact ⟨hR.mem_ball_two_mul hT hr hx hd', by rwa [hdr], by rwa [hdr]⟩
  have h1 : ∫ y in ball z (2 * r) ∩ {y : C.Carrier | t₁ < T.d' x y ∧ T.d' x y < t₂},
        C.carrierKernel (C.splitK0 H.norm D Γ φ) x y ∂(volume : Measure C.Carrier) =
      ∫ y in {y : C.Carrier | t₁ < C.rho H.norm x y ∧ C.rho H.norm x y < t₂},
        C.carrierKernel (C.splitK0 H.norm D Γ φ) x y ∂(volume : Measure C.Carrier) := by
    rw [← integral_indicator hAm, ← integral_indicator hBm]
    congr 1
    funext y
    by_cases hy : C.carrierKernel (C.splitK0 H.norm D Γ φ) x y = 0
    · simp [Set.indicator_apply, hy]
    · simp only [Set.indicator_apply, hAB y hy]
  have hBne : ∀ y ∈ {y : C.Carrier | t₁ < C.rho H.norm x y ∧ C.rho H.norm x y < t₂}, x ≠ y := by
    intro y hy hxy
    subst hxy
    have h0 : C.rho H.norm x x = 0 := by
      show H.norm (C.Θ x.val x.val) = 0
      rw [(C.chart x.val x.val_mem).2.2.2.2, hν0]
    have := hy.1
    linarith
  have h2 : ∫ y in {y : C.Carrier | t₁ < C.rho H.norm x y ∧ C.rho H.norm x y < t₂},
        C.carrierKernel (C.splitK0 H.norm D Γ φ) x y ∂(volume : Measure C.Carrier) =
      ∫ y in {y : C.Carrier | t₁ < C.rho H.norm x y ∧ C.rho H.norm x y < t₂},
        C.splitK0 H.norm D Γ φ x.val y.val ∂(volume : Measure C.Carrier) :=
    setIntegral_congr_fun hBm (fun y hy => carrierKernel_of_ne (hBne y hy))
  have h3 := setIntegral_carrier_eq_image (C := C) (C.splitK0 H.norm D Γ φ x.val) hBm
  have himg : Carrier.val '' {y : C.Carrier | t₁ < C.rho H.norm x y ∧ C.rho H.norm x y < t₂} =
      C.rhoAnnulus H.norm x.val t₁ t₂ := by
    ext η
    constructor
    · rintro ⟨y, ⟨h1, h2⟩, rfl⟩
      exact ⟨y.val_mem, h1, h2⟩
    · rintro ⟨hη, h1, h2⟩
      exact ⟨Carrier.mk η hη, ⟨h1, h2⟩, rfl⟩
  rw [h1, h2, h3, himg]
  exact (C.integral_splitK0_annulus_of_support Γ hΓ D hφc (R₀ := R')
    (fun s hs => hφ0 s hs.le) x.val_mem (hD _ x.val_mem) (hR.chart_image x hxΩ) ht₁ ht).2

end LiftedChart
end RothschildStein.P1
