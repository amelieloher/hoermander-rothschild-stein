-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.LeftParametrixKernel

/-!
# Uniform mass bounds of the left kernel and of its error kernel

For compact sets `Kt, Kw ⊆ C.U` (supports of an output cutoff and of an input weight) the lifted
kernels `Γ*(Θ(η, ξ))` and the left error bracket
`a(ξ) (E*_η Γ*)(Θ(η, ξ)) + 2 ∑ᵢ (a dᵢ + X̃ᵢ a)(ξ) (Zᵢ Γ*)(Θ(η, ξ)) + (L̃* a)(ξ) Γ*(Θ(η, ξ))`
satisfy, uniformly in `η ∈ Kw`, `∫⁻_{ξ ∈ Kt} ‖·‖ₑ dξ ≤ M < ∞` (BB pp. 560–563; the pole computation,
"positive type": the error terms are `O(‖u‖^{1-Q})` near the pole by the weights of the remainder
fields, the divergence terms being smooth coefficients times `Zᵢ Γ*`, and bounded away from it by
joint continuity off the diagonal). The proofs of the near and far bounds are the ones of the right
parametrix, for an arbitrary `H1` fundamental kernel.
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
  {X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart (fun i : Fin (q + 1) => if i = 0 then (2 : ℕ+) else 1) s Ω hΩ X x₀ m}

/-- Away from the pole a bracket that is jointly continuous off the diagonal is
bounded, uniformly for `η ∈ Kw`, `ξ ∈ Kt` with `ρ ≤ ν(Θ η ξ)`. -/
theorem exists_far_bound_of_continuousOn {B : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ}
    (hB : ContinuousOn (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => B p.2 p.1)
      C.kernelOffDiag) {Kt Kw : Set (Fin (n + m) → ℝ)} (hKt : IsCompact Kt) (hKw : IsCompact Kw)
    (hKtU : Kt ⊆ C.U) (hKwU : Kw ⊆ C.U) (ν : G2.HomogeneousNorm C.G) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ Mf : ℝ, ∀ η ∈ Kw, ∀ ξ ∈ Kt, ρ ≤ ν (C.Θ η ξ) → |B η ξ| ≤ Mf := by
  let g : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) → ℝ := fun p => ν (C.Θ p.2 p.1)
  have hΘc : ContinuousOn (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => C.Θ p.2 p.1)
      (Kt ×ˢ Kw) :=
    C.theta_smooth.continuousOn.comp continuous_swap.continuousOn
      (fun _ hp => ⟨hKwU hp.2, hKtU hp.1⟩)
  have hg : ContinuousOn g (Kt ×ˢ Kw) := ν.gauge.1.comp_continuousOn hΘc
  have hclosed : IsClosed (Kt ×ˢ Kw ∩ g ⁻¹' Ici ρ) :=
    hg.preimage_isClosed_of_isClosed (hKt.prod hKw).isClosed isClosed_Ici
  have hFa : IsCompact (Kt ×ˢ Kw ∩ g ⁻¹' Ici ρ) :=
    (hKt.prod hKw).of_isClosed_subset hclosed inter_subset_left
  have hsub : (Kt ×ˢ Kw ∩ g ⁻¹' Ici ρ) ⊆ C.kernelOffDiag := by
    rintro ⟨ξ, η⟩ ⟨⟨hξ, hη⟩, h⟩
    refine ⟨hKtU hξ, hKwU hη, fun hne => ?_⟩
    have h1 : ρ ≤ ν (C.Θ η ξ) := h
    have h0 : C.Θ η ξ = 0 := by
      rw [show ξ = η from hne]
      exact theta_self (hKwU hη)
    rw [h0, (ν.gauge.2.2.1 0).mpr rfl] at h1
    linarith
  obtain ⟨Mf, hMf⟩ := hFa.exists_bound_of_continuousOn (hB.mono hsub)
  refine ⟨Mf, fun η hη ξ hξ h => ?_⟩
  have := hMf (ξ, η) ⟨⟨hξ, hη⟩, h⟩
  simpa [Real.norm_eq_abs] using this

/-- A bracket bounded by `M ν(Θ η ξ)^{1-Q}` near the pole and bounded away from it
has a uniformly bounded lower integral over `Kt` for `η ∈ Kw` (`dξ ≤ D₀ du`, `ν^{1-Q}` is locally
integrable). -/
theorem exists_lintegral_bound_of_near_far {B : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ}
    {Kt Kw : Set (Fin (n + m) → ℝ)} (hKt : IsCompact Kt) (hKw : IsCompact Kw)
    (hKtU : Kt ⊆ C.U) (hKwU : Kw ⊆ C.U) (ν : G2.HomogeneousNorm C.G) {ρ M Mf : ℝ}
    (hnear : ∀ η ∈ Kw, ∀ ξ ∈ Kt, 0 < ν (C.Θ η ξ) → ν (C.Θ η ξ) < ρ →
      |B η ξ| ≤ M * ν (C.Θ η ξ) ^ (1 - (C.G.homogeneousDimension : ℤ)))
    (hfar : ∀ η ∈ Kw, ∀ ξ ∈ Kt, ρ ≤ ν (C.Θ η ξ) → |B η ξ| ≤ Mf) :
    ∃ M₂ : ℝ≥0∞, M₂ < ⊤ ∧ ∀ η ∈ Kw, ∫⁻ ξ in Kt, ‖B η ξ‖ₑ ≤ M₂ := by
  have hNZ : NeZero (n + m) := ⟨C.G.dimension_pos.ne'⟩
  obtain ⟨D₀, hD₀, hD⟩ := exists_density_bound (C := C) hKt hKw hKtU hKwU
  set Q : ℕ := C.G.homogeneousDimension with hQ
  let gn : (Fin (n + m) → ℝ) → ℝ := fun u =>
    |M| * Set.indicator {u | ν u ≤ ρ} (fun u => ν u ^ (-((Q : ℝ) - 1))) u
  have hgint : Integrable gn := (integrable_indicator_gauge_rpow ν (β := (Q : ℝ) - 1)
    (by linarith) ρ).const_mul |M|
  have hgfin : ∫⁻ u, ENNReal.ofReal (gn u) < ⊤ := hgint.lintegral_lt_top
  have hKtfin : volume Kt < ⊤ := hKt.measure_lt_top
  refine ⟨ENNReal.ofReal D₀ * (∫⁻ u, ENNReal.ofReal (gn u)) + ENNReal.ofReal |Mf| * volume Kt,
    ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top ENNReal.ofReal_lt_top hgfin,
      ENNReal.mul_lt_top ENNReal.ofReal_lt_top hKtfin⟩, fun η hη => ?_⟩
  have hmeas : MeasurableSet Kt := hKt.isClosed.measurableSet
  have h0 : ∀ᵐ ξ ∂(volume : Measure (Fin (n + m) → ℝ)), ξ ≠ η := by
    have : ({η} : Set (Fin (n + m) → ℝ))ᶜ ∈ ae (volume : Measure (Fin (n + m) → ℝ)) := by
      rw [compl_mem_ae_iff]
      simp
    exact this
  have hpt : ∀ᵐ ξ ∂(volume.restrict Kt), ‖B η ξ‖ₑ ≤
      ENNReal.ofReal (gn (C.Θ η ξ)) + ENNReal.ofReal |Mf| := by
    refine (ae_restrict_iff' hmeas).2 ?_
    filter_upwards [h0] with ξ hne hξ
    rw [Real.enorm_eq_ofReal_abs]
    by_cases hfarξ : ρ ≤ ν (C.Θ η ξ)
    · calc ENNReal.ofReal |B η ξ| ≤ ENNReal.ofReal |Mf| :=
            ENNReal.ofReal_le_ofReal ((hfar η hη ξ hξ hfarξ).trans (le_abs_self _))
        _ ≤ _ := le_add_self
    · have hlt : ν (C.Θ η ξ) < ρ := not_le.1 hfarξ
      have hνpos : 0 < ν (C.Θ η ξ) := by
        refine G2.gauge_pos ν.gauge (C.theta_ne_zero (hKwU hη) (hKtU hξ) hne)
      have hb := hnear η hη ξ hξ hνpos hlt
      have hind : gn (C.Θ η ξ) = |M| * ν (C.Θ η ξ) ^ (-((Q : ℝ) - 1)) := by
        simp only [gn]
        rw [Set.indicator_of_mem (show C.Θ η ξ ∈ {u | ν u ≤ ρ} from hlt.le)]
      have hz : ν (C.Θ η ξ) ^ (1 - (Q : ℤ)) = ν (C.Θ η ξ) ^ (-((Q : ℝ) - 1)) := by
        rw [← Real.rpow_intCast]
        congr 1
        push_cast
        ring
      calc ENNReal.ofReal |B η ξ| ≤ ENNReal.ofReal (gn (C.Θ η ξ)) := by
            refine ENNReal.ofReal_le_ofReal (hb.trans ?_)
            rw [hind, ← hz]
            exact mul_le_mul_of_nonneg_right (le_abs_self M) (zpow_pos hνpos _).le
        _ ≤ _ := le_self_add
  calc ∫⁻ ξ in Kt, ‖B η ξ‖ₑ
      ≤ ∫⁻ ξ in Kt, (ENNReal.ofReal (gn (C.Θ η ξ)) + ENNReal.ofReal |Mf|) :=
        lintegral_mono_ae hpt
    _ = (∫⁻ ξ in Kt, ENNReal.ofReal (gn (C.Θ η ξ))) + ENNReal.ofReal |Mf| * volume Kt := by
        rw [lintegral_add_right _ measurable_const, setLIntegral_const]
    _ ≤ ENNReal.ofReal D₀ * (∫⁻ u, ENNReal.ofReal (gn u)) + ENNReal.ofReal |Mf| * volume Kt := by
        gcongr
        refine (lintegral_comp_theta_le_mass (hKwU hη) hKt hKtU hD₀ (fun ξ hξ => hD η hη ξ hξ)
          (fun u => ENNReal.ofReal (gn u))).trans ?_
        gcongr
        exact Measure.restrict_le_self

/-- The lower integral of an `H1` fundamental kernel over `Kt` is bounded
uniformly in `η ∈ Kw`. -/
theorem exists_lintegral_bound_kernel_of_standing {H : H1.StandingHypotheses C.G q}
    (K : H1.FundamentalKernel C.G H) {Kt Kw : Set (Fin (n + m) → ℝ)}
    (hKt : IsCompact Kt) (hKw : IsCompact Kw) (hKtU : Kt ⊆ C.U) (hKwU : Kw ⊆ C.U) :
    ∃ M₁ : ℝ≥0∞, M₁ < ⊤ ∧ ∀ η ∈ Kw, ∫⁻ ξ in Kt, ‖K (C.Θ η ξ)‖ₑ ≤ M₁ := by
  obtain ⟨D₀, hD₀, hD⟩ := exists_density_bound (C := C) hKt hKw hKtU hKwU
  obtain ⟨hPc, -⟩ := isCompact_thetaImage (C := C) hKt hKw hKtU hKwU
  set B := Prod.snd '' ((fun z : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => (z.1, C.Θ z.1 z.2)) ''
    (Kw ×ˢ Kt)) with hB
  have hBc : IsCompact B := hPc.image continuous_snd
  have hfin : ∫⁻ u in B, ‖(K : (Fin (n + m) → ℝ) → ℝ) u‖ₑ < ⊤ :=
    (K.locallyIntegrable.integrableOn_isCompact hBc).2
  refine ⟨ENNReal.ofReal D₀ * ∫⁻ u in B, ‖(K : (Fin (n + m) → ℝ) → ℝ) u‖ₑ,
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin, fun η hη => ?_⟩
  refine (lintegral_comp_theta_le_mass (hKwU hη) hKt hKtU hD₀ (fun ξ hξ => hD η hη ξ hξ)
    (fun u => ‖(K : (Fin (n + m) → ℝ) → ℝ) u‖ₑ)).trans ?_
  gcongr
  rintro _ ⟨ξ, hξ, rfl⟩
  exact ⟨(η, C.Θ η ξ), ⟨(η, ξ), ⟨hη, hξ⟩, rfl⟩, rfl⟩

/-- The remainder derivative `R₀ K` of an `H1` fundamental kernel lies in the
symbol class of degree `1 - Q` (`R_{[0]}` has weight `≥ -1`), uniformly for centres in a compact
set. -/
theorem sym_R0_kernel {H : H1.StandingHypotheses C.G q} (K : H1.FundamentalKernel C.G H)
    (ν : G2.HomogeneousNorm C.G) {Kc : Set (Fin (n + m) → ℝ)} (hKc : IsCompact Kc)
    (hKU : Kc ⊆ C.U) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hT : ∀ η ∈ Kc, ∀ u, ν u ≤ ρ → (η, u) ∈ C.T) (kk : ℕ) :
    Sym (chartCtx C ν Kc ρ) kk (1 - (C.G.homogeneousDimension : ℤ))
      (fun η u => fieldDerivative (C.R [0] η) K u) := by
  have hc := chartCtx_good C ν Kc hρ0 hρ1
  have hΓ : ∀ kk, Sym (chartCtx C ν Kc ρ) kk (2 - (C.G.homogeneousDimension : ℤ))
      (fun _ => (K : (Fin (n + m) → ℝ) → ℝ)) := fun kk => sym_kernel C K ν Kc ρ kk
  have hZR0 : ∀ (j : Fin (n + m)) (kk : ℕ),
      Sym (chartCtx C ν Kc ρ) kk ((C.G.weight j : ℤ) - 1) (fun η u => C.R [0] η u j) :=
    fun j kk => sym_congr_degree (by simp)
      (sym_remainderField C ν hKc hKU hρ0 hρ1 hT 0 j kk)
  exact sym_congr_degree (by ring)
    (Sym.fieldDeriv (chartCtx C ν Kc ρ) hc (Z := fun η u => C.R [0] η u) (w := 1) hZR0
      (hΓ (kk + 1)))

/-- Near the pole, uniformly for `η ∈ Kw`, `ξ ∈ Kt`: the left error bracket is
bounded by `M ν(Θ η ξ)^{1-Q}` (the weights of the remainder fields: `R_{[i]}` has weight `≥ 0` and
`R_{[0]}` weight `≥ -1`, so `E*_η Γ* = O(ν^{1-Q})`; the divergence terms are smooth coefficients
times `Zᵢ Γ*` and `Γ*`). -/
theorem exists_near_bound_left {H : H1.StandingHypotheses C.G q} (K : H1.FundamentalKernel C.G H)
    {Kt Kw : Set (Fin (n + m) → ℝ)} (hKt : IsCompact Kt) (hKw : IsCompact Kw) (hKtU : Kt ⊆ C.U)
    (hKwU : Kw ⊆ C.U) {a : (Fin (n + m) → ℝ) → ℝ} (ha : ContDiffOn ℝ (⊤ : ℕ∞) a C.U) :
    ∃ (ν : G2.HomogeneousNorm C.G) (ρ M : ℝ), ν.Smooth ∧ 0 < ρ ∧ ρ ≤ 1 ∧
      ∀ η ∈ Kw, ∀ ξ ∈ Kt, 0 < ν (C.Θ η ξ) → ν (C.Θ η ξ) < ρ →
        |C.leftErrBracket K a η ξ| ≤
          M * ν (C.Θ η ξ) ^ (1 - (C.G.homogeneousDimension : ℤ)) := by
  obtain ⟨ρ, hρ0, hρ1, hT⟩ := exists_chart_radius C (G2.smoothNorm C.G) hKw hKwU
  set ν := G2.smoothNorm C.G with hνdef
  obtain ⟨hE, hZ, hK⟩ := sym_kernel_package K ν hKw hKwU hρ0 hρ1 hT
  have hR0 := sym_R0_kernel K ν hKw hKwU hρ0 hρ1 hT
  obtain ⟨ME, hME⟩ := (hE 0).bound _
  obtain ⟨MK, hMK⟩ := (hK 0).bound _
  obtain ⟨MR, hMR⟩ := (hR0 0).bound _
  choose MZ hMZ using fun i : Fin q => (hZ i 0).bound _
  obtain ⟨Ba, hBa⟩ := hKt.exists_bound_of_continuousOn (ha.continuousOn.mono hKtU)
  obtain ⟨BL, hBL⟩ := hKt.exists_bound_of_continuousOn
    ((contDiffOn_sumSquaresWithDriftTranspose_Xl ha).continuousOn.mono hKtU)
  choose BD hBD using fun i : Fin q => hKt.exists_bound_of_continuousOn
    ((contDiffOn_leftBetaCoeff ha i).continuousOn.mono hKtU)
  refine ⟨ν, ρ, |Ba| * (|ME| + 2 * |MR|) + 2 * ∑ i : Fin q, |BD i| * |MZ i| + |BL| * |MK|,
    G2.smoothNorm_smooth C.G, hρ0, hρ1, ?_⟩
  intro η hη ξ hξ hνpos hνlt
  have hηU := hKwU hη
  have hξU := hKtU hξ
  set u := C.Θ η ξ with hu
  set Q : ℤ := (C.G.homogeneousDimension : ℤ) with hQ
  have hz : 0 < ν u ^ (1 - Q) := zpow_pos hνpos _
  have hP : u ∈ (chartCtx C ν Kw ρ).P := ⟨hνpos, hνlt⟩
  have hu0 : u ≠ 0 := by
    intro h0
    rw [h0, (ν.gauge.2.2.1 0).mpr rfl] at hνpos
    exact lt_irrefl _ hνpos
  have hlpe : C.leftPoleError η K u = C.leftErrorOp η K u :=
    C.leftPoleError_eq_leftErrorOp hηU isOpen_compl_singleton K.smooth_off_zero hu0
      (C.theta_mem_target hηU hξU)
  have e1 : |C.errorOp η K u| ≤ |ME| * ν u ^ (1 - Q) :=
    (hME η hη u hP).trans (mul_le_mul_of_nonneg_right (le_abs_self _) hz.le)
  have eR : |fieldDerivative (C.R [0] η) K u| ≤ |MR| * ν u ^ (1 - Q) :=
    (hMR η hη u hP).trans (mul_le_mul_of_nonneg_right (le_abs_self _) hz.le)
  have e2 : ∀ i : Fin q, |fieldDerivative (zField C i.succ η) K u| ≤ |MZ i| * ν u ^ (1 - Q) :=
    fun i => (hMZ i η hη u hP).trans (mul_le_mul_of_nonneg_right (le_abs_self _) hz.le)
  have e3 : |K u| ≤ |MK| * ν u ^ (1 - Q) :=
    (hMK η hη u hP).trans (mul_le_mul_of_nonneg_right (le_abs_self _) hz.le)
  have ha' : |a ξ| ≤ |Ba| := by simpa [Real.norm_eq_abs] using (hBa ξ hξ).trans (le_abs_self Ba)
  have hL' : |sumSquaresWithDriftTranspose C.Xl a ξ| ≤ |BL| := by
    simpa [Real.norm_eq_abs] using (hBL ξ hξ).trans (le_abs_self BL)
  have hD' : ∀ i : Fin q, |C.leftBetaCoeff a i ξ| ≤ |BD i| := fun i => by
    simpa [Real.norm_eq_abs] using (hBD i ξ hξ).trans (le_abs_self (BD i))
  have hzD : ∀ i : Fin q, C.zDeriv η i.succ K u = fieldDerivative (zField C i.succ η) K u :=
    fun i => zDeriv_eq_zField η i.succ K u
  have hLE : |C.leftPoleError η K u| ≤ (|ME| + 2 * |MR|) * ν u ^ (1 - Q) := by
    rw [hlpe]
    unfold leftErrorOp
    calc |C.errorOp η K u - 2 * fieldDerivative (C.R [0] η) K u|
        ≤ |C.errorOp η K u| + |2 * fieldDerivative (C.R [0] η) K u| := abs_sub _ _
      _ = |C.errorOp η K u| + 2 * |fieldDerivative (C.R [0] η) K u| := by rw [abs_mul, abs_two]
      _ ≤ |ME| * ν u ^ (1 - Q) + 2 * (|MR| * ν u ^ (1 - Q)) := by gcongr
      _ = (|ME| + 2 * |MR|) * ν u ^ (1 - Q) := by ring
  have b1 : |a ξ * C.leftPoleError η K u| ≤ |Ba| * (|ME| + 2 * |MR|) * ν u ^ (1 - Q) := by
    rw [abs_mul]
    calc |a ξ| * |C.leftPoleError η K u| ≤ |Ba| * ((|ME| + 2 * |MR|) * ν u ^ (1 - Q)) :=
          mul_le_mul ha' hLE (abs_nonneg _) (abs_nonneg _)
      _ = |Ba| * (|ME| + 2 * |MR|) * ν u ^ (1 - Q) := by ring
  have b2 : |2 * ∑ i : Fin q, C.leftBetaCoeff a i ξ * C.zDeriv η i.succ K u| ≤
      2 * ∑ i : Fin q, |BD i| * |MZ i| * ν u ^ (1 - Q) := by
    rw [abs_mul, abs_two]
    refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun i _ => ?_)) (by norm_num)
    rw [abs_mul, hzD i]
    calc |C.leftBetaCoeff a i ξ| * |fieldDerivative (zField C i.succ η) K u|
        ≤ |BD i| * (|MZ i| * ν u ^ (1 - Q)) := mul_le_mul (hD' i) (e2 i) (abs_nonneg _) (abs_nonneg _)
      _ = |BD i| * |MZ i| * ν u ^ (1 - Q) := by ring
  have b3 : |sumSquaresWithDriftTranspose C.Xl a ξ * K u| ≤ |BL| * |MK| * ν u ^ (1 - Q) := by
    rw [abs_mul]
    calc |sumSquaresWithDriftTranspose C.Xl a ξ| * |K u| ≤ |BL| * (|MK| * ν u ^ (1 - Q)) :=
          mul_le_mul hL' e3 (abs_nonneg _) (abs_nonneg _)
      _ = |BL| * |MK| * ν u ^ (1 - Q) := by ring
  calc |C.leftErrBracket K a η ξ| ≤ |a ξ * C.leftPoleError η K u| +
        |2 * ∑ i : Fin q, C.leftBetaCoeff a i ξ * C.zDeriv η i.succ K u| +
        |sumSquaresWithDriftTranspose C.Xl a ξ * K u| := abs_add_three _ _ _
    _ ≤ |Ba| * (|ME| + 2 * |MR|) * ν u ^ (1 - Q) +
        2 * ∑ i : Fin q, |BD i| * |MZ i| * ν u ^ (1 - Q) +
        |BL| * |MK| * ν u ^ (1 - Q) := add_le_add (add_le_add b1 b2) b3
    _ = (|Ba| * (|ME| + 2 * |MR|) + 2 * ∑ i : Fin q, |BD i| * |MZ i| + |BL| * |MK|) *
          ν u ^ (1 - Q) := by
        rw [← Finset.sum_mul]
        ring

/-- The lower integral of the left error bracket over `Kt` is bounded uniformly
in `η ∈ Kw` (BB pp. 560–563; the pole computation: positive type). -/
theorem exists_lintegral_bound_leftErrBracket (hq : 0 < q) (ν₀ : G2.HomogeneousNorm C.G)
    (K : H1.FundamentalKernel C.G ((C.driftModel hq ν₀).reverseDrift C.G))
    {Kt Kw : Set (Fin (n + m) → ℝ)} (hKt : IsCompact Kt) (hKw : IsCompact Kw) (hKtU : Kt ⊆ C.U)
    (hKwU : Kw ⊆ C.U) {a : (Fin (n + m) → ℝ) → ℝ} (ha : ContDiffOn ℝ (⊤ : ℕ∞) a C.U) :
    ∃ M₂ : ℝ≥0∞, M₂ < ⊤ ∧ ∀ η ∈ Kw, ∫⁻ ξ in Kt, ‖C.leftErrBracket K a η ξ‖ₑ ≤ M₂ := by
  obtain ⟨ν, ρ, M, hν, hρ0, hρ1, hnear⟩ := exists_near_bound_left K hKt hKw hKtU hKwU ha
  obtain ⟨Mf, hMf⟩ := exists_far_bound_of_continuousOn (continuousOn_leftErrBracket K ha)
    hKt hKw hKtU hKwU ν hρ0
  exact exists_lintegral_bound_of_near_far hKt hKw hKtU hKwU ν hnear hMf

end LiftedChart

end RothschildStein.P1
