-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.RightParametrixKernel
public import RothschildStein.P1.RightParametrixError
public import RothschildStein.P1.RightParametrixPole

/-!
# Uniform mass bounds of the right kernel and of its error kernel

For compact sets `Kt, Kw ⊆ C.U` (supports of an output cutoff and of an input weight) the lifted
kernels `K(Θ(η, ξ))` and the error bracket
`a(ξ) (E_η K)(Θ(η, ξ)) + 2 ∑ᵢ (X̃ᵢ a)(ξ) (Zᵢ K)(Θ(η, ξ)) + (L̃ a)(ξ) K(Θ(η, ξ))`
satisfy, uniformly in `η ∈ Kw`, `∫⁻_{ξ ∈ Kt} ‖·‖ₑ dξ ≤ M < ∞` (BB p. 605; the right pole computation,
"positive type": the error terms are `O(‖u‖^{1-Q})` near the pole by the weights of the remainder
fields, and bounded away from it by joint continuity off the diagonal). The substitution
`u = Θ(η, ξ)` has density `≤ D₀` on `Kw × Kt` (`lintegral_comp_theta_le_mass`).
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

section General

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  {C : LiftedChart w s Ω hΩ X x₀ m}

/-- The image of `Kw × Kt` under `(η, ξ) ↦ (η, Θ η ξ)` is compact and lies in
the domain `T` of the remainders and density corrections. -/
theorem isCompact_thetaImage {Kt Kw : Set (Fin (n + m) → ℝ)} (hKt : IsCompact Kt)
    (hKw : IsCompact Kw) (hKtU : Kt ⊆ C.U) (hKwU : Kw ⊆ C.U) :
    IsCompact ((fun z : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => (z.1, C.Θ z.1 z.2)) '' (Kw ×ˢ Kt)) ∧
    ((fun z : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => (z.1, C.Θ z.1 z.2)) '' (Kw ×ˢ Kt)) ⊆ C.T := by
  refine ⟨(hKw.prod hKt).image_of_continuousOn
    (continuousOn_fst.prodMk (C.theta_smooth.continuousOn.mono (prod_mono hKwU hKtU))), ?_⟩
  rintro _ ⟨⟨η, ξ⟩, ⟨hη, hξ⟩, rfl⟩
  exact ⟨hKwU hη, C.theta_mem_target (hKwU hη) (hKtU hξ)⟩

/-- A uniform bound `D₀` of the density `c(η) (1 + ω₊(η, Θ η ξ))` on `Kw × Kt`. -/
theorem exists_density_bound {Kt Kw : Set (Fin (n + m) → ℝ)} (hKt : IsCompact Kt)
    (hKw : IsCompact Kw) (hKtU : Kt ⊆ C.U) (hKwU : Kw ⊆ C.U) :
    ∃ D₀ : ℝ, 0 < D₀ ∧ ∀ η ∈ Kw, ∀ ξ ∈ Kt, C.c η * (1 + C.ωp η (C.Θ η ξ)) ≤ D₀ := by
  obtain ⟨hcpt, hT⟩ := isCompact_thetaImage (C := C) hKt hKw hKtU hKwU
  have hcont : ContinuousOn (fun z : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) =>
      C.c z.1 * (1 + C.ωp z.1 z.2)) C.T := by
    have h1 : ContinuousOn (fun z : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => C.c z.1) C.T :=
      (C.density_smooth.continuousOn.comp continuousOn_fst (fun z hz => hz.1))
    exact h1.mul (continuousOn_const.add C.ωp_smooth.continuousOn)
  obtain ⟨M, hM⟩ := hcpt.exists_bound_of_continuousOn (hcont.mono hT)
  refine ⟨max M 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun η hη ξ hξ => ?_⟩
  have h0 := hM (η, C.Θ η ξ) ⟨(η, ξ), ⟨hη, hξ⟩, rfl⟩
  have h1 : |C.c η * (1 + C.ωp η (C.Θ η ξ))| ≤ M := by simpa [Real.norm_eq_abs] using h0
  exact (le_abs_self _).trans (h1.trans (le_max_left _ _))

/-- Comparison of lower integrals under the substitution `u = Θ η ξ`
(`dξ ≤ D₀ du` on `Kt` when the density is bounded by `D₀`). -/
theorem lintegral_comp_theta_le_mass {η : Fin (n + m) → ℝ} (hη : η ∈ C.U)
    {Kt : Set (Fin (n + m) → ℝ)} (hKt : IsCompact Kt) (hKtU : Kt ⊆ C.U) {D₀ : ℝ} (hD₀ : 0 < D₀)
    (hD : ∀ ξ ∈ Kt, C.c η * (1 + C.ωp η (C.Θ η ξ)) ≤ D₀) (g : (Fin (n + m) → ℝ) → ℝ≥0∞) :
    ∫⁻ ξ in Kt, g (C.Θ η ξ) ≤ ENNReal.ofReal D₀ * ∫⁻ u in C.Θ η '' Kt, g u := by
  have hmeas : MeasurableSet Kt := hKt.isClosed.measurableSet
  have hderiv : ∀ x ∈ Kt, HasFDerivWithinAt (C.Θ η) (fderiv ℝ (C.Θ η) x) Kt x :=
    fun x hx => (C.differentiableAt_theta hη (hKtU hx)).hasFDerivAt.hasFDerivWithinAt
  have h := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hmeas hderiv
    ((injOn_theta hη).mono hKtU) g
  rw [h, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono_ae ((ae_restrict_iff' hmeas).2 (Filter.Eventually.of_forall (fun ξ hξ => ?_)))
  obtain ⟨hp1, -, hjac, -⟩ := C.jacobian η hη ξ (hKtU hξ)
  have hdet : |(fderiv ℝ (C.Θ η) ξ).det| = (C.c η * (1 + C.ωp η (C.Θ η ξ)))⁻¹ := by
    rw [← hjac]
    unfold absoluteJacobian
    rw [LinearMap.det_toMatrix]
  have hpos : 0 < C.c η * (1 + C.ωp η (C.Θ η ξ)) := mul_pos (C.density_pos η hη) hp1
  have h1 : 1 ≤ D₀ * (C.c η * (1 + C.ωp η (C.Θ η ξ)))⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hpos, one_mul]
    exact hD ξ hξ
  rw [← mul_assoc, hdet, ← ENNReal.ofReal_mul hD₀.le]
  calc g (C.Θ η ξ) = 1 * g (C.Θ η ξ) := (one_mul _).symm
    _ ≤ ENNReal.ofReal (D₀ * (C.c η * (1 + C.ωp η (C.Θ η ξ)))⁻¹) * g (C.Θ η ξ) := by
        gcongr
        exact ENNReal.one_le_ofReal.2 h1

end General

section Drift

variable {n q s m : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart (fun i : Fin (q + 1) => if i = 0 then (2 : ℕ+) else 1) s Ω hΩ X x₀ m}

variable (C) in
/-- The bracket of the error kernel of the right parametrix,
`a(ξ) (E_η K)(Θ(η, ξ)) + 2 ∑ᵢ (X̃ᵢ a)(ξ) (Zᵢ K)(Θ(η, ξ)) + (L̃ a)(ξ) K(Θ(η, ξ))`
(the right pole computation, output product formula). -/
def errBracket (K a : (Fin (n + m) → ℝ) → ℝ) (η ξ : Fin (n + m) → ℝ) : ℝ :=
  a ξ * C.rightPoleError η K (C.Θ η ξ) +
    2 * ∑ i : Fin q, fieldDerivative (C.Xl i.succ) a ξ * C.zDeriv η i.succ K (C.Θ η ξ) +
    sumSquaresWithDrift C.Xl a ξ * K (C.Θ η ξ)

/-- The error bracket is jointly continuous on the off-diagonal set. -/
theorem continuousOn_errBracket {hq : 0 < q} {ν₀ : G2.HomogeneousNorm C.G}
    (K : H1.FundamentalKernel C.G (C.driftModel hq ν₀)) {a : (Fin (n + m) → ℝ) → ℝ}
    (ha : ContDiffOn ℝ (⊤ : ℕ∞) a C.U) :
    ContinuousOn (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) =>
      C.errBracket K a p.2 p.1) C.kernelOffDiag :=
  (contDiffOn_errorBracket K.smooth_off_zero ha).continuousOn.congr (fun _ hp =>
    (sumSquaresWithDrift1_kernelPhi_eq K ha hp.2.1 hp.1 hp.2.2).symm)

/-- Symbol classes of the kernel, of `Zᵢ K` and of the error `E K`, uniformly for
centres in a compact set: all lie in `Sym (1 - Q)`. -/
theorem sym_kernel_package {H : H1.StandingHypotheses C.G q} (K : H1.FundamentalKernel C.G H)
    (ν : G2.HomogeneousNorm C.G) {Kc : Set (Fin (n + m) → ℝ)} (hKc : IsCompact Kc)
    (hKU : Kc ⊆ C.U) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hT : ∀ η ∈ Kc, ∀ u, ν u ≤ ρ → (η, u) ∈ C.T) :
    (∀ kk, Sym (chartCtx C ν Kc ρ) kk (1 - (C.G.homogeneousDimension : ℤ))
      (fun η u => C.errorOp η K u)) ∧
    (∀ (i : Fin q) (kk : ℕ), Sym (chartCtx C ν Kc ρ) kk (1 - (C.G.homogeneousDimension : ℤ))
      (fun η u => fieldDerivative (zField C i.succ η) K u)) ∧
    (∀ kk, Sym (chartCtx C ν Kc ρ) kk (1 - (C.G.homogeneousDimension : ℤ)) (fun _ u => K u)) := by
  have hc := chartCtx_good C ν Kc hρ0 hρ1
  set Q : ℤ := (C.G.homogeneousDimension : ℤ) with hQ
  have hΓ : ∀ kk, Sym (chartCtx C ν Kc ρ) kk (2 - Q) (fun _ => (K : (Fin (n + m) → ℝ) → ℝ)) :=
    fun kk => sym_kernel C K ν Kc ρ kk
  have hZY : ∀ (i : Fin q) (j : Fin (n + m)) (kk : ℕ),
      Sym (chartCtx C ν Kc ρ) kk ((C.G.weight j : ℤ) - 1) (fun _ u => C.Y i.succ u j) :=
    fun i j kk => sym_congr_degree (by simp [Fin.succ_ne_zero])
      (sym_modelField C ν Kc ρ i.succ j kk)
  have hZR : ∀ (i : Fin q) (j : Fin (n + m)) (kk : ℕ),
      Sym (chartCtx C ν Kc ρ) kk ((C.G.weight j : ℤ) - 0) (fun η u => C.R [i.succ] η u j) :=
    fun i j kk => sym_congr_degree (by simp [Fin.succ_ne_zero])
      (sym_remainderField C ν hKc hKU hρ0 hρ1 hT i.succ j kk)
  have hZZ : ∀ (i : Fin q) (j : Fin (n + m)) (kk : ℕ),
      Sym (chartCtx C ν Kc ρ) kk ((C.G.weight j : ℤ) - 1) (fun η u => zField C i.succ η u j) :=
    fun i j kk => sym_congr_degree (by simp [Fin.succ_ne_zero])
      (zField_sym C ν hKc hKU hρ0 hρ1 hT i.succ j kk)
  have hZR0 : ∀ (j : Fin (n + m)) (kk : ℕ),
      Sym (chartCtx C ν Kc ρ) kk ((C.G.weight j : ℤ) - 1) (fun η u => C.R [0] η u j) :=
    fun j kk => sym_congr_degree (by simp)
      (sym_remainderField C ν hKc hKU hρ0 hρ1 hT 0 j kk)
  have hAR : ∀ (i : Fin q) (kk : ℕ), Sym (chartCtx C ν Kc ρ) kk (2 - Q)
      (fun η u => fieldDerivative (C.R [i.succ] η) (K : (Fin (n + m) → ℝ) → ℝ) u) :=
    fun i kk => sym_congr_degree (by ring)
      (Sym.fieldDeriv (chartCtx C ν Kc ρ) hc (Z := fun η u => C.R [i.succ] η u) (w := 0)
        (fun j k => hZR i j k) (hΓ (kk + 1)))
  have hAZ : ∀ (i : Fin q) (kk : ℕ), Sym (chartCtx C ν Kc ρ) kk (1 - Q)
      (fun η u => fieldDerivative (zField C i.succ η) (K : (Fin (n + m) → ℝ) → ℝ) u) :=
    fun i kk => sym_congr_degree (by ring)
      (Sym.fieldDeriv (chartCtx C ν Kc ρ) hc (Z := fun η u => zField C i.succ η u) (w := 1)
        (fun j k => hZZ i j k) (hΓ (kk + 1)))
  refine ⟨fun kk => ?_, hAZ, fun kk => Sym.mono_d _ hc (by omega) (hΓ kk)⟩
  have t1 : ∀ i : Fin q, Sym (chartCtx C ν Kc ρ) kk (1 - Q)
      (fun η u => fieldDerivative (C.Y i.succ)
        (fieldDerivative (C.R [i.succ] η) (K : (Fin (n + m) → ℝ) → ℝ)) u) := fun i =>
    sym_congr_degree (by ring)
      (Sym.fieldDeriv (chartCtx C ν Kc ρ) hc (Z := fun _ u => C.Y i.succ u) (w := 1)
        (fun j k => hZY i j k) (hAR i (kk + 1)))
  have t2 : ∀ i : Fin q, Sym (chartCtx C ν Kc ρ) kk (1 - Q)
      (fun η u => fieldDerivative (C.R [i.succ] η)
        (fieldDerivative (zField C i.succ η) (K : (Fin (n + m) → ℝ) → ℝ)) u) := fun i =>
    sym_congr_degree (by ring)
      (Sym.fieldDeriv (chartCtx C ν Kc ρ) hc (Z := fun η u => C.R [i.succ] η u) (w := 0)
        (fun j k => hZR i j k) (hAZ i (kk + 1)))
  have t3 : Sym (chartCtx C ν Kc ρ) kk (1 - Q)
      (fun η u => fieldDerivative (C.R [0] η) (K : (Fin (n + m) → ℝ) → ℝ) u) :=
    sym_congr_degree (by ring)
      (Sym.fieldDeriv (chartCtx C ν Kc ρ) hc (Z := fun η u => C.R [0] η u) (w := 1) hZR0
        (hΓ (kk + 1)))
  exact Sym.add _ hc (Sym.sum _ hc (Finset.univ : Finset (Fin q)) (fun i η u =>
    fieldDerivative (C.Y i.succ) (fieldDerivative (C.R [i.succ] η) (K : (Fin (n + m) → ℝ) → ℝ)) u +
    fieldDerivative (C.R [i.succ] η) (fieldDerivative (zField C i.succ η)
      (K : (Fin (n + m) → ℝ) → ℝ)) u) (fun i _ => Sym.add _ hc (t1 i) (t2 i))) t3

/-- Near the pole, uniformly for `η ∈ Kw`, `ξ ∈ Kt`: the error bracket and the kernel
are bounded by `M ν(Θ η ξ)^{1-Q}` (the weights of the remainder fields: `R_{[i]}` has weight `≥ 0`
and `R_{[0]}` weight `≥ -1`, so `E_η K = O(ν^{1-Q})`). -/
theorem exists_near_bound (hq : 0 < q) (ν₀ : G2.HomogeneousNorm C.G)
    (K : H1.FundamentalKernel C.G (C.driftModel hq ν₀)) {Kt Kw : Set (Fin (n + m) → ℝ)}
    (hKt : IsCompact Kt) (hKw : IsCompact Kw) (hKtU : Kt ⊆ C.U) (hKwU : Kw ⊆ C.U)
    {a : (Fin (n + m) → ℝ) → ℝ} (ha : ContDiffOn ℝ (⊤ : ℕ∞) a C.U) :
    ∃ (ν : G2.HomogeneousNorm C.G) (ρ M : ℝ), ν.Smooth ∧ 0 < ρ ∧ ρ ≤ 1 ∧
      ∀ η ∈ Kw, ∀ ξ ∈ Kt, 0 < ν (C.Θ η ξ) → ν (C.Θ η ξ) < ρ →
        |C.errBracket K a η ξ| ≤ M * ν (C.Θ η ξ) ^ (1 - (C.G.homogeneousDimension : ℤ)) ∧
        |K (C.Θ η ξ)| ≤ M * ν (C.Θ η ξ) ^ (1 - (C.G.homogeneousDimension : ℤ)) := by
  obtain ⟨ρ, hρ0, hρ1, hT⟩ := exists_chart_radius C (G2.smoothNorm C.G) hKw hKwU
  set ν := G2.smoothNorm C.G with hνdef
  obtain ⟨hE, hZ, hK⟩ := sym_kernel_package K ν hKw hKwU hρ0 hρ1 hT
  obtain ⟨ME, hME⟩ := (hE 0).bound _
  obtain ⟨MK, hMK⟩ := (hK 0).bound _
  choose MZ hMZ using fun i : Fin q => (hZ i 0).bound _
  obtain ⟨Ba, hBa⟩ := hKt.exists_bound_of_continuousOn (ha.continuousOn.mono hKtU)
  obtain ⟨BL, hBL⟩ := hKt.exists_bound_of_continuousOn
    ((contDiffOn_sumSquaresWithDrift_Xl ha).continuousOn.mono hKtU)
  choose BX hBX using fun i : Fin q => hKt.exists_bound_of_continuousOn
    ((contDiffOn_fieldDerivative_Xl ha i.succ).continuousOn.mono hKtU)
  refine ⟨ν, ρ, |Ba| * |ME| + 2 * ∑ i : Fin q, |BX i| * |MZ i| + |BL| * |MK| + |MK|,
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
  have hrpe : C.rightPoleError η K u = C.errorOp η K u :=
    C.rightPoleError_eq_errorOp hηU isOpen_compl_singleton K.smooth_off_zero hu0
      (C.theta_mem_target hηU hξU)
  have hzD : ∀ i : Fin q, C.zDeriv η i.succ K u = fieldDerivative (zField C i.succ η) K u :=
    fun i => by rw [zDeriv_eq_fieldDerivative]
  have e1 : |C.errorOp η K u| ≤ |ME| * ν u ^ (1 - Q) :=
    (hME η hη u hP).trans (mul_le_mul_of_nonneg_right (le_abs_self _) hz.le)
  have e2 : ∀ i : Fin q, |fieldDerivative (zField C i.succ η) K u| ≤ |MZ i| * ν u ^ (1 - Q) :=
    fun i => (hMZ i η hη u hP).trans (mul_le_mul_of_nonneg_right (le_abs_self _) hz.le)
  have e3 : |K u| ≤ |MK| * ν u ^ (1 - Q) :=
    (hMK η hη u hP).trans (mul_le_mul_of_nonneg_right (le_abs_self _) hz.le)
  have ha' : |a ξ| ≤ |Ba| := by simpa [Real.norm_eq_abs] using (hBa ξ hξ).trans (le_abs_self Ba)
  have hL' : |sumSquaresWithDrift C.Xl a ξ| ≤ |BL| := by
    simpa [Real.norm_eq_abs] using (hBL ξ hξ).trans (le_abs_self BL)
  have hX' : ∀ i : Fin q, |fieldDerivative (C.Xl i.succ) a ξ| ≤ |BX i| := fun i => by
    simpa [Real.norm_eq_abs] using (hBX i ξ hξ).trans (le_abs_self (BX i))
  have b1 : |a ξ * C.rightPoleError η K u| ≤ |Ba| * |ME| * ν u ^ (1 - Q) := by
    rw [abs_mul, hrpe]
    calc |a ξ| * |C.errorOp η K u| ≤ |Ba| * (|ME| * ν u ^ (1 - Q)) :=
          mul_le_mul ha' e1 (abs_nonneg _) (abs_nonneg _)
      _ = |Ba| * |ME| * ν u ^ (1 - Q) := by ring
  have b2 : |2 * ∑ i : Fin q, fieldDerivative (C.Xl i.succ) a ξ * C.zDeriv η i.succ K u| ≤
      2 * ∑ i : Fin q, |BX i| * |MZ i| * ν u ^ (1 - Q) := by
    rw [abs_mul, abs_two]
    refine mul_le_mul_of_nonneg_left ((Finset.abs_sum_le_sum_abs _ _).trans
      (Finset.sum_le_sum fun i _ => ?_)) (by norm_num)
    rw [abs_mul, hzD i]
    calc |fieldDerivative (C.Xl i.succ) a ξ| * |fieldDerivative (zField C i.succ η) K u|
        ≤ |BX i| * (|MZ i| * ν u ^ (1 - Q)) := mul_le_mul (hX' i) (e2 i) (abs_nonneg _) (abs_nonneg _)
      _ = |BX i| * |MZ i| * ν u ^ (1 - Q) := by ring
  have b3 : |sumSquaresWithDrift C.Xl a ξ * K u| ≤ |BL| * |MK| * ν u ^ (1 - Q) := by
    rw [abs_mul]
    calc |sumSquaresWithDrift C.Xl a ξ| * |K u| ≤ |BL| * (|MK| * ν u ^ (1 - Q)) :=
          mul_le_mul hL' e3 (abs_nonneg _) (abs_nonneg _)
      _ = |BL| * |MK| * ν u ^ (1 - Q) := by ring
  refine ⟨?_, ?_⟩
  · calc |C.errBracket K a η ξ| ≤ |a ξ * C.rightPoleError η K u| +
          |2 * ∑ i : Fin q, fieldDerivative (C.Xl i.succ) a ξ * C.zDeriv η i.succ K u| +
          |sumSquaresWithDrift C.Xl a ξ * K u| := abs_add_three _ _ _
      _ ≤ |Ba| * |ME| * ν u ^ (1 - Q) + 2 * ∑ i : Fin q, |BX i| * |MZ i| * ν u ^ (1 - Q) +
          |BL| * |MK| * ν u ^ (1 - Q) := add_le_add (add_le_add b1 b2) b3
      _ ≤ (|Ba| * |ME| + 2 * ∑ i : Fin q, |BX i| * |MZ i| + |BL| * |MK| + |MK|) *
            ν u ^ (1 - Q) := by
          rw [← Finset.sum_mul]
          nlinarith [mul_nonneg (abs_nonneg MK) hz.le]
  · calc |K u| ≤ |MK| * ν u ^ (1 - Q) := e3
      _ ≤ (|Ba| * |ME| + 2 * ∑ i : Fin q, |BX i| * |MZ i| + |BL| * |MK| + |MK|) *
            ν u ^ (1 - Q) := by
          refine mul_le_mul_of_nonneg_right ?_ hz.le
          have h1 : 0 ≤ |Ba| * |ME| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
          have h2 : 0 ≤ ∑ i : Fin q, |BX i| * |MZ i| :=
            Finset.sum_nonneg (fun i _ => mul_nonneg (abs_nonneg _) (abs_nonneg _))
          have h3 : 0 ≤ |BL| * |MK| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
          linarith

/-- Away from the pole the error bracket is bounded, uniformly for `η ∈ Kw`,
`ξ ∈ Kt` with `ρ ≤ ν(Θ η ξ)`: it is jointly continuous off the diagonal (it is `L̃_ξ` of the
jointly smooth `a(ξ) K(Θ(η, ξ))`) and the set is compact. -/
theorem exists_far_bound (hq : 0 < q) (ν₀ : G2.HomogeneousNorm C.G)
    (K : H1.FundamentalKernel C.G (C.driftModel hq ν₀)) {Kt Kw : Set (Fin (n + m) → ℝ)}
    (hKt : IsCompact Kt) (hKw : IsCompact Kw) (hKtU : Kt ⊆ C.U) (hKwU : Kw ⊆ C.U)
    {a : (Fin (n + m) → ℝ) → ℝ} (ha : ContDiffOn ℝ (⊤ : ℕ∞) a C.U)
    (ν : G2.HomogeneousNorm C.G) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ Mf : ℝ, ∀ η ∈ Kw, ∀ ξ ∈ Kt, ρ ≤ ν (C.Θ η ξ) → |C.errBracket K a η ξ| ≤ Mf := by
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
  obtain ⟨Mf, hMf⟩ := hFa.exists_bound_of_continuousOn
    ((continuousOn_errBracket K ha).mono hsub)
  refine ⟨Mf, fun η hη ξ hξ h => ?_⟩
  have := hMf (ξ, η) ⟨⟨hξ, hη⟩, h⟩
  simpa [Real.norm_eq_abs] using this

/-- The lower integral of the kernel over `Kt` is bounded uniformly in `η ∈ Kw`. -/
theorem exists_lintegral_bound_kernel (hq : 0 < q) (ν₀ : G2.HomogeneousNorm C.G)
    (K : H1.FundamentalKernel C.G (C.driftModel hq ν₀)) {Kt Kw : Set (Fin (n + m) → ℝ)}
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

/-- The lower integral of the error bracket over `Kt` is bounded uniformly in
`η ∈ Kw`. -/
theorem exists_lintegral_bound_errBracket (hq : 0 < q) (ν₀ : G2.HomogeneousNorm C.G)
    (K : H1.FundamentalKernel C.G (C.driftModel hq ν₀)) {Kt Kw : Set (Fin (n + m) → ℝ)}
    (hKt : IsCompact Kt) (hKw : IsCompact Kw) (hKtU : Kt ⊆ C.U) (hKwU : Kw ⊆ C.U)
    {a : (Fin (n + m) → ℝ) → ℝ} (ha : ContDiffOn ℝ (⊤ : ℕ∞) a C.U) :
    ∃ M₂ : ℝ≥0∞, M₂ < ⊤ ∧ ∀ η ∈ Kw, ∫⁻ ξ in Kt, ‖C.errBracket K a η ξ‖ₑ ≤ M₂ := by
  have hNZ : NeZero (n + m) := ⟨C.G.dimension_pos.ne'⟩
  obtain ⟨ν, ρ, M, hν, hρ0, hρ1, hnear⟩ := exists_near_bound hq ν₀ K hKt hKw hKtU hKwU ha
  obtain ⟨Mf, hMf⟩ := exists_far_bound hq ν₀ K hKt hKw hKtU hKwU ha ν hρ0
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
  have hpt : ∀ᵐ ξ ∂(volume.restrict Kt), ‖C.errBracket K a η ξ‖ₑ ≤
      ENNReal.ofReal (gn (C.Θ η ξ)) + ENNReal.ofReal |Mf| := by
    refine (ae_restrict_iff' hmeas).2 ?_
    filter_upwards [h0] with ξ hne hξ
    rw [Real.enorm_eq_ofReal_abs]
    by_cases hfar : ρ ≤ ν (C.Θ η ξ)
    · calc ENNReal.ofReal |C.errBracket K a η ξ| ≤ ENNReal.ofReal |Mf| :=
            ENNReal.ofReal_le_ofReal ((hMf η hη ξ hξ hfar).trans (le_abs_self _))
        _ ≤ _ := le_add_self
    · have hlt : ν (C.Θ η ξ) < ρ := not_le.1 hfar
      have hνpos : 0 < ν (C.Θ η ξ) := by
        refine G2.gauge_pos ν.gauge (C.theta_ne_zero (hKwU hη) (hKtU hξ) hne)
      have hb := (hnear η hη ξ hξ hνpos hlt).1
      have hind : gn (C.Θ η ξ) = |M| * ν (C.Θ η ξ) ^ (-((Q : ℝ) - 1)) := by
        simp only [gn]
        rw [Set.indicator_of_mem (show C.Θ η ξ ∈ {u | ν u ≤ ρ} from hlt.le)]
      have hz : ν (C.Θ η ξ) ^ (1 - (Q : ℤ)) = ν (C.Θ η ξ) ^ (-((Q : ℝ) - 1)) := by
        rw [← Real.rpow_intCast]
        congr 1
        push_cast
        ring
      calc ENNReal.ofReal |C.errBracket K a η ξ| ≤ ENNReal.ofReal (gn (C.Θ η ξ)) := by
            refine ENNReal.ofReal_le_ofReal (hb.trans ?_)
            rw [hind, ← hz]
            exact mul_le_mul_of_nonneg_right (le_abs_self M) (zpow_pos hνpos _).le
        _ ≤ _ := le_self_add
  calc ∫⁻ ξ in Kt, ‖C.errBracket K a η ξ‖ₑ
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

end Drift

end LiftedChart

end RothschildStein.P1
