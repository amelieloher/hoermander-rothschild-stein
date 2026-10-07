-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.ContinuityPositiveShell
public import RothschildStein.P1.SchurLpNorm

/-!
# Sobolev interpolation, near part: dyadic shells and the Schur bound for dominating kernels

The near and far parts of the Sobolev interpolation inequality are bounded by integral operators whose kernels are explicit
functions of the lifted distance:

* near: `A d̃^(1-Q) 1_{d̃ ≤ 2b}` (row and column integrals `≤ C A b`, `shell_lintegral_le_ball`);
* far: `B max(d̃, a)^(-(Q+1))` (row and column integrals `≤ C B / a`,
  `shell_lintegral_max_le`, from the dyadic shells `{2^j a ≤ d̃ ≤ 2^(j+1) a}` as for the restricted error
  with a geometric sum, `shell_lintegral_far_pow_le`).

`eLpNorm_le_of_row_col_bound` is Schur's test for a nonnegative jointly measurable kernel
dominating an operator pointwise; `LiftedChart.eLpNorm_le_of_dl_dominated` specialises it to kernels
`φ(d̃(x, y))` cut to `S × S` (`dlKernel`), whose measurability follows from the continuity of `d̃`
on `U × U` (`continuousOn_dl_toReal`). (BB pp. 544, 581–583.)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal Topology
namespace RothschildStein.P2

open RothschildStein.P1

section Abstract

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} {S : Set E} {dr : E → E → ℝ} {q : ℕ}
  {ρ Cv : ℝ}

/-- **Far integral with the extra decay `dr^(-(q+2))`**: if `S` has the homogeneous ball bound
`μ(S ∩ {dr x · < t}) ≤ Cv t^(q+1)`, then `∫_{a ≤ dr} c / dr^(q+2) ≤ 2 c Cv 2^(q+1) / a` (the dyadic
shell `{2^j a ≤ dr ≤ 2^(j+1) a}` contributes `c Cv 2^(q+1) / (2^j a)`, a geometric series). -/
theorem shell_lintegral_far_pow_le (h : ShellData μ S dr q ρ Cv) {x : E} (hx : x ∈ S) {c a : ℝ}
    (hc : 0 ≤ c) (ha : 0 < a) :
    ∫⁻ y in S ∩ {y | a ≤ dr x y}, ENNReal.ofReal (c / dr x y ^ (q + 2)) ∂μ ≤
      ENNReal.ofReal (2 * (c * (Cv * 2 ^ (q + 1))) / a) := by
  set K : ℝ := c * (Cv * 2 ^ (q + 1)) with hK
  have hK0 : 0 ≤ K := mul_nonneg hc (mul_nonneg h.Cv_nonneg (by positivity))
  set a' : ℕ → ℝ := fun j => 2 ^ j * a with ha'
  have hapos : ∀ j, 0 < a' j := fun j => by simp only [ha']; positivity
  have hcover : S ∩ {y | a ≤ dr x y} ⊆ ⋃ j, shell S dr x (a' j) := by
    rintro y ⟨hyS, hya⟩
    obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near (x := dr x y / a) (y := (2 : ℝ))
      ((one_le_div ha).mpr hya) one_lt_two
    refine mem_iUnion.mpr ⟨n, hyS, ?_, ?_⟩
    · have := (le_div_iff₀ ha).mp hn1
      simpa [ha'] using this
    · have := (div_lt_iff₀ ha).mp hn2
      simp only [ha']
      rw [pow_succ] at this
      linarith
  have hterm : ∀ j, ∫⁻ y in shell S dr x (a' j), ENNReal.ofReal (c / dr x y ^ (q + 2)) ∂μ ≤
      ENNReal.ofReal (K * (1 / a) * (1 / 2) ^ j) := by
    intro j
    refine (h.lintegral_shell_le hx (hapos j) hc (q + 2)).trans (le_of_eq ?_)
    congr 1
    have hp : 0 < a' j := hapos j
    have e : a' j = 2 ^ j * a := rfl
    have h2 : (0 : ℝ) < 2 ^ j := by positivity
    have e2 : (a' j) ^ (q + 2) = (a' j) ^ (q + 1) * a' j := pow_succ (a' j) (q + 1)
    rw [hK, e, one_div, one_div, inv_pow]
    have e3 : (2 * (2 ^ j * a)) ^ (q + 1) = 2 ^ (q + 1) * (2 ^ j * a) ^ (q + 1) := mul_pow _ _ _
    have e4 : (2 ^ j * a) ^ (q + 2) = (2 ^ j * a) ^ (q + 1) * (2 ^ j * a) := pow_succ _ _
    rw [e3, e4]
    field_simp
  calc ∫⁻ y in S ∩ {y | a ≤ dr x y}, ENNReal.ofReal (c / dr x y ^ (q + 2)) ∂μ
      ≤ ∫⁻ y in ⋃ j, shell S dr x (a' j), ENNReal.ofReal (c / dr x y ^ (q + 2)) ∂μ :=
        lintegral_mono_set hcover
    _ ≤ ∑' j, ∫⁻ y in shell S dr x (a' j), ENNReal.ofReal (c / dr x y ^ (q + 2)) ∂μ :=
        lintegral_iUnion_le _ _
    _ ≤ ∑' j : ℕ, ENNReal.ofReal (K * (1 / a) * (1 / 2) ^ j) := ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal (2 * K / a) := by
        have hnn : ∀ j : ℕ, 0 ≤ K * (1 / a) * (1 / 2) ^ j := fun j => by positivity
        have hsum : Summable (fun j : ℕ => K * (1 / a) * (1 / 2) ^ j) :=
          (summable_geometric_two).mul_left (K * (1 / a))
        rw [← ENNReal.ofReal_tsum_of_nonneg hnn hsum, tsum_mul_left, tsum_geometric_two]
        congr 1
        field_simp

/-- **`∫ c / max(dr, a)^(q+2) ≤ C c / a`** over `S`: the ball `{dr < a}` carries the constant
value `c / a^(q+2)` and the volume bound, the rest is the far integral. -/
theorem shell_lintegral_max_le (h : ShellData μ S dr q ρ Cv) {x : E} (hx : x ∈ S) {c a : ℝ}
    (hc : 0 ≤ c) (ha : 0 < a) :
    ∫⁻ y in S, ENNReal.ofReal (c / (max (dr x y) a) ^ (q + 2)) ∂μ ≤
      ENNReal.ofReal (c * Cv / a + 2 * (c * (Cv * 2 ^ (q + 1))) / a) := by
  set B : Set E := S ∩ {y | dr x y < a} with hB
  have hBm : MeasurableSet B := h.measurableSet_ball_all hx a
  have hsplit := lintegral_inter_add_sdiff (μ := μ)
    (fun y => ENNReal.ofReal (c / (max (dr x y) a) ^ (q + 2))) S hBm
  have e1 : S ∩ B = B := inter_eq_right.mpr inter_subset_left
  have e2 : S \ B = S ∩ {y | a ≤ dr x y} := by
    ext y
    simp only [hB, Set.mem_sdiff, mem_inter_iff, mem_ofPred_eq, not_and, not_lt]
    exact ⟨fun hy => ⟨hy.1, hy.2 hy.1⟩, fun hy => ⟨hy.1, fun _ => hy.2⟩⟩
  rw [e1, e2] at hsplit
  rw [← hsplit]
  have hB1 : ∫⁻ y in B, ENNReal.ofReal (c / (max (dr x y) a) ^ (q + 2)) ∂μ ≤
      ENNReal.ofReal (c * Cv / a) := by
    have hcongr : ∫⁻ y in B, ENNReal.ofReal (c / (max (dr x y) a) ^ (q + 2)) ∂μ =
        ∫⁻ y in B, ENNReal.ofReal (c / a ^ (q + 2)) ∂μ :=
      setLIntegral_congr_fun hBm (fun y hy => by rw [max_eq_right hy.2.le])
    rw [hcongr, setLIntegral_const]
    calc ENNReal.ofReal (c / a ^ (q + 2)) * μ B
        ≤ ENNReal.ofReal (c / a ^ (q + 2)) * ENNReal.ofReal (Cv * a ^ (q + 1)) :=
          mul_le_mul_right (h.measure_ball_le_all hx ha) _
      _ = ENNReal.ofReal (c * Cv / a) := by
          rw [← ENNReal.ofReal_mul (div_nonneg hc (by positivity))]
          congr 1
          field_simp
          ring
  have hmeas : MeasurableSet (S ∩ {y | a ≤ dr x y}) := by
    rw [← e2]
    exact h.measurableSet.diff hBm
  have hB2 : ∫⁻ y in S ∩ {y | a ≤ dr x y},
      ENNReal.ofReal (c / (max (dr x y) a) ^ (q + 2)) ∂μ ≤
      ENNReal.ofReal (2 * (c * (Cv * 2 ^ (q + 1))) / a) := by
    have hcongr : ∫⁻ y in S ∩ {y | a ≤ dr x y},
        ENNReal.ofReal (c / (max (dr x y) a) ^ (q + 2)) ∂μ =
        ∫⁻ y in S ∩ {y | a ≤ dr x y}, ENNReal.ofReal (c / dr x y ^ (q + 2)) ∂μ :=
      setLIntegral_congr_fun hmeas (fun y hy => by rw [max_eq_left hy.2])
    rw [hcongr]
    exact shell_lintegral_far_pow_le h hx hc ha
  calc _ ≤ ENNReal.ofReal (c * Cv / a) + ENNReal.ofReal (2 * (c * (Cv * 2 ^ (q + 1))) / a) :=
        add_le_add hB1 hB2
    _ = _ := by
        rw [← ENNReal.ofReal_add (div_nonneg (mul_nonneg hc h.Cv_nonneg) ha.le)
          (div_nonneg (mul_nonneg zero_le_two (mul_nonneg hc (mul_nonneg h.Cv_nonneg
            (by positivity)))) ha.le)]

/-- **Near integral of a function supported in the ball**: if `F ≤ c / dr^q` on `S ∩ {dr ≤ b}`
and `F = 0` on the rest of `S`, then `∫_S F ≤ c Cv 2^(q+1) b`. -/
theorem shell_lintegral_le_ball (h : ShellData μ S dr q ρ Cv) {x : E} (hx : x ∈ S)
    {F : E → ℝ≥0∞} {c b : ℝ} (hc : 0 ≤ c) (hb : 0 ≤ b)
    (hF : ∀ y ∈ S, F y ≤ if dr x y ≤ b then ENNReal.ofReal (c / dr x y ^ q) else 0) :
    ∫⁻ y in S, F y ∂μ ≤ ENNReal.ofReal (c * (Cv * 2 ^ (q + 1)) * b) := by
  classical
  set T : Set E := S ∩ {y | dr x y ≤ b} with hT
  have hTm : MeasurableSet T := h.measurableSet_closedBall hx b
  calc ∫⁻ y in S, F y ∂μ
      ≤ ∫⁻ y in S, T.indicator (fun y => ENNReal.ofReal (c / dr x y ^ q)) y ∂μ := by
        refine setLIntegral_mono' h.measurableSet (fun y hy => ?_)
        by_cases hyb : dr x y ≤ b
        · have : y ∈ T := ⟨hy, hyb⟩
          rw [indicator_of_mem this]
          simpa [hyb] using hF y hy
        · have : y ∉ T := fun hyT => hyb hyT.2
          rw [indicator_of_notMem this]
          simpa [hyb] using hF y hy
    _ = ∫⁻ y in T, ENNReal.ofReal (c / dr x y ^ q) ∂μ := by
        rw [lintegral_indicator hTm, Measure.restrict_restrict hTm,
          inter_eq_left.mpr inter_subset_left]
    _ ≤ _ := h.lintegral_ball_le hx hc hb

/-- **Schur's test for a dominating kernel** (BB Prop 11.10): `K ≥ 0` jointly measurable
with row and column integrals `≤ Λ`; if `|T x| ≤ ∫ K(x, y) |g(y)| dy` almost everywhere then
`‖T‖_p ≤ Λ ‖g‖_p` for `1 ≤ p < ∞`. -/
theorem eLpNorm_le_of_row_col_bound (μ : Measure E) [SFinite μ] (K : E → E → ℝ)
    (hK : Measurable (Function.uncurry K)) (hK0 : ∀ x y, 0 ≤ K x y) {Λ : ℝ} (hΛ : 0 < Λ)
    (hrow : ∀ x, ∫⁻ y, ENNReal.ofReal (K x y) ∂μ ≤ ENNReal.ofReal Λ)
    (hcol : ∀ y, ∫⁻ x, ENNReal.ofReal (K x y) ∂μ ≤ ENNReal.ofReal Λ) {p : ℝ} (hp : 1 ≤ p)
    {g : E → ℝ} (hg : MemLp g (ENNReal.ofReal p) μ) {T : E → ℝ} (hTm : AEStronglyMeasurable T μ)
    (hT : ∀ᵐ x ∂μ, |T x| ≤ ∫ y, K x y * |g y| ∂μ) :
    eLpNorm T (ENNReal.ofReal p) μ ≤ ENNReal.ofReal Λ * eLpNorm g (ENNReal.ofReal p) μ := by
  have hrow' : ∀ x, ∫⁻ y, ‖K x y‖ₑ ∂μ ≤ ENNReal.ofReal Λ := fun x => by
    have : ∀ y, ‖K x y‖ₑ = ENNReal.ofReal (K x y) := fun y => Real.enorm_eq_ofReal (hK0 x y)
    simp only [this]
    exact hrow x
  have hcol' : ∀ y, ∫⁻ x, ‖K x y‖ₑ ∂μ ≤ ENNReal.ofReal Λ := fun y => by
    have : ∀ x, ‖K x y‖ₑ = ENNReal.ofReal (K x y) := fun x => Real.enorm_eq_ofReal (hK0 x y)
    simp only [this]
    exact hcol y
  have hgn : MemLp (fun y => ‖g y‖) (ENNReal.ofReal p) μ := hg.norm
  have hb := integralOperator_schur_eLpNorm_bound μ μ K hK (ENNReal.ofReal Λ)
    (ENNReal.ofReal Λ) ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top hrow' hcol'
    (fun y => ‖g y‖) hp hgn
  have hpos : ENNReal.ofReal Λ ≠ 0 := (ENNReal.ofReal_pos.mpr hΛ).ne'
  rw [← ENNReal.rpow_add _ _ hpos ENNReal.ofReal_ne_top, sub_add_cancel, ENNReal.rpow_one] at hb
  calc eLpNorm T (ENNReal.ofReal p) μ
      ≤ eLpNorm (fun x => ∫ y, K x y * ‖g y‖ ∂μ) (ENNReal.ofReal p) μ := by
        refine eLpNorm_mono_ae (f := T) (g := fun x => ∫ y, K x y * ‖g y‖ ∂μ) hTm ?_
        filter_upwards [hT] with x hx
        rw [Real.norm_eq_abs, Real.norm_eq_abs]
        exact hx.trans (le_abs_self _)
    _ ≤ ENNReal.ofReal Λ * eLpNorm (fun y => ‖g y‖) (ENNReal.ofReal p) μ := hb
    _ = ENNReal.ofReal Λ * eLpNorm g (ENNReal.ofReal p) μ := by
        rw [eLpNorm_norm g hg.aestronglyMeasurable]

end Abstract

section Profiles

/-- The cut-off profile `1` on `[0, b]`, `0` on `[2b, ∞)`, continuous in between. -/
def interpCut (b t : ℝ) : ℝ := min 1 (max 0 (2 - t / b))

theorem interpCut_nonneg (b t : ℝ) : 0 ≤ interpCut b t := le_min zero_le_one (le_max_left _ _)

theorem interpCut_le_one (b t : ℝ) : interpCut b t ≤ 1 := min_le_left _ _

theorem interpCut_eq_one {b t : ℝ} (hb : 0 < b) (ht : t ≤ b) : interpCut b t = 1 := by
  unfold interpCut
  refine min_eq_left (le_max_of_le_right ?_)
  have := (div_le_one hb).mpr ht
  linarith

theorem interpCut_eq_zero {b t : ℝ} (hb : 0 < b) (ht : 2 * b ≤ t) : interpCut b t = 0 := by
  unfold interpCut
  have h2 : 2 ≤ t / b := by
    rw [le_div_iff₀ hb]
    linarith
  rw [max_eq_left (by linarith)]
  exact min_eq_right zero_le_one

theorem continuous_interpCut (b : ℝ) : Continuous (interpCut b) := by
  unfold interpCut
  fun_prop

/-- The near profile `A θ_b(t) / t^q` (size `A d̃^(1-Q)` for `q = Q - 1`, cut at `2b`). -/
def interpNearProfile (A b : ℝ) (q : ℕ) (t : ℝ) : ℝ := A * interpCut b t / t ^ q

/-- The far profile `B / max(t, a)^(q+2)` (size `B d̃^(-Q-1)` for `q = Q - 1`, cut at `a`). -/
def interpFarProfile (B a : ℝ) (q : ℕ) (t : ℝ) : ℝ := B / (max t a) ^ (q + 2)

theorem measurable_interpNearProfile (A b : ℝ) (q : ℕ) : Measurable (interpNearProfile A b q) := by
  unfold interpNearProfile
  exact (measurable_const.mul (continuous_interpCut b).measurable).div (measurable_id.pow_const q)

theorem measurable_interpFarProfile (B a : ℝ) (q : ℕ) : Measurable (interpFarProfile B a q) := by
  unfold interpFarProfile
  exact measurable_const.div ((measurable_id.max measurable_const).pow_const (q + 2))

theorem interpNearProfile_nonneg {A b : ℝ} (hA : 0 ≤ A) (q : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ interpNearProfile A b q t :=
  div_nonneg (mul_nonneg hA (interpCut_nonneg b t)) (pow_nonneg ht q)

theorem interpFarProfile_nonneg {B a : ℝ} (hB : 0 ≤ B) (ha : 0 < a) (q : ℕ) {t : ℝ}
    (_ht : 0 ≤ t) : 0 ≤ interpFarProfile B a q t :=
  div_nonneg hB (pow_nonneg (le_max_of_le_right ha.le) _)

end Profiles

section Chart

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  (C : LiftedChart w s Ω hΩ X x₀ m)

/-- The lifted control distance is continuous on `U × U` (the metric topology of the carrier
is the Euclidean one). -/
theorem continuousOn_dl_toReal : ContinuousOn
    (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => (C.dl p.1 p.2).toReal)
    (C.U ×ˢ C.U) := by
  rw [continuousOn_iff_continuous_domRestrict]
  have hι : Continuous (fun p : ↥(C.U ×ˢ C.U) =>
      ((⟨p.1.1, p.2.1⟩ : C.Carrier), (⟨p.1.2, p.2.2⟩ : C.Carrier))) := by
    refine Continuous.prodMk ?_ ?_
    · exact LiftedChart.Carrier.isOpenEmbedding_val.isInducing.continuous_iff.2
        (continuous_fst.comp continuous_subtype_val)
    · exact LiftedChart.Carrier.isOpenEmbedding_val.isInducing.continuous_iff.2
        (continuous_snd.comp continuous_subtype_val)
  exact (continuous_dist (α := C.Carrier)).comp hι

/-- The kernel `φ(d̃(x, y))` cut to `S × S`. -/
def dlKernel (S : Set (Fin (n + m) → ℝ)) (φ : ℝ → ℝ) (x y : Fin (n + m) → ℝ) : ℝ :=
  (S ×ˢ S).indicator (fun p => φ (C.dl p.1 p.2).toReal) (x, y)

variable {C}
variable {S : Set (Fin (n + m) → ℝ)} {φ : ℝ → ℝ} {x y : Fin (n + m) → ℝ}

theorem dlKernel_of_mem (hx : x ∈ S) (hy : y ∈ S) : dlKernel C S φ x y = φ (C.dl x y).toReal :=
  Set.indicator_of_mem (s := S ×ˢ S) (a := (x, y)) ⟨hx, hy⟩
    (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => φ (C.dl p.1 p.2).toReal)

theorem dlKernel_of_not_mem (h : x ∉ S ∨ y ∉ S) : dlKernel C S φ x y = 0 := by
  refine indicator_of_notMem (s := S ×ˢ S) ?_ _
  rintro ⟨hx, hy⟩
  rcases h with h | h
  exacts [h hx, h hy]

/-- The cut kernel `φ(d̃(x, y))` of a Borel function `φ` is jointly measurable. -/
theorem measurable_dlKernel (hS : MeasurableSet S) (hSU : S ⊆ C.U) (hφ : Measurable φ) :
    Measurable (Function.uncurry (dlKernel C S φ)) := by
  classical
  have hSS : MeasurableSet (S ×ˢ S) := hS.prod hS
  have hD : ContinuousOn (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => (C.dl p.1 p.2).toReal)
      (S ×ˢ S) := (continuousOn_dl_toReal C).mono (prod_mono hSU hSU)
  have hDm : Measurable ((S ×ˢ S).piecewise
      (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => (C.dl p.1 p.2).toReal) (fun _ => 0)) :=
    ContinuousOn.measurable_piecewise hD continuousOn_const hSS
  have : Function.uncurry (dlKernel C S φ) = (S ×ˢ S).indicator
      (fun p => φ ((S ×ˢ S).piecewise
        (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => (C.dl p.1 p.2).toReal)
        (fun _ => 0) p)) := by
    funext p
    by_cases hp : p ∈ S ×ˢ S
    · simp [dlKernel, Function.uncurry, hp]
    · simp [dlKernel, Function.uncurry, hp]
  rw [this]
  exact (hφ.comp hDm).indicator hSS

/-- **Schur's test for a dominating kernel `φ(d̃)`** on a compact patch: if the row integrals
`∫_S φ(d̃(x, y)) dy` are `≤ Λ` and `|T x| ≤ ∫_V φ(d̃(x, y)) |g(y)| dy` on `V ⊆ S`, then
`‖T‖_{L^p(V)} ≤ Λ ‖g‖_{L^p(V)}` (the column integrals are the row integrals, `d̃` is symmetric). -/
theorem eLpNorm_le_of_dl_dominated {V : Set (Fin (n + m) → ℝ)} (hS : IsCompact S) (hSU : S ⊆ C.U)
    (hVS : V ⊆ S) (hV : MeasurableSet V) (hφm : Measurable φ) (hφ0 : ∀ t, 0 ≤ t → 0 ≤ φ t)
    {Λ : ℝ} (hΛ : 0 < Λ)
    (hrow : ∀ x ∈ S, ∫⁻ y in S, ENNReal.ofReal (φ (C.dl x y).toReal) ≤ ENNReal.ofReal Λ)
    {p : ℝ} (hp : 1 ≤ p) {g T : (Fin (n + m) → ℝ) → ℝ}
    (hg : MemLp g (ENNReal.ofReal p) (volume.restrict V))
    (hTm : AEStronglyMeasurable T (volume.restrict V))
    (hT : ∀ x ∈ V, |T x| ≤ ∫ y in V, φ (C.dl x y).toReal * |g y|) :
    eLpNorm T (ENNReal.ofReal p) (volume.restrict V) ≤
      ENNReal.ofReal Λ * eLpNorm g (ENNReal.ofReal p) (volume.restrict V) := by
  have hK := measurable_dlKernel hS.measurableSet hSU hφm
  have hK0 : ∀ x y, 0 ≤ dlKernel C S φ x y := by
    intro x y
    by_cases h : x ∈ S ∧ y ∈ S
    · rw [dlKernel_of_mem h.1 h.2]
      exact hφ0 _ ENNReal.toReal_nonneg
    · rw [dlKernel_of_not_mem (by tauto)]
  have hrowK : ∀ x, ∫⁻ y, ENNReal.ofReal (dlKernel C S φ x y) ∂(volume.restrict V) ≤
      ENNReal.ofReal Λ := by
    intro x
    by_cases hx : x ∈ S
    · calc ∫⁻ y, ENNReal.ofReal (dlKernel C S φ x y) ∂(volume.restrict V)
          ≤ ∫⁻ y, ENNReal.ofReal (dlKernel C S φ x y) ∂(volume.restrict S) :=
            lintegral_mono' (Measure.restrict_mono hVS le_rfl) le_rfl
        _ = ∫⁻ y in S, ENNReal.ofReal (φ (C.dl x y).toReal) :=
            setLIntegral_congr_fun hS.measurableSet (fun y hy => by rw [dlKernel_of_mem hx hy])
        _ ≤ ENNReal.ofReal Λ := hrow x hx
    · simp [dlKernel_of_not_mem (Or.inl hx)]
  have hcolK : ∀ y, ∫⁻ x, ENNReal.ofReal (dlKernel C S φ x y) ∂(volume.restrict V) ≤
      ENNReal.ofReal Λ := by
    intro y
    by_cases hy : y ∈ S
    · calc ∫⁻ x, ENNReal.ofReal (dlKernel C S φ x y) ∂(volume.restrict V)
          ≤ ∫⁻ x, ENNReal.ofReal (dlKernel C S φ x y) ∂(volume.restrict S) :=
            lintegral_mono' (Measure.restrict_mono hVS le_rfl) le_rfl
        _ = ∫⁻ x in S, ENNReal.ofReal (φ (C.dl y x).toReal) :=
            setLIntegral_congr_fun hS.measurableSet (fun x hx => by
              rw [dlKernel_of_mem hx hy, C.dl_symm x y])
        _ ≤ ENNReal.ofReal Λ := hrow y hy
    · simp [dlKernel_of_not_mem (Or.inr hy)]
  refine eLpNorm_le_of_row_col_bound (volume.restrict V) _ hK hK0 hΛ hrowK hcolK hp hg hTm ?_
  filter_upwards [ae_restrict_mem hV] with x hx
  refine (hT x hx).trans (le_of_eq ?_)
  refine setIntegral_congr_fun hV (fun y hy => ?_)
  rw [dlKernel_of_mem (hVS hx) (hVS hy)]

variable (C)

/-- **Row integrals of the near kernel**: for a compact `S ⊆ U` there is `Cn` with
`∫_S A θ_b(d̃(x, y)) d̃(x, y)^(1-Q) dy ≤ Cn A b` for every `A ≥ 0`, `b > 0`, `x ∈ S`
(dyadic balls and volume growth, `shell_lintegral_le_ball`). -/
theorem exists_near_row_bound (hS : IsCompact S) (hSU : S ⊆ C.U) :
    ∃ Cn : ℝ, 0 < Cn ∧ ∀ A b : ℝ, 0 ≤ A → 0 < b → ∀ x ∈ S,
      ∫⁻ y in S, ENNReal.ofReal (interpNearProfile A b (C.G.homogeneousDimension - 1)
        (C.dl x y).toReal) ≤ ENNReal.ofReal (Cn * A * b) := by
  obtain ⟨ρ, Cv, hsd⟩ := C.exists_shellData_patch hS hSU
  have hCv := hsd.Cv_nonneg
  refine ⟨(Cv + 1) * 2 ^ (C.G.homogeneousDimension - 1 + 1) * 2, by positivity, fun A b hA hb x hx => ?_⟩
  refine (shell_lintegral_le_ball hsd hx (F := fun y => ENNReal.ofReal (interpNearProfile A b
    (C.G.homogeneousDimension - 1) (C.dl x y).toReal)) (c := A) (b := 2 * b) hA (by positivity)
    (fun y hy => ?_)).trans (ENNReal.ofReal_le_ofReal ?_)
  · by_cases hyb : (C.dl x y).toReal ≤ 2 * b
    · rw [ite_eq_left hyb]
      refine ENNReal.ofReal_le_ofReal ?_
      unfold interpNearProfile
      exact div_le_div_of_nonneg_right (mul_le_of_le_one_right hA (interpCut_le_one _ _))
        (pow_nonneg ENNReal.toReal_nonneg _)
    · rw [ite_eq_right hyb]
      have : interpCut b (C.dl x y).toReal = 0 := interpCut_eq_zero hb (not_le.mp hyb).le
      simp [interpNearProfile, this]
  · have h2 : (0 : ℝ) ≤ A * (2 * b) := by positivity
    calc A * (Cv * 2 ^ (C.G.homogeneousDimension - 1 + 1)) * (2 * b)
        ≤ A * ((Cv + 1) * 2 ^ (C.G.homogeneousDimension - 1 + 1)) * (2 * b) := by gcongr; linarith
      _ = (Cv + 1) * 2 ^ (C.G.homogeneousDimension - 1 + 1) * 2 * A * b := by ring

/-- **Row integrals of the far kernel**: for a compact `S ⊆ U` there is `Cf` with
`∫_S B max(d̃(x, y), a)^(-(Q+1)) dy ≤ Cf B / a` for `B ≥ 0`, `a > 0`, `x ∈ S`
(`shell_lintegral_max_le`: the shells `{2^j a ≤ d̃ ≤ 2^(j+1) a}` and the volume growth). -/
theorem exists_far_row_bound (hS : IsCompact S) (hSU : S ⊆ C.U) :
    ∃ Cf : ℝ, 0 < Cf ∧ ∀ B a : ℝ, 0 ≤ B → 0 < a → ∀ x ∈ S,
      ∫⁻ y in S, ENNReal.ofReal (interpFarProfile B a (C.G.homogeneousDimension - 1)
        (C.dl x y).toReal) ≤ ENNReal.ofReal (Cf * B / a) := by
  obtain ⟨ρ, Cv, hsd⟩ := C.exists_shellData_patch hS hSU
  have hCv := hsd.Cv_nonneg
  refine ⟨(Cv + 1) * (1 + 2 * 2 ^ (C.G.homogeneousDimension - 1 + 1)), by positivity,
    fun B a hB ha x hx => ?_⟩
  refine (shell_lintegral_max_le hsd hx hB ha).trans (ENNReal.ofReal_le_ofReal ?_)
  have hp : (0 : ℝ) ≤ 2 ^ (C.G.homogeneousDimension - 1 + 1) := by positivity
  have e : B * Cv / a + 2 * (B * (Cv * 2 ^ (C.G.homogeneousDimension - 1 + 1))) / a =
      Cv * (1 + 2 * 2 ^ (C.G.homogeneousDimension - 1 + 1)) * B / a := by
    field_simp
  rw [e]
  have : Cv * (1 + 2 * 2 ^ (C.G.homogeneousDimension - 1 + 1)) ≤
      (Cv + 1) * (1 + 2 * 2 ^ (C.G.homogeneousDimension - 1 + 1)) := by
    gcongr; linarith
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right this hB) ha.le

end Chart

end RothschildStein.P2
