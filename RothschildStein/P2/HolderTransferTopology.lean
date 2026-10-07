-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.HolderTransferForward
public import RothschildStein.G4.FirstExit
public import RothschildStein.G2.MaxGauge
public import RothschildStein.G1.ControlledBasics
public import RothschildStein.G1.WeightedTriangle

/-!
# Topology of the lifted chart used by the Hölder transfer

The facts about the topology of the control distance that the Hölder transfer needs, derived inside
the lifted chart (the `gauge_comparison` field) and from a first-exit lemma for controlled curves:

* Euclidean convergence implies convergence of the control distances at points of the chart
  neighborhood `U` (`d̃(ξ, ζ) → 0` as `ζ → ξ`) and at the base points `π (U)` (`d(x, y) → 0`);
* small control distance implies small Euclidean distance, uniformly on a compact set of centres,
  with no assumption on the weights;
* a compact set `K₁ ⊆ U` containing all the small lifted balls `B̃(η, t₁)`, `η ∈ K`;
* the lifted control balls inside `U` are Euclidean open; a function with finite Hölder
  seminorm on a Euclidean open subset of `U` is Euclidean continuous there.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Filter TopologicalSpace Metric
open scoped ENNReal Topology BigOperators
open RothschildStein.P1
namespace RothschildStein.P2
variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}

/-- Euclidean lower bound, uniform on a compact set of centres: small control distance
from a point of `K` forces a small Euclidean distance. By first exit; no condition on the
weights (BB Props 1.37/1.42). -/
theorem exists_norm_lt_of_controlDistance_lt {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω)
    {w : Fin k → ℕ+} {Z : Fin k → (Fin n → ℝ) → (Fin n → ℝ)}
    (hZ : ∀ i, ContinuousOn (Z i) Ω) {K : Set (Fin n → ℝ)} (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ ∀ x ∈ K, ∀ y, controlDistance Ω w Z x y < ENNReal.ofReal r →
      ‖y - x‖ < ε := by
  obtain ⟨ε₀, hε₀, hsub⟩ := hK.exists_cthickening_subset_open hΩ hKΩ
  have hK₂ : IsCompact (Metric.cthickening ε₀ K) := hK.cthickening
  have hc : ContinuousOn (fun z => ∑ i, ‖Z i z‖) (Metric.cthickening ε₀ K) :=
    continuousOn_finsetSum Finset.univ (fun i _ => (hZ i).norm.mono hsub)
  obtain ⟨M, hM⟩ := hK₂.exists_bound_of_continuousOn hc
  set C' : ℝ := |M| + 1 with hC'
  have hC : 0 < C' := by positivity
  set R : ℝ := min ε ε₀ with hRdef
  have hR : 0 < R := lt_min hε hε₀
  have hmin : 0 < min 1 (R / C') := lt_min zero_lt_one (div_pos hR hC)
  refine ⟨min 1 (R / C') / 2, half_pos hmin, fun x hx y hy => ?_⟩
  obtain ⟨δ, hδ, hδr, γ, hγ, hz, ho⟩ := G1.exists_controlledCurve_of_controlDistance_lt hy
  have hδm : δ < min 1 (R / C') := hδr.trans (half_lt_self hmin)
  have hδ1 : δ ≤ 1 := hδm.le.trans (min_le_left _ _)
  have hsmall : δ * C' < R := (lt_div_iff₀ hC).mp (hδm.trans_le (min_le_right _ _))
  have hbound : ∀ z, ‖z - γ 0‖ ≤ R → ∑ i, ‖Z i z‖ ≤ C' := by
    intro z hz'
    rw [hz] at hz'
    have hzK : z ∈ Metric.cthickening ε₀ K :=
      Metric.mem_cthickening_of_dist_le z x ε₀ K hx
        (by rw [dist_eq_norm]; exact hz'.trans (min_le_right _ _))
    have h1 := hM z hzK
    rw [Real.norm_eq_abs] at h1
    linarith [le_abs_self (∑ i, ‖Z i z‖), le_abs_self M]
  have hd := G4.controlledCurve_displacement_le_in_buffer hγ hδ1 hC.le hR hsmall hbound
    (t := 1) ⟨zero_le_one, le_rfl⟩
  rw [ho, hz] at hd
  exact lt_of_le_of_lt hd (hsmall.trans_le (min_le_left _ _))

/-- inside the chart: Euclidean convergence implies convergence of the lifted control
distance at every point `ξ` of `U` (the `gauge_comparison` field and continuity of `Θ ξ`). -/
theorem exists_dl_lt_of_euclid_close (C : LiftedChart w s Ω hΩ X x₀ m)
    {ξ : Fin (n + m) → ℝ} (hξ : ξ ∈ C.U) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ' : ℝ, 0 < δ' ∧ ∀ ζ, ‖ζ - ξ‖ < δ' → ζ ∈ C.U ∧ C.dl ξ ζ < ENNReal.ofReal ε := by
  obtain ⟨Cρ, hCρ1, hgauge⟩ := C.gauge_comparison
  have hCρ : 0 < Cρ := lt_of_lt_of_le zero_lt_one hCρ1
  have hΘc : ContinuousOn (fun ζ => C.Θ ξ ζ) C.U := by
    have h1 := C.theta_smooth.continuousOn
    exact h1.comp (Continuous.continuousOn (continuous_const.prodMk continuous_id))
      (fun ζ hζ => ⟨hξ, hζ⟩)
  have hΘat : ContinuousAt (fun ζ => C.Θ ξ ζ) ξ := hΘc.continuousAt (C.isOpen_U.mem_nhds hξ)
  have hg : ContinuousAt (fun ζ => rsGauge C.G.weight C.G.weight_pos (C.Θ ξ ζ)) ξ :=
    (G2.continuous_gauge C.G).continuousAt.comp hΘat
  have hg0 : rsGauge C.G.weight C.G.weight_pos (C.Θ ξ ξ) = 0 := by
    rw [(C.chart ξ hξ).2.2.2.2]
    exact (G2.gauge_eq_zero_iff C.G 0).mpr rfl
  have hev : ∀ᶠ ζ in 𝓝 ξ, rsGauge C.G.weight C.G.weight_pos (C.Θ ξ ζ) < ε / Cρ ∧ ζ ∈ C.U := by
    refine (hg.eventually (gt_mem_nhds ?_)).and (C.isOpen_U.mem_nhds hξ)
    show rsGauge C.G.weight C.G.weight_pos (C.Θ ξ ξ) < ε / Cρ
    rw [hg0]
    positivity
  obtain ⟨δ', hδ', hball⟩ := Metric.eventually_nhds_iff.mp hev
  refine ⟨δ', hδ', fun ζ hζ => ?_⟩
  obtain ⟨h1, h2⟩ := hball (by rwa [dist_eq_norm])
  refine ⟨h2, ?_⟩
  have hle := (hgauge ξ hξ ζ h2).2
  refine lt_of_le_of_lt hle ((ENNReal.ofReal_lt_ofReal_iff hε).2 ?_)
  rw [mul_comm]
  exact (lt_div_iff₀ hCρ).mp h1

/-- The chart neighborhood lies in the lifted domain `O`. -/
theorem holderTransfer_U_subset_O (C : LiftedChart w s Ω hΩ X x₀ m) : C.U ⊆ C.O :=
  fun _ hξ => C.closure_U_subset (subset_closure hξ)

/-- at the base: Euclidean convergence `y → x` implies `d(x, y) → 0` at every point
`x = π ξ`, `ξ ∈ U` (through the lift `(y, tail ξ)` and `d ≤ d̃`). -/
theorem exists_controlDistance_lt_of_euclid_close (C : LiftedChart w s Ω hΩ X x₀ m)
    {x : Fin n → ℝ} (hx : x ∈ basePoint '' C.U) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ' : ℝ, 0 < δ' ∧ ∀ y, ‖y - x‖ < δ' →
      y ∈ basePoint '' C.U ∧ controlDistance Ω w X x y < ENNReal.ofReal ε := by
  obtain ⟨ξ₀, hξ₀, rfl⟩ := hx
  obtain ⟨δ', hδ', hball⟩ := exists_dl_lt_of_euclid_close C hξ₀ hε
  have hcont : Continuous (fun y : Fin n → ℝ => joinPoint y (tailPoint ξ₀ : Fin m → ℝ)) :=
    continuous_joinPoint_left _
  have h0 : joinPoint (basePoint ξ₀) (tailPoint ξ₀) = ξ₀ := joinPoint_basePoint_tailPoint ξ₀
  have hmem : {y : Fin n → ℝ | ‖joinPoint y (tailPoint ξ₀ : Fin m → ℝ) - ξ₀‖ < δ'} ∈
      𝓝 (basePoint ξ₀) := by
    have hopen : IsOpen {y : Fin n → ℝ | ‖joinPoint y (tailPoint ξ₀ : Fin m → ℝ) - ξ₀‖ < δ'} :=
      isOpen_lt (continuous_norm.comp (hcont.sub continuous_const)) continuous_const
    refine hopen.mem_nhds ?_
    simp only [mem_ofPred_eq, h0, sub_self, norm_zero]
    exact hδ'
  obtain ⟨δ'', hδ'', hsub⟩ := Metric.mem_nhds_iff.mp hmem
  refine ⟨δ'', hδ'', fun y hy => ?_⟩
  have hy' : y ∈ Metric.ball (basePoint ξ₀) δ'' := by rwa [mem_ball, dist_eq_norm]
  obtain ⟨hU, hd⟩ := hball _ (hsub hy')
  refine ⟨⟨_, hU, basePoint_joinPoint y _⟩, ?_⟩
  calc controlDistance Ω w X (basePoint ξ₀) y
      = controlDistance Ω w X (basePoint ξ₀) (basePoint (joinPoint y (tailPoint ξ₀ : Fin m → ℝ))) := by
        rw [basePoint_joinPoint]
    _ ≤ C.dl ξ₀ (joinPoint y (tailPoint ξ₀ : Fin m → ℝ)) :=
        controlDistance_basePoint_le Ω w X C.P _ _
    _ < _ := hd

/-- For a compact `K ⊆ U` there is a compact
`K₁ ⊆ U` and `t₁ > 0` such that every lifted ball `B̃(η, t₁)`, `η ∈ K`, lies in `K₁`
(Euclidean thickening and the uniform first-exit bound). -/
theorem exists_compact_lifts (C : LiftedChart w s Ω hΩ X x₀ m) {K : Set (Fin (n + m) → ℝ)}
    (hK : IsCompact K) (hKU : K ⊆ C.U) :
    ∃ K₁ : Set (Fin (n + m) → ℝ), IsCompact K₁ ∧ K₁ ⊆ C.U ∧ K ⊆ K₁ ∧
      ∃ t₁ : ℝ, 0 < t₁ ∧ ∀ η ∈ K, ∀ ζ, C.dl η ζ < ENNReal.ofReal t₁ → ζ ∈ K₁ := by
  obtain ⟨ε₁, hε₁, hsub⟩ := hK.exists_cthickening_subset_open C.isOpen_U hKU
  have hOopen : IsOpen C.O := hΩ.preimage continuous_basePoint
  have hKO : K ⊆ C.O := hKU.trans (holderTransfer_U_subset_O C)
  obtain ⟨r, hr, hclose⟩ := exists_norm_lt_of_controlDistance_lt (w := w) hOopen
    (fun i => (C.lift_smooth i).continuousOn) hK hKO hε₁
  refine ⟨Metric.cthickening ε₁ K, hK.cthickening, hsub, Metric.self_subset_cthickening K,
    r, hr, fun η hη ζ hζ => ?_⟩
  exact Metric.mem_cthickening_of_dist_le ζ η ε₁ K hη
    (by rw [dist_eq_norm]; exact (hclose η hη ζ hζ).le)

/-- A control ball contained in a set `N ⊆ Ω` at whose points Euclidean convergence implies
convergence of the control distance is Euclidean open (triangle inequality). -/
theorem isOpen_rsBall_of_close {n' k' : ℕ} {Ω' : Set (Fin n' → ℝ)} {w' : Fin k' → ℕ+}
    {X' : Fin k' → (Fin n' → ℝ) → (Fin n' → ℝ)} {N : Set (Fin n' → ℝ)} (hNΩ : N ⊆ Ω')
    (hclose : ∀ x ∈ N, ∀ ε : ℝ, 0 < ε → ∃ δ' : ℝ, 0 < δ' ∧ ∀ y, ‖y - x‖ < δ' →
      y ∈ N ∧ controlDistance Ω' w' X' x y < ENNReal.ofReal ε)
    {p : Fin n' → ℝ} {r : ℝ} (hsub : rsBall Ω' w' X' p r ⊆ N) :
    IsOpen (rsBall Ω' w' X' p r) := by
  rw [isOpen_iff_mem_nhds]
  intro ξ hξ
  have hdlt : controlDistance Ω' w' X' p ξ < ENNReal.ofReal r := hξ.2
  have hfin : controlDistance Ω' w' X' p ξ ≠ ⊤ := ne_top_of_lt hdlt
  have hr : 0 < r := ENNReal.ofReal_pos.mp (lt_of_le_of_lt bot_le hdlt)
  set a : ℝ := (controlDistance Ω' w' X' p ξ).toReal with ha
  have ha0 : 0 ≤ a := ENNReal.toReal_nonneg
  have haeq : ENNReal.ofReal a = controlDistance Ω' w' X' p ξ := ENNReal.ofReal_toReal hfin
  have har : a < r := (ENNReal.ofReal_lt_ofReal_iff hr).mp (by rwa [haeq])
  obtain ⟨δ', hδ', hball⟩ := hclose ξ (hsub hξ) (r - a) (sub_pos.mpr har)
  refine Metric.mem_nhds_iff.mpr ⟨δ', hδ', fun ζ hζ => ?_⟩
  obtain ⟨hU, hd⟩ := hball ζ (by rwa [mem_ball, dist_eq_norm] at hζ)
  refine ⟨hNΩ hU, ?_⟩
  calc controlDistance Ω' w' X' p ζ ≤ controlDistance Ω' w' X' p ξ + controlDistance Ω' w' X' ξ ζ :=
        G1.controlDistance_triangle Ω' w' X' p ξ ζ
    _ < ENNReal.ofReal a + ENNReal.ofReal (r - a) := by
        rw [haeq]
        exact ENNReal.add_lt_add_left hfin hd
    _ = ENNReal.ofReal r := by
        rw [← ENNReal.ofReal_add ha0 (sub_nonneg.mpr har.le)]
        congr 1
        ring

/-- The lifted control balls contained in `U` are Euclidean open. -/
theorem isOpen_rsBall_lifted (C : LiftedChart w s Ω hΩ X x₀ m) {η : Fin (n + m) → ℝ} {r : ℝ}
    (hsub : rsBall C.O w C.Xl η r ⊆ C.U) : IsOpen (rsBall C.O w C.Xl η r) :=
  isOpen_rsBall_of_close (holderTransfer_U_subset_O C)
    (fun ξ hξ ε hε => by
      obtain ⟨δ', hδ', hball⟩ := exists_dl_lt_of_euclid_close C hξ hε
      exact ⟨δ', hδ', hball⟩) hsub

/-- A finite Hölder seminorm gives the pointwise bound with its real value. -/
theorem abs_sub_le_of_holderSeminorm {d : (Fin n → ℝ) → (Fin n → ℝ) → ℝ≥0∞} {α : ℝ}
    (hα : 0 ≤ α) {V : Set (Fin n → ℝ)} {f : (Fin n → ℝ) → ℝ}
    (hf : holderSeminorm d α V f ≠ ⊤) {x y : Fin n → ℝ} (hx : x ∈ V) (hy : y ∈ V)
    (hxy : d x y ≠ ⊤) :
    |f x - f y| ≤ (holderSeminorm d α V f).toReal * (d x y).toReal ^ α := by
  have hset : {C : ℝ≥0∞ | C < ⊤ ∧ ∀ x ∈ V, ∀ y ∈ V, d x y < ⊤ →
      ENNReal.ofReal |f x - f y| ≤ C * d x y ^ α}.Nonempty := by
    by_contra hne
    rw [not_nonempty_iff_eq_empty] at hne
    exact hf (by unfold holderSeminorm; rw [hne, sInf_empty])
  have hpow : d x y ^ α ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hα hxy
  have hle : ENNReal.ofReal |f x - f y| ≤ holderSeminorm d α V f * d x y ^ α := by
    obtain ⟨C0, hC0⟩ := hset
    unfold holderSeminorm
    rw [sInf_eq_iInf', ENNReal.iInf_mul' (fun h => absurd h hpow) (fun _ => ⟨⟨C0, hC0⟩⟩)]
    exact le_iInf fun C => C.2.2 x hx y hy (lt_top_iff_ne_top.mpr hxy)
  have hrhs : holderSeminorm d α V f * d x y ^ α ≠ ⊤ := ENNReal.mul_ne_top hf hpow
  have := ENNReal.toReal_mono hrhs hle
  rwa [ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_mul, ← ENNReal.toReal_rpow] at this

/-- A function with finite Hölder seminorm (exponent `α > 0`) with respect to `d̃` on a Euclidean
open subset `A ⊆ U` of the chart is Euclidean continuous on `A`. -/
theorem continuousOn_of_holderSeminorm_ne_top (C : LiftedChart w s Ω hΩ X x₀ m)
    {A : Set (Fin (n + m) → ℝ)} (hA : IsOpen A) (hAU : A ⊆ C.U) {α : ℝ} (hα : 0 < α)
    {g : (Fin (n + m) → ℝ) → ℝ} (hg : holderSeminorm C.dl α A g ≠ ⊤) : ContinuousOn g A := by
  intro ξ hξ
  apply ContinuousAt.continuousWithinAt
  rw [Metric.continuousAt_iff]
  intro ε hε
  set M : ℝ := (holderSeminorm C.dl α A g).toReal + 1 with hM
  have hM0 : 0 < M := by positivity
  set ε₂ : ℝ := (ε / (2 * M)) ^ α⁻¹ with hε₂
  have hε₂0 : 0 < ε₂ := Real.rpow_pos_of_pos (by positivity) _
  obtain ⟨δ₁, hδ₁, hball⟩ := exists_dl_lt_of_euclid_close C (hAU hξ) hε₂0
  obtain ⟨δ₂, hδ₂, hAball⟩ := Metric.isOpen_iff.mp hA ξ hξ
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun ζ hζ => ?_⟩
  rw [dist_eq_norm] at hζ
  have hζA : ζ ∈ A := hAball (by rw [mem_ball, dist_eq_norm]; exact hζ.trans_le (min_le_right _ _))
  obtain ⟨-, hd⟩ := hball ζ (hζ.trans_le (min_le_left _ _))
  have hdfin : C.dl ξ ζ ≠ ⊤ := ne_top_of_lt (hd.trans ENNReal.ofReal_lt_top)
  have habs := abs_sub_le_of_holderSeminorm hα.le hg hξ hζA hdfin
  have hdt : (C.dl ξ ζ).toReal < ε₂ := ENNReal.toReal_lt_of_lt_ofReal hd
  have hpow : (C.dl ξ ζ).toReal ^ α < ε / (2 * M) := by
    calc (C.dl ξ ζ).toReal ^ α < ε₂ ^ α :=
          Real.rpow_lt_rpow ENNReal.toReal_nonneg hdt hα
      _ = ε / (2 * M) := Real.rpow_inv_rpow (by positivity) hα.ne'
  have hM1 : (holderSeminorm C.dl α A g).toReal ≤ M := by rw [hM]; linarith
  have hnn : 0 ≤ (C.dl ξ ζ).toReal ^ α := Real.rpow_nonneg ENNReal.toReal_nonneg _
  rw [Real.dist_eq, abs_sub_comm]
  calc |g ξ - g ζ| ≤ (holderSeminorm C.dl α A g).toReal * (C.dl ξ ζ).toReal ^ α := habs
    _ ≤ M * (C.dl ξ ζ).toReal ^ α := mul_le_mul_of_nonneg_right hM1 hnn
    _ < M * (ε / (2 * M)) := mul_lt_mul_of_pos_left hpow hM0
    _ = ε / 2 := by field_simp
    _ < ε := by linarith

/-- A function `f` on the base all of whose points over `S` have a
lift in a Euclidean open `A ⊆ U` where `f ∘ π` has finite Hölder seminorm is Euclidean continuous on
`S`: near a lift point an open product neighborhood supplies a fixed fiber coordinate `h` with
`f(y) = f̃(y, h)`, and `f̃` is continuous because Euclidean convergence implies `d̃`-convergence. -/
theorem continuousOn_of_lifts (C : LiftedChart w s Ω hΩ X x₀ m) {A : Set (Fin (n + m) → ℝ)}
    (hA : IsOpen A) (hAU : A ⊆ C.U) {α : ℝ} (hα : 0 < α) {S : Set (Fin n → ℝ)}
    (hS : ∀ y ∈ S, ∃ ζ ∈ A, basePoint ζ = y) {f : (Fin n → ℝ) → ℝ}
    (hsem : holderSeminorm C.dl α A (fun ξ => f (basePoint ξ)) ≠ ⊤) : ContinuousOn f S := by
  have hfc : ContinuousOn (fun ξ => f (basePoint ξ)) A :=
    continuousOn_of_holderSeminorm_ne_top C hA hAU hα hsem
  intro y hy
  obtain ⟨ζ, hζ, hζy⟩ := hS y hy
  have hι : Continuous (fun y' : Fin n → ℝ => joinPoint y' (tailPoint ζ : Fin m → ℝ)) :=
    continuous_joinPoint_left _
  have hιy : joinPoint y (tailPoint ζ : Fin m → ℝ) = ζ := by
    rw [← hζy]
    exact joinPoint_basePoint_tailPoint ζ
  have hat : ContinuousAt (fun ξ => f (basePoint ξ)) (joinPoint y (tailPoint ζ : Fin m → ℝ)) := by
    rw [hιy]
    exact hfc.continuousAt (hA.mem_nhds hζ)
  have hcomp := ContinuousAt.comp (g := fun ξ => f (basePoint ξ))
    (f := fun y' : Fin n → ℝ => joinPoint y' (tailPoint ζ : Fin m → ℝ)) (x := y) hat
    hι.continuousAt
  refine ContinuousAt.continuousWithinAt ?_
  have hfun : f = (fun ξ => f (basePoint ξ)) ∘ (fun y' : Fin n → ℝ =>
      joinPoint y' (tailPoint ζ : Fin m → ℝ)) := by
    funext y'
    simp [basePoint_joinPoint]
  rw [hfun]
  exact hcomp

end RothschildStein.P2
