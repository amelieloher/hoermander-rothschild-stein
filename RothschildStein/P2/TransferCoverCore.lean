-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.NormTransfer
public import RothschildStein.P2.HolderTransfer
public import RothschildStein.P2.CutoffsGeometry
public import RothschildStein.H3.FiniteCoverSobolevNorm
public import RothschildStein.Definitions.driftWeight
public import RothschildStein.Definitions.noDriftWeight
public import RothschildStein.S.Sobolev
public import RothschildStein.S.HolderZeroOrder

/-!
# Transfer estimates: shared definitions and chart lemmas

This module collects what the Sobolev and the Hölder transfer-and-cover theorems share.

* The operator `L̃ = ∑_i X̃_{J i}` as a family of words `J : ι → List (Fin k)`; the drift operator
  `L = X_0 + ∑_{i ≥ 1} X_i²` is `driftOpWords q` (alphabet `Fin (q + 1)`, weight two at the
  letter `0`), the no-drift operator `L = ∑ X_i²` is `noDriftOpWords q` (alphabet `Fin q`).
  `HasWeakOperatorValue` (Sobolev, weak word derivatives, a.e. identity) and
  `HasIntrinsicOperatorValue` (Hölder, intrinsic word derivatives, pointwise identity) say that
  `f = L u` in the sense of the Sobolev, respectively Hölder, norms.
* The open `ρ`-balls `U^ρ_r = {ξ ∈ U | ν(Θ(ξ₀, ξ)) < r}` of the radial cutoff construction at the chart centre
  `ξ₀ = (x₀, 0)` as `Opens`.
* The comparison constant `C_ρ` comparing `ν ∘ Θ` with the lifted control distance, and
  the Euclidean openness of small base control balls around the base point of a chart.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped ENNReal Topology BigOperators
open RothschildStein.P1
namespace RothschildStein.P2
variable {n k : ℕ} {w : Fin k → ℕ+} {st : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}

/-! ### The operator `L` as a family of words -/

/-- The words of the drift operator `L = X_0 + ∑_{i ≥ 1} X_i²` on the alphabet `Fin (q + 1)`
(the drift is the letter `0`, of weight two): `[0]` and `[i, i]` for `i ≥ 1`. -/
def driftOpWords (q : ℕ) : Fin (q + 1) → List (Fin (q + 1)) :=
  fun i => if i = 0 then [0] else [i, i]

/-- The words of the operator `L = ∑_i X_i²` without drift on the alphabet `Fin q`. -/
def noDriftOpWords (q : ℕ) : Fin q → List (Fin q) := fun i => [i, i]

/-- `f` is a value of `L u = ∑_i X_{J i} u` on `V` in the Sobolev sense: `u` has weak word
derivatives `g_i` for the words `J i` on `V` and `f = ∑_i g_i` almost everywhere on `V`. -/
def HasWeakOperatorValue {ι : Type} [Fintype ι] (X : Fin k → (Fin n → ℝ) → (Fin n → ℝ))
    (V : Opens (Fin n → ℝ)) (J : ι → List (Fin k)) (u f : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ g : ι → (Fin n → ℝ) → ℝ, (∀ i, hasWeakWordDeriv X V (J i) u (g i)) ∧
    f =ᵐ[volume.restrict (V : Set (Fin n → ℝ))] fun x => ∑ i, g i x

/-- `f` is a value of `L u = ∑_i X_{J i} u` on `V` in the Hölder sense: `u` has intrinsic word
derivatives `g_i` for the words `J i` on `V` and `f = ∑_i g_i` pointwise on `V`. -/
def HasIntrinsicOperatorValue {ι : Type} [Fintype ι] (X : Fin k → (Fin n → ℝ) → (Fin n → ℝ))
    (V : Opens (Fin n → ℝ)) (J : ι → List (Fin k)) (u f : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ g : ι → (Fin n → ℝ) → ℝ, (∀ i, hasIntrinsicWordDeriv X V (J i) u (g i)) ∧
    ∀ x ∈ (V : Set (Fin n → ℝ)), ∑ i, g i x = f x

section Operator
variable {ι : Type} [Fintype ι] {J : ι → List (Fin k)} {u f : (Fin n → ℝ) → ℝ}

theorem HasWeakOperatorValue.mono {V V' : Opens (Fin n → ℝ)}
    (hV : (V' : Set (Fin n → ℝ)) ⊆ (V : Set (Fin n → ℝ))) (h : HasWeakOperatorValue X V J u f) :
    HasWeakOperatorValue X V' J u f := by
  obtain ⟨g, hg, hf⟩ := h
  exact ⟨g, fun i => RothschildStein.S.hasWeakWordDeriv_restrict X V V' hV (hg i),
    hf.filter_mono (ae_mono (Measure.restrict_mono hV le_rfl))⟩

theorem HasWeakOperatorValue.aestronglyMeasurable {V : Opens (Fin n → ℝ)}
    (h : HasWeakOperatorValue X V J u f) :
    AEStronglyMeasurable f (volume.restrict (V : Set (Fin n → ℝ))) := by
  obtain ⟨g, hg, hf⟩ := h
  have hs : AEStronglyMeasurable (fun x => ∑ i, g i x) (volume.restrict (V : Set (Fin n → ℝ))) :=
    Finset.aestronglyMeasurable_fun_sum Finset.univ fun i _ => (hg i).2.1.aestronglyMeasurable
  exact hs.congr hf.symm

theorem HasIntrinsicOperatorValue.mono {V V' : Opens (Fin n → ℝ)}
    (hV : (V' : Set (Fin n → ℝ)) ⊆ (V : Set (Fin n → ℝ))) (h : HasIntrinsicOperatorValue X V J u f) :
    HasIntrinsicOperatorValue X V' J u f := by
  obtain ⟨g, hg, hf⟩ := h
  exact ⟨g, fun i => hasIntrinsicWordDeriv_mono hV (J i) (hg i), fun x hx => hf x (hV hx)⟩

end Operator

/-! ### Lifting the operator value -/

theorem HasWeakOperatorValue.lift {ι : Type} [Fintype ι] {J : ι → List (Fin k)}
    {u f : (Fin n → ℝ) → ℝ} {Uo : Opens (Fin (n + m) → ℝ)} {Vo : Opens (Fin n → ℝ)}
    (S : FiberSetting Uo Vo) (P : Fin k → Fin m → MvPolynomial (Fin (n + m)) ℝ)
    (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (triangularLift X P i) (Uo : Set (Fin (n + m) → ℝ)))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Vo : Set (Fin n → ℝ)))
    (h : HasWeakOperatorValue X Vo J u f) :
    HasWeakOperatorValue (triangularLift X P) Uo J (fun ξ => u (basePoint ξ))
      (fun ξ => f (basePoint ξ)) := by
  obtain ⟨g, hg, hf⟩ := h
  refine ⟨fun i ξ => g i (basePoint ξ), fun i => S.hasWeakWordDeriv_lift X P hXt hX (J i) (hg i), ?_⟩
  have h1 : ∀ᵐ x ∂(volume : Measure (Fin n → ℝ)), x ∈ (Vo : Set (Fin n → ℝ)) →
      f x = ∑ i, g i x := (ae_restrict_iff' Vo.isOpen.measurableSet).1 hf
  have h2 := ae_comp_basePoint (m := m) h1
  rw [Filter.EventuallyEq, ae_restrict_iff' Uo.isOpen.measurableSet]
  filter_upwards [h2] with ξ hξ hmem using hξ (S.proj ξ hmem)

/-- A Sobolev function on `V_r` lifts to a Sobolev function on `U_r`. -/
theorem memSobolevX_lift {Uo : Opens (Fin (n + m) → ℝ)} {Vo : Opens (Fin n → ℝ)}
    {W : Set (Fin n → ℝ)} {cup clow : ℝ}
    (S : FiberSetting Uo Vo)
    (hFB : FiberBounds (Uo : Set (Fin (n + m) → ℝ)) (Vo : Set (Fin n → ℝ)) W cup clow)
    (P : Fin k → Fin m → MvPolynomial (Fin (n + m)) ℝ)
    (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (triangularLift X P i) (Uo : Set (Fin (n + m) → ℝ)))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Vo : Set (Fin n → ℝ))) {j : ℕ} {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hpt : p ≠ ⊤) {u : (Fin n → ℝ) → ℝ} (hu : memSobolevX w X Vo j p u) :
    memSobolevX w (triangularLift X P) Uo j p (fun ξ => u (basePoint ξ)) := by
  have key : ∀ g : (Fin n → ℝ) → ℝ, MemLp g p (volume.restrict (Vo : Set (Fin n → ℝ))) →
      MemLp (fun ξ => g (basePoint ξ)) p (volume.restrict (Uo : Set (Fin (n + m) → ℝ))) :=
    fun g hg => memLp_iff.2 (lt_of_le_of_lt
      (hFB.eLpNorm_comp_le hp hpt hg.aestronglyMeasurable)
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (memLp_iff.1 hg)))
  refine ⟨key _ hu.1, fun I hI => ?_⟩
  obtain ⟨g, hg, hgp⟩ := hu.2 I hI
  exact ⟨fun ξ => g (basePoint ξ), S.hasWeakWordDeriv_lift X P hXt hX I hg, key _ hgp⟩

/-- The `L^∞` norm of a lift is at most the `L^∞` norm of the function (only measurability of the
sets and the projection `π (A) ⊆ V` are used). -/
theorem eLpNorm_top_comp_basePoint_le {A : Set (Fin (n + m) → ℝ)} {V : Set (Fin n → ℝ)}
    (hA : MeasurableSet A) (hV : MeasurableSet V) (hproj : ∀ ξ ∈ A, basePoint ξ ∈ V)
    (f : (Fin n → ℝ) → ℝ) :
    eLpNorm (fun ξ => f (basePoint ξ)) ⊤ (volume.restrict A) ≤
      eLpNorm f ⊤ (volume.restrict V) := by
  by_cases hf : AEStronglyMeasurable f (volume.restrict V)
  · have hfA := aestronglyMeasurable_comp_basePoint hA hV hproj hf
    rw [eLpNorm_exponent_top hfA, eLpNorm_exponent_top hf]
    apply eLpNormEssSup_le_of_ae_enorm_bound
    have h1 : ∀ᵐ x ∂(volume : Measure (Fin n → ℝ)), x ∈ V → ‖f x‖ₑ ≤ eLpNormEssSup f
        (volume.restrict V) :=
      (ae_restrict_iff' hV).1 ae_le_eLpNormEssSup
    have h2 := ae_comp_basePoint (m := m) h1
    filter_upwards [ae_restrict_of_ae h2, ae_restrict_mem hA] with ξ hξ hmem
      using hξ (hproj ξ hmem)
  · rw [eLpNorm_of_not_aestronglyMeasurable hf]
    exact le_top

/-! ### The `ρ`-balls of the chart centre as open sets -/

/-- The `ρ`-ball `U^ρ_r(η) = {ξ ∈ U | ν(Θ(η, ξ)) < r}` of a centre `η ∈ U` is open. -/
theorem isOpen_rhoBall (C : LiftedChart w st Ω hΩ X x₀ m) (ν : G2.HomogeneousNorm C.G)
    {η : Fin (n + m) → ℝ} (hη : η ∈ C.U) (r : ℝ) : IsOpen (rhoBall C ν η r) := by
  have hΘc : ContinuousOn (fun ζ => C.Θ η ζ) C.U :=
    C.theta_smooth.continuousOn.comp (Continuous.continuousOn (continuous_const.prodMk continuous_id))
      (fun ζ hζ => ⟨hη, hζ⟩)
  have hc : ContinuousOn (fun ζ => ν (C.Θ η ζ)) C.U := ν.gauge.1.comp_continuousOn hΘc
  have himg : rhoBall C ν η r = C.U ∩ (fun ζ => ν (C.Θ η ζ)) ⁻¹' Set.Iio r := by
    ext ζ
    simp [rhoBall]
  rw [himg]
  exact hc.isOpen_inter_preimage C.isOpen_U isOpen_Iio

/-- The open `ρ`-ball `U^ρ_r = U^ρ_r(ξ₀)` at the chart centre `ξ₀ = (x₀, 0)`. -/
def rhoBallOpen (C : LiftedChart w st Ω hΩ X x₀ m) (ν : G2.HomogeneousNorm C.G) (r : ℝ) :
    Opens (Fin (n + m) → ℝ) :=
  ⟨rhoBall C ν (joinPoint x₀ (0 : Fin m → ℝ)) r, isOpen_rhoBall C ν C.center_mem r⟩

theorem rhoBall_mono (C : LiftedChart w st Ω hΩ X x₀ m) (ν : G2.HomogeneousNorm C.G)
    (η : Fin (n + m) → ℝ) {r r' : ℝ} (h : r ≤ r') : rhoBall C ν η r ⊆ rhoBall C ν η r' :=
  fun _ hξ => ⟨hξ.1, lt_of_lt_of_le hξ.2 h⟩

/-! ### Comparing `ν ∘ Θ` with `d̃` -/

/-- For every smooth homogeneous norm `ν` (indeed every `G2.HomogeneousNorm`) there is
`C_ν ≥ 1` with `ν(Θ(η, ξ)) / C_ν ≤ d̃(η, ξ) ≤ C_ν ν(Θ(η, ξ))` on the chart neighborhood: the
`gauge_comparison` field and the equivalence of homogeneous gauges (`G2.gauge_equivalent_max`). -/
theorem exists_gauge_comparison (C : LiftedChart w st Ω hΩ X x₀ m) (ν : G2.HomogeneousNorm C.G) :
    ∃ Cν : ℝ, 1 ≤ Cν ∧ ∀ η ∈ C.U, ∀ ξ ∈ C.U,
      ENNReal.ofReal (ν (C.Θ η ξ) / Cν) ≤ C.dl η ξ ∧
        C.dl η ξ ≤ ENNReal.ofReal (Cν * ν (C.Θ η ξ)) := by
  obtain ⟨Cρ, hCρ1, hg⟩ := C.gauge_comparison
  obtain ⟨a, b, ha, hb, hab⟩ := G2.gauge_equivalent_max ν.gauge
  have hCρ : 0 < Cρ := lt_of_lt_of_le zero_lt_one hCρ1
  refine ⟨max 1 (max (Cρ / a) (b * Cρ)), le_max_left _ _, fun η hη ξ hξ => ?_⟩
  obtain ⟨hlow, hup⟩ := hg η hη ξ hξ
  set g := rsGauge C.G.weight C.G.weight_pos (C.Θ η ξ) with hgdef
  set v := ν (C.Θ η ξ) with hv
  have hg0 : 0 ≤ g := G2.gauge_nonneg C.G _
  have hv0 : 0 ≤ v := ν.gauge.2.1 _
  obtain ⟨hv1, hv2⟩ := hab (C.Θ η ξ)
  set Cν := max 1 (max (Cρ / a) (b * Cρ)) with hCν
  have hCν0 : 0 < Cν := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have h1 : b * Cρ ≤ Cν := le_trans (le_max_right _ _) (le_max_right _ _)
  have h2 : Cρ / a ≤ Cν := le_trans (le_max_left _ _) (le_max_right _ _)
  constructor
  · refine le_trans (ENNReal.ofReal_le_ofReal ?_) hlow
    calc v / Cν ≤ (b * g) / (b * Cρ) :=
          div_le_div₀ (by positivity) hv2 (by positivity) h1
      _ = g / Cρ := mul_div_mul_left _ _ hb.ne'
  · refine le_trans hup (ENNReal.ofReal_le_ofReal ?_)
    calc Cρ * g = (Cρ / a) * (a * g) := by field_simp
      _ ≤ (Cρ / a) * v := mul_le_mul_of_nonneg_left hv1 (by positivity)
      _ ≤ Cν * v := mul_le_mul_of_nonneg_right h2 hv0

/-! ### Euclidean openness of the small base balls around the chart base point -/

theorem liftedChart_base_mem (C : LiftedChart w st Ω hΩ X x₀ m) : x₀ ∈ Ω := by
  have := holderTransfer_U_subset_O C C.center_mem
  simpa [LiftedChart.O, basePoint_joinPoint] using this

/-- The control balls `B(x₀, ρ)` for small `ρ` are Euclidean open: for `ρ = δ r` with `r < r_*`
every point has a lift in the chart (the lower fiber bound), so the ball lies in `π(U)`, where
Euclidean convergence implies convergence of the control distance. -/
theorem exists_isOpen_base_ball (C : LiftedChart w st Ω hΩ X x₀ m) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → IsOpen (rsBall Ω w X x₀ ρ) := by
  obtain ⟨rstar, δ, cf, hr, hδ0, hδ1, hcf, hosc⟩ := lifted_oscillation C
    (K₁ := {joinPoint x₀ (0 : Fin m → ℝ)}) isCompact_singleton
    (singleton_subset_iff.mpr C.center_mem)
  refine ⟨δ * rstar / 2, by positivity, fun ρ hρ hρ0 => ?_⟩
  have hr0 : 0 < ρ / δ := div_pos hρ hδ0
  have hrr : ρ / δ < rstar := by
    rw [div_lt_iff₀ hδ0]
    nlinarith
  obtain ⟨hUsU, -, -, -, -, hlift, -⟩ := hosc _ (mem_singleton _) (ρ / δ) hr0 hrr
  have hδr : δ * (ρ / δ) = ρ := by field_simp
  have hsub : rsBall Ω w X x₀ ρ ⊆ basePoint '' C.U := by
    intro x hx
    have hx' : x ∈ rsBall Ω w X (basePoint (joinPoint x₀ (0 : Fin m → ℝ))) (δ * (ρ / δ)) := by
      rw [hδr, basePoint_joinPoint]
      exact hx
    obtain ⟨ζ, hζ, hζx⟩ := hlift x hx'
    exact ⟨ζ, hUsU hζ, hζx⟩
  exact isOpen_rsBall_of_close (N := basePoint '' C.U)
    (fun x hx => by
      obtain ⟨ξ, hξ, rfl⟩ := hx
      exact holderTransfer_U_subset_O C hξ)
    (fun x hx ε hε => exists_controlDistance_lt_of_euclid_close C hx hε) hsub

/-- Every point of an open set `V ⊆ Ω` has a control ball inside `V`: for a chart base point `x` the
control balls `B(x, ε)` for small `ε` lie in any Euclidean neighbourhood of `x` (first exit,
`exists_norm_lt_of_controlDistance_lt`). -/
theorem exists_rsBall_subset (hΩ' : IsOpen Ω) (hX : ∀ i, ContinuousOn (X i) Ω)
    {V : Set (Fin n → ℝ)} (hV : IsOpen V) {x : Fin n → ℝ} (hxV : x ∈ V) (hxΩ : x ∈ Ω) :
    ∃ ε : ℝ, 0 < ε ∧ rsBall Ω w X x ε ⊆ V := by
  obtain ⟨e, he, hball⟩ := Metric.isOpen_iff.1 hV x hxV
  obtain ⟨r, hr, hclose⟩ := exists_norm_lt_of_controlDistance_lt (w := w) hΩ' hX
    (isCompact_singleton (x := x)) (singleton_subset_iff.2 hxΩ) he
  refine ⟨r, hr, fun y hy => hball ?_⟩
  rw [Metric.mem_ball, dist_eq_norm]
  exact hclose x rfl y hy.2

/-! ### The operator words lie in the order-two word family -/

theorem driftOpWords_mem_wordFamily (q : ℕ) (i : Fin (q + 1)) :
    driftOpWords q i ∈ wordFamily driftWeight 2 := by
  rw [RothschildStein.S.mem_wordFamily_iff]
  by_cases hi : i = 0
  · subst hi
    simp [driftOpWords, wordWeight, driftWeight]
  · simp [driftOpWords, hi, wordWeight, driftWeight]

theorem noDriftOpWords_mem_wordFamily (q : ℕ) (i : Fin q) :
    noDriftOpWords q i ∈ wordFamily noDriftWeight 2 := by
  rw [RothschildStein.S.mem_wordFamily_iff]
  simp [noDriftOpWords, wordWeight, noDriftWeight]

/-- The order-zero Sobolev norm is the `L^p` norm (`1 ≤ p`): the only word of weight zero
is the empty word, whose weak derivative is `f` itself. This identifies the right-hand sides
`sobolevXENorm w X V 0 p f` of the regularity statements with `‖f‖_{L^p(V)}`. -/
theorem sobolevXENorm_zero_eq_eLpNorm (w' : Fin k → ℕ+) (X' : Fin k → (Fin n → ℝ) → (Fin n → ℝ))
    (V : Opens (Fin n → ℝ)) {p : ℝ≥0∞} (hp : 1 ≤ p) (f : (Fin n → ℝ) → ℝ) :
    sobolevXENorm w' X' V 0 p f = eLpNorm f p (volume.restrict (V : Set (Fin n → ℝ))) := by
  classical
  unfold sobolevXENorm
  rw [RothschildStein.S.wordFamily_zero, Finset.sum_singleton]
  by_cases hloc : LocallyIntegrableOn f (V : Set (Fin n → ℝ)) volume
  · exact RothschildStein.S.weakWordENorm_eq X' V [] p f f
      (RothschildStein.S.hasWeakWordDeriv_nil X' V hloc)
  · have h1 : weakWordENorm X' V [] p f = ⊤ := by
      unfold weakWordENorm
      have : {r | ∃ g : (Fin n → ℝ) → ℝ, hasWeakWordDeriv X' V [] f g ∧
          AEStronglyMeasurable g (volume.restrict (V : Set (Fin n → ℝ))) ∧
          r = eLpNorm g p (volume.restrict (V : Set (Fin n → ℝ)))} = ∅ := by
        ext r
        simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
        rintro ⟨g, hg, -⟩
        exact hloc hg.1
      rw [this, sInf_empty]
    have h2 : eLpNorm f p (volume.restrict (V : Set (Fin n → ℝ))) = ⊤ := by
      by_contra hne
      have hmem : MemLp f p (volume.restrict (V : Set (Fin n → ℝ))) := lt_top_iff_ne_top.2 hne
      exact hloc (locallyIntegrableOn_of_locallyIntegrable_restrict (hmem.locallyIntegrable hp))
    rw [h1, h2]

end RothschildStein.P2
