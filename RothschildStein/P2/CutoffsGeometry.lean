-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.CutoffsFields
public import RothschildStein.H3.QuasiballProfile

/-!
# Geometry of the ρ-balls and the radial cutoff

`U^ρ_r(ξ₀) = {ξ ∈ U | ν(Θ(ξ₀, ξ)) < r}` (BB p. 578; the comparison `ρ ≍ d̃` of the lifted chart). Closed ρ-balls of small radius are
compact subsets of `U` (images of closed gauge balls under `(e ξ₀).symm`), uniformly over a
compact set of centres. The cutoff is `χ((ν(Θ(ξ₀, ξ)) - s)/(r - s))` with the fixed smooth profile
`χ(x) = smoothTransition(3 - 6x)`, equal to `1` for `x ≤ 1/3` and to `0` for `x ≥ 1/2`; it is
extended by zero outside `U`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology
namespace RothschildStein.P2

open RothschildStein.P1

variable {n k : ℕ} {w : Fin k → ℕ+} {st : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}

/-- The `ρ`-ball `U^ρ_r(ξ₀) = {ξ ∈ U | ν(Θ(ξ₀, ξ)) < r}` (BB p. 578). -/
def rhoBall (C : LiftedChart w st Ω hΩ X x₀ m) (ν : G2.HomogeneousNorm C.G)
    (ξ₀ : Fin (n + m) → ℝ) (r : ℝ) : Set (Fin (n + m) → ℝ) :=
  {ξ | ξ ∈ C.U ∧ ν (C.Θ ξ₀ ξ) < r}

/-- The closed `ρ`-ball `{ξ ∈ U | ν(Θ(ξ₀, ξ)) ≤ r}`. -/
def closedRhoBall (C : LiftedChart w st Ω hΩ X x₀ m) (ν : G2.HomogeneousNorm C.G)
    (ξ₀ : Fin (n + m) → ℝ) (r : ℝ) : Set (Fin (n + m) → ℝ) :=
  {ξ | ξ ∈ C.U ∧ ν (C.Θ ξ₀ ξ) ≤ r}

theorem rhoBall_subset_closed (C : LiftedChart w st Ω hΩ X x₀ m) (ν : G2.HomogeneousNorm C.G)
    (ξ₀ : Fin (n + m) → ℝ) {r : ℝ} : rhoBall C ν ξ₀ r ⊆ closedRhoBall C ν ξ₀ r :=
  fun _ h => ⟨h.1, h.2.le⟩

theorem closedRhoBall_subset_rhoBall (C : LiftedChart w st Ω hΩ X x₀ m)
    (ν : G2.HomogeneousNorm C.G) (ξ₀ : Fin (n + m) → ℝ) {r r' : ℝ} (h : r < r') :
    closedRhoBall C ν ξ₀ r ⊆ rhoBall C ν ξ₀ r' :=
  fun _ hξ => ⟨hξ.1, hξ.2.trans_lt h⟩

/-- Closed `ρ`-balls inside the domain of the chart are compact. -/
theorem isCompact_closedRhoBall (C : LiftedChart w st Ω hΩ X x₀ m) (ν : G2.HomogeneousNorm C.G)
    {ξ₀ : Fin (n + m) → ℝ} (hξ₀ : ξ₀ ∈ C.U) {ρ : ℝ}
    (hT : ∀ u, ν u ≤ ρ → (ξ₀, u) ∈ C.T) : IsCompact (closedRhoBall C ν ξ₀ ρ) := by
  obtain ⟨hsrc, hΘ, -, -, -⟩ := C.chart ξ₀ hξ₀
  have himg : closedRhoBall C ν ξ₀ ρ = (C.e ξ₀).symm '' {u | ν u ≤ ρ} := by
    ext ξ
    constructor
    · rintro ⟨hξ, hν⟩
      refine ⟨C.Θ ξ₀ ξ, hν, ?_⟩
      have hs : ξ ∈ (C.e ξ₀).source := by rw [hsrc]; exact hξ
      rw [← hΘ ξ hξ]
      exact (C.e ξ₀).left_inv hs
    · rintro ⟨u, hu, rfl⟩
      have ht : u ∈ (C.e ξ₀).target := (hT u hu).2
      have hs : (C.e ξ₀).symm u ∈ C.U := by
        rw [← hsrc]; exact (C.e ξ₀).map_target ht
      refine ⟨hs, ?_⟩
      rw [← hΘ _ hs, (C.e ξ₀).right_inv ht]
      exact hu
  rw [himg]
  exact (G2.isCompact_gauge_le ν.gauge ρ).image_of_continuousOn
    ((C.e ξ₀).continuousOn_symm.mono (fun u hu => (hT u hu).2))

/-- Small gauge sublevels lie in any neighbourhood of the origin. -/
theorem exists_gauge_sublevel_subset {N : ℕ} (G : HomogeneousGroup N)
    {ν : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν) {v : Set (Fin N → ℝ)}
    (hv : v ∈ 𝓝 (0 : Fin N → ℝ)) :
    ∃ r : ℝ, 0 < r ∧ r ≤ 1 ∧ ∀ u, ν u ≤ r → u ∈ v := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 hv
  obtain ⟨c, hc, hcoord⟩ := exists_abs_coord_le G hν
  refine ⟨min 1 (ε / (2 * c)), lt_min one_pos (by positivity), min_le_left _ _, fun u hu => ?_⟩
  apply hball
  rw [Metric.mem_ball, dist_zero_right, pi_norm_lt_iff hε]
  intro i
  have hν0 := hν.2.1 u
  have hν1 : ν u ≤ 1 := hu.trans (min_le_left _ _)
  have hνr : ν u ≤ ε / (2 * c) := hu.trans (min_le_right _ _)
  have h1 : ν u ^ G.weight i ≤ ν u := pow_le_of_le_one hν0 hν1 (G.weight_pos i).ne'
  have h2 : |u i| ≤ c * ν u := (hcoord u i).trans (mul_le_mul_of_nonneg_left h1 hc.le)
  rw [Real.norm_eq_abs]
  calc |u i| ≤ c * ν u := h2
    _ ≤ c * (ε / (2 * c)) := mul_le_mul_of_nonneg_left hνr hc.le
    _ = ε / 2 := by field_simp
    _ < ε := by linarith

/-- Uniform chart radius: for centres in a compact subset of `U` the closed gauge ball of radius
`ρ₀` lies in the domain of the remainders. -/
theorem exists_chart_radius (C : LiftedChart w st Ω hΩ X x₀ m) (ν : G2.HomogeneousNorm C.G)
    {Kc : Set (Fin (n + m) → ℝ)} (hKc : IsCompact Kc) (hKU : Kc ⊆ C.U) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ρ₀ ≤ 1 ∧ ∀ η ∈ Kc, ∀ u, ν u ≤ ρ₀ → (η, u) ∈ C.T := by
  have h0 : Kc ×ˢ ({0} : Set (Fin (n + m) → ℝ)) ⊆ C.T := by
    rintro ⟨η, u⟩ ⟨hη, hu⟩
    rw [mem_singleton_iff] at hu
    subst hu
    obtain ⟨hsrc, -, -, -, hη0⟩ := C.chart η (hKU hη)
    refine ⟨hKU hη, ?_⟩
    have hs : η ∈ (C.e η).source := by rw [hsrc]; exact hKU hη
    have hmap := (C.e η).map_source hs
    have hval : C.e η η = C.Θ η η := (C.chart η (hKU hη)).2.1 η (hKU hη)
    rw [hval, hη0] at hmap
    exact hmap
  obtain ⟨u, v, -, hvo, hKu, h0v, huv⟩ :=
    generalized_tube_lemma hKc isCompact_singleton C.isOpen_T h0
  obtain ⟨r, hr0, hr1, hr⟩ := exists_gauge_sublevel_subset C.G ν.gauge (hvo.mem_nhds (h0v (mem_singleton _)))
  exact ⟨r, hr0, hr1, fun η hη t ht => huv ⟨hKu hη, hr t ht⟩⟩

/-- The fixed smooth one-variable profile: `1` for `x ≤ 1/3`, `0` for `x ≥ 1/2`. -/
def cutoffProfile (x : ℝ) : ℝ := Real.smoothTransition (3 - 6 * x)

theorem cutoffProfile_range (x : ℝ) : 0 ≤ cutoffProfile x ∧ cutoffProfile x ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem cutoffProfile_one {x : ℝ} (hx : x ≤ 1 / 3) : cutoffProfile x = 1 :=
  Real.smoothTransition.one_of_one_le (by linarith)

theorem cutoffProfile_zero {x : ℝ} (hx : 1 / 2 ≤ x) : cutoffProfile x = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

/-- The radial cutoff `χ((ν(Θ(ξ₀, ξ)) - s)/(r - s))`, extended by zero outside `U`. -/
def radialCutoff (C : LiftedChart w st Ω hΩ X x₀ m) (ν : G2.HomogeneousNorm C.G)
    (ξ₀ : Fin (n + m) → ℝ) (s r : ℝ) : (Fin (n + m) → ℝ) → ℝ :=
  C.U.indicator (fun ξ => cutoffProfile ((ν (C.Θ ξ₀ ξ) - s) / (r - s)))

theorem cutoffProfile_eq_quasiball {s r : ℝ} (hsr : s < r) (τ : ℝ) :
    cutoffProfile ((τ - s) / (r - s)) =
      H3.quasiballProfile (s + (r - s) / 3) (s + 2 * (r - s) / 3) τ := by
  have ha : r - s ≠ 0 := (sub_pos.2 hsr).ne'
  have h6 : ((s + 2 * (r - s) / 3) - (s + (r - s) / 3)) / 2 = (r - s) / 6 := by ring
  have h7 : ((s + (r - s) / 3) + (s + 2 * (r - s) / 3)) / 2 - τ = s + (r - s) / 2 - τ := by ring
  have key : 3 - 6 * ((τ - s) / (r - s)) =
      (((s + (r - s) / 3) + (s + 2 * (r - s) / 3)) / 2 - τ) /
        (((s + 2 * (r - s) / 3) - (s + (r - s) / 3)) / 2) := by
    rw [h6, h7]
    field_simp
    ring
  unfold cutoffProfile H3.quasiballProfile
  rw [key]

theorem radialCutoff_apply_of_mem (C : LiftedChart w st Ω hΩ X x₀ m)
    (ν : G2.HomogeneousNorm C.G) (ξ₀ : Fin (n + m) → ℝ) (s r : ℝ) {ξ : Fin (n + m) → ℝ}
    (hξ : ξ ∈ C.U) :
    radialCutoff C ν ξ₀ s r ξ = cutoffProfile ((ν (C.Θ ξ₀ ξ) - s) / (r - s)) :=
  Set.indicator_of_mem hξ _

theorem radialCutoff_apply_of_notMem (C : LiftedChart w st Ω hΩ X x₀ m)
    (ν : G2.HomogeneousNorm C.G) (ξ₀ : Fin (n + m) → ℝ) (s r : ℝ) {ξ : Fin (n + m) → ℝ}
    (hξ : ξ ∉ C.U) : radialCutoff C ν ξ₀ s r ξ = 0 :=
  Set.indicator_of_notMem hξ _

theorem radialCutoff_range (C : LiftedChart w st Ω hΩ X x₀ m) (ν : G2.HomogeneousNorm C.G)
    (ξ₀ : Fin (n + m) → ℝ) (s r : ℝ) (ξ : Fin (n + m) → ℝ) :
    0 ≤ radialCutoff C ν ξ₀ s r ξ ∧ radialCutoff C ν ξ₀ s r ξ ≤ 1 := by
  by_cases hξ : ξ ∈ C.U
  · rw [radialCutoff_apply_of_mem C ν ξ₀ s r hξ]
    exact cutoffProfile_range _
  · rw [radialCutoff_apply_of_notMem C ν ξ₀ s r hξ]
    exact ⟨le_rfl, zero_le_one⟩

theorem radialCutoff_eq_one (C : LiftedChart w st Ω hΩ X x₀ m) (ν : G2.HomogeneousNorm C.G)
    (ξ₀ : Fin (n + m) → ℝ) {s r : ℝ} (hsr : s < r) {ξ : Fin (n + m) → ℝ}
    (hξ : ξ ∈ rhoBall C ν ξ₀ s) : radialCutoff C ν ξ₀ s r ξ = 1 := by
  rw [radialCutoff_apply_of_mem C ν ξ₀ s r hξ.1]
  apply cutoffProfile_one
  have ha : 0 < r - s := sub_pos.2 hsr
  rw [div_le_iff₀ ha]
  linarith [hξ.2]

theorem radialCutoff_eq_zero (C : LiftedChart w st Ω hΩ X x₀ m) (ν : G2.HomogeneousNorm C.G)
    (ξ₀ : Fin (n + m) → ℝ) {s r : ℝ} (hsr : s < r) {ξ : Fin (n + m) → ℝ}
    (hξ : (s + r) / 2 ≤ ν (C.Θ ξ₀ ξ)) : radialCutoff C ν ξ₀ s r ξ = 0 := by
  by_cases hU : ξ ∈ C.U
  · rw [radialCutoff_apply_of_mem C ν ξ₀ s r hU]
    apply cutoffProfile_zero
    have ha : 0 < r - s := sub_pos.2 hsr
    rw [le_div_iff₀ ha]
    linarith
  · exact radialCutoff_apply_of_notMem C ν ξ₀ s r hU

/-- Smoothness of `Θ(ξ₀, ·)` on the chart domain. -/
theorem contDiffAt_theta (C : LiftedChart w st Ω hΩ X x₀ m) {ξ₀ : Fin (n + m) → ℝ}
    (hξ₀ : ξ₀ ∈ C.U) {ξ : Fin (n + m) → ℝ} (hξ : ξ ∈ C.U) :
    ContDiffAt ℝ (⊤ : ℕ∞) (C.Θ ξ₀) ξ :=
  (C.theta_smooth.comp (contDiff_const.prodMk contDiff_id).contDiffOn
    (fun _ hξ' => ⟨hξ₀, hξ'⟩)).contDiffAt (C.isOpen_U.mem_nhds hξ)

/-- The radial cutoff is smooth, supported in the closed `ρ`-ball of radius `(s + r)/2`,
and takes values in `[0, 1]`, equal to `1` on `U^ρ_s`. -/
theorem radialCutoff_contDiff (C : LiftedChart w st Ω hΩ X x₀ m) (ν : G2.HomogeneousNorm C.G)
    (hν : ν.Smooth) {ξ₀ : Fin (n + m) → ℝ} (hξ₀ : ξ₀ ∈ C.U) {s r ρ : ℝ} (hs : 0 < s)
    (hsr : s < r) (hρ : (s + r) / 2 ≤ ρ) (hT : ∀ u, ν u ≤ ρ → (ξ₀, u) ∈ C.T) :
    ContDiff ℝ (⊤ : ℕ∞) (radialCutoff C ν ξ₀ s r) := by
  have ha : 0 < r - s := sub_pos.2 hsr
  have hg : ContDiff ℝ (⊤ : ℕ∞) (fun u => H3.quasiballProfile (s + (r - s) / 3)
      (s + 2 * (r - s) / 3) (ν u)) :=
    H3.contDiff_radial_quasiballProfile ν hν (by linarith) (by linarith)
  have hK : IsCompact (closedRhoBall C ν ξ₀ ((s + r) / 2)) :=
    (isCompact_closedRhoBall C ν hξ₀ (ρ := (s + r) / 2) (fun u hu => hT u (hu.trans hρ)))
  refine contDiff_iff_contDiffAt.2 (fun ξ => ?_)
  by_cases hU : ξ ∈ C.U
  · have hev : radialCutoff C ν ξ₀ s r =ᶠ[𝓝 ξ]
        fun ξ => H3.quasiballProfile (s + (r - s) / 3) (s + 2 * (r - s) / 3) (ν (C.Θ ξ₀ ξ)) := by
      filter_upwards [C.isOpen_U.mem_nhds hU] with ξ' hξ'
      rw [radialCutoff_apply_of_mem C ν ξ₀ s r hξ', cutoffProfile_eq_quasiball hsr]
    exact (hg.contDiffAt.comp ξ (contDiffAt_theta C hξ₀ hU)).congr_of_eventuallyEq hev
  · have hξK : ξ ∉ closedRhoBall C ν ξ₀ ((s + r) / 2) := fun h => hU h.1
    have h0 : ∀ᶠ ξ' in 𝓝 ξ, radialCutoff C ν ξ₀ s r ξ' = 0 := by
      filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hξK] with ξ' hξ'
      by_cases hU' : ξ' ∈ C.U
      · apply radialCutoff_eq_zero C ν ξ₀ hsr
        by_contra hlt
        exact hξ' ⟨hU', (not_le.1 hlt).le⟩
      · exact radialCutoff_apply_of_notMem C ν ξ₀ s r hU'
    exact contDiffAt_const.congr_of_eventuallyEq h0

theorem radialCutoff_tsupport_subset (C : LiftedChart w st Ω hΩ X x₀ m)
    (ν : G2.HomogeneousNorm C.G) {ξ₀ : Fin (n + m) → ℝ} (hξ₀ : ξ₀ ∈ C.U) {s r ρ : ℝ}
    (hsr : s < r) (hρ : (s + r) / 2 ≤ ρ) (hT : ∀ u, ν u ≤ ρ → (ξ₀, u) ∈ C.T) :
    tsupport (radialCutoff C ν ξ₀ s r) ⊆ closedRhoBall C ν ξ₀ ((s + r) / 2) := by
  have hK : IsCompact (closedRhoBall C ν ξ₀ ((s + r) / 2)) :=
    (isCompact_closedRhoBall C ν hξ₀ (ρ := (s + r) / 2) (fun u hu => hT u (hu.trans hρ)))
  apply closure_minimal _ hK.isClosed
  intro ξ hξ
  by_cases hU : ξ ∈ C.U
  · by_contra hmem
    apply Function.mem_support.1 hξ
    apply radialCutoff_eq_zero C ν ξ₀ hsr
    by_contra hlt
    exact hmem ⟨hU, (not_le.1 hlt).le⟩
  · exact absurd (radialCutoff_apply_of_notMem C ν ξ₀ s r hU) (Function.mem_support.1 hξ)

end RothschildStein.P2
