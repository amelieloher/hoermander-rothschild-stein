-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.CutoffsGeometry
public import RothschildStein.S.ClassicalWords
public import RothschildStein.H3.RadialExpansionBound
public import RothschildStein.H3.RadialBoundConstants
public import RothschildStein.H3.PlateauWords

/-!
# Transfer of word derivatives and the sup bound

`X̃_I (h ∘ Θ(ξ₀, ·)) = (Z_I h) ∘ Θ(ξ₀, ·)` on `U` for `h` smooth with support in the gauge ball
where the truncated fields agree with `Z_i = Y_i + R_{[i],ξ₀}` (BB p. 579, via
`C.bracket_approx`). Combined with the finite radial expansion of H3 and the gauge word bound of
`CutoffsFields`, this gives `‖X̃_I φ‖_∞ ≤ C(j) (r - s)^{-j}` for the radial cutoff
(BB p. 579).
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

theorem contDiff_wordDerivative_global {N l : ℕ} (Y : Fin l → (Fin N → ℝ) → (Fin N → ℝ))
    (hY : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (Y i)) (I : List (Fin l)) {f : (Fin N → ℝ) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) : ContDiff ℝ (⊤ : ℕ∞) (wordDerivative Y I f) := by
  induction I with
  | nil => exact hf
  | cons i I ih =>
    exact (ih.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply (hY i)

/-- Transfer of word derivatives through `Θ(ξ₀, ·)` on `U`. -/
theorem wordDerivative_transfer (C : LiftedChart w st Ω hΩ X x₀ m) (ν : G2.HomogeneousNorm C.G)
    (hν : ν.Smooth) {ξ₀ : Fin (n + m) → ℝ} (hξ₀ : ξ₀ ∈ C.U) {ρ : ℝ} (hρ : 0 < ρ)
    (hT : ∀ u, ν u ≤ ρ → (ξ₀, u) ∈ C.T) (I : List (Fin k))
    {h : (Fin (n + m) → ℝ) → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hs : tsupport h ⊆ {u | ν u ≤ ρ / 2}) :
    ∀ ξ ∈ C.U, wordDerivative C.Xl I (fun ξ' => h (C.Θ ξ₀ ξ')) ξ =
      wordDerivative (zCut C ν ρ ξ₀) I h (C.Θ ξ₀ ξ) := by
  induction I with
  | nil => intro ξ _; rfl
  | cons i I ih =>
    intro ξ hξ
    have hev : wordDerivative C.Xl I (fun ξ' => h (C.Θ ξ₀ ξ')) =ᶠ[𝓝 ξ]
        fun ξ' => wordDerivative (zCut C ν ρ ξ₀) I h (C.Θ ξ₀ ξ') :=
      Filter.eventuallyEq_of_mem (C.isOpen_U.mem_nhds hξ) (fun ξ' hξ' => ih ξ' hξ')
    have hh' : ContDiff ℝ (⊤ : ℕ∞) (wordDerivative (zCut C ν ρ ξ₀) I h) :=
      contDiff_wordDerivative_global _ (zCut_contDiff C ν hν hρ hT) I hh
    have hs' : tsupport (wordDerivative (zCut C ν ρ ξ₀) I h) ⊆ {u | ν u ≤ ρ / 2} :=
      (S.tsupport_wordDerivative_subset _ I h).trans hs
    have hΘ : DifferentiableAt ℝ (C.Θ ξ₀) ξ :=
      (contDiffAt_theta C hξ₀ hξ).differentiableAt (by simp)
    have hdh : DifferentiableAt ℝ (wordDerivative (zCut C ν ρ ξ₀) I h) (C.Θ ξ₀ ξ) :=
      hh'.differentiable (by simp) _
    have hb : fderiv ℝ (C.Θ ξ₀) ξ (C.Xl i ξ) = zField C i ξ₀ (C.Θ ξ₀ ξ) :=
      C.bracket_approx [i] (List.cons_ne_nil i []) ξ₀ hξ₀ ξ hξ
    show fderiv ℝ (wordDerivative C.Xl I fun ξ' => h (C.Θ ξ₀ ξ')) ξ (C.Xl i ξ) =
      fderiv ℝ (wordDerivative (zCut C ν ρ ξ₀) I h) (C.Θ ξ₀ ξ) (zCut C ν ρ ξ₀ i (C.Θ ξ₀ ξ))
    rw [hev.fderiv_eq,
      show (fun ξ' => wordDerivative (zCut C ν ρ ξ₀) I h (C.Θ ξ₀ ξ')) =
        (wordDerivative (zCut C ν ρ ξ₀) I h) ∘ (C.Θ ξ₀) from rfl,
      fderiv_comp ξ hdh hΘ, ContinuousLinearMap.comp_apply, hb]
    by_cases hmem : C.Θ ξ₀ ξ ∈ tsupport (wordDerivative (zCut C ν ρ ξ₀) I h)
    · rw [zCut_eq C ν hρ (hs' hmem)]
    · rw [fderiv_of_notMem_tsupport ℝ hmem]
      simp

/-- The gauge profile composed with the gauge, as a function of `u`. -/
def gaugeProfile (C : LiftedChart w st Ω hΩ X x₀ m) (ν : G2.HomogeneousNorm C.G) (s r : ℝ) :
    (Fin (n + m) → ℝ) → ℝ :=
  fun u => H3.quasiballProfile (s + (r - s) / 3) (s + 2 * (r - s) / 3) (ν u)

theorem gaugeProfile_contDiff (C : LiftedChart w st Ω hΩ X x₀ m) (ν : G2.HomogeneousNorm C.G)
    (hν : ν.Smooth) {s r : ℝ} (hs : 0 < s) (hsr : s < r) :
    ContDiff ℝ (⊤ : ℕ∞) (gaugeProfile C ν s r) :=
  H3.contDiff_radial_quasiballProfile ν hν (by linarith) (by linarith)

theorem gaugeProfile_eq_zero (C : LiftedChart w st Ω hΩ X x₀ m) (ν : G2.HomogeneousNorm C.G)
    {s r : ℝ} (hsr : s < r) {u : Fin (n + m) → ℝ} (hu : (s + r) / 2 ≤ ν u) :
    gaugeProfile C ν s r u = 0 :=
  H3.quasiballProfile_zero (by linarith) (by linarith)

theorem gaugeProfile_tsupport (C : LiftedChart w st Ω hΩ X x₀ m) (ν : G2.HomogeneousNorm C.G)
    {s r : ℝ} (hsr : s < r) : tsupport (gaugeProfile C ν s r) ⊆ {u | ν u ≤ (s + r) / 2} := by
  apply closure_minimal _ (isClosed_le ν.gauge.1 continuous_const)
  intro u hu
  by_contra hlt
  exact hu (gaugeProfile_eq_zero C ν hsr (not_le.1 hlt).le)

theorem radialCutoff_eq_gaugeProfile_comp (C : LiftedChart w st Ω hΩ X x₀ m)
    (ν : G2.HomogeneousNorm C.G) (ξ₀ : Fin (n + m) → ℝ) {s r : ℝ} (hsr : s < r)
    {ξ : Fin (n + m) → ℝ} (hξ : ξ ∈ C.U) :
    radialCutoff C ν ξ₀ s r ξ = gaugeProfile C ν s r (C.Θ ξ₀ ξ) := by
  rw [radialCutoff_apply_of_mem C ν ξ₀ s r hξ, cutoffProfile_eq_quasiball hsr]
  rfl

/-- The word derivatives of the radial cutoff inside `U` in terms of the truncated fields `Z`. -/
theorem wordDerivative_radialCutoff_of_mem (C : LiftedChart w st Ω hΩ X x₀ m)
    (ν : G2.HomogeneousNorm C.G) (hν : ν.Smooth) {ξ₀ : Fin (n + m) → ℝ} (hξ₀ : ξ₀ ∈ C.U)
    {s r ρ : ℝ} (hs : 0 < s) (hsr : s < r) (hρ : 0 < ρ) (hrρ : s + r ≤ ρ)
    (hT : ∀ u, ν u ≤ ρ → (ξ₀, u) ∈ C.T) (I : List (Fin k)) {ξ : Fin (n + m) → ℝ}
    (hξ : ξ ∈ C.U) :
    wordDerivative C.Xl I (radialCutoff C ν ξ₀ s r) ξ =
      wordDerivative (zCut C ν ρ ξ₀) I (gaugeProfile C ν s r) (C.Θ ξ₀ ξ) := by
  have hev : radialCutoff C ν ξ₀ s r =ᶠ[𝓝 ξ] fun ξ' => gaugeProfile C ν s r (C.Θ ξ₀ ξ') := by
    filter_upwards [C.isOpen_U.mem_nhds hξ] with ξ' hξ'
    exact radialCutoff_eq_gaugeProfile_comp C ν ξ₀ hsr hξ'
  rw [(H3.wordDerivative_germ C.Xl I hev).self_of_nhds]
  exact wordDerivative_transfer C ν hν hξ₀ hρ hT I (gaugeProfile_contDiff C ν hν hs hsr)
    ((gaugeProfile_tsupport C ν hsr).trans (fun u hu => by
      have : ν u ≤ (s + r) / 2 := hu
      show ν u ≤ ρ / 2
      linarith)) ξ hξ

/-- Outside `U` every word derivative of the radial cutoff vanishes. -/
theorem wordDerivative_radialCutoff_of_notMem (C : LiftedChart w st Ω hΩ X x₀ m)
    (ν : G2.HomogeneousNorm C.G) {ξ₀ : Fin (n + m) → ℝ} (hξ₀ : ξ₀ ∈ C.U)
    {s r ρ : ℝ} (hs : 0 < s) (hsr : s < r) (hrρ : s + r ≤ ρ)
    (hT : ∀ u, ν u ≤ ρ → (ξ₀, u) ∈ C.T) (I : List (Fin k)) {ξ : Fin (n + m) → ℝ}
    (hξ : ξ ∉ C.U) : wordDerivative C.Xl I (radialCutoff C ν ξ₀ s r) ξ = 0 := by
  have hts := radialCutoff_tsupport_subset C ν hξ₀ (ρ := ρ) hsr (by linarith) hT
  have hnot : ξ ∉ tsupport (radialCutoff C ν ξ₀ s r) := fun h => hξ (hts h).1
  have h0 : radialCutoff C ν ξ₀ s r =ᶠ[𝓝 ξ] fun _ => (0 : ℝ) := by
    filter_upwards [(isClosed_tsupport _).isOpen_compl.mem_nhds hnot] with ξ' hξ'
    exact image_eq_zero_of_notMem_tsupport hξ'
  rw [(H3.wordDerivative_germ C.Xl I h0).self_of_nhds, H3.wordDerivative_const]
  simp

theorem gap_rpow_third {a : ℝ} (ha : 0 < a) (W : ℕ) :
    (a / 3) ^ (-(W : ℝ)) = 3 ^ W * a ^ (-(W : ℝ)) := by
  rw [Real.div_rpow ha.le (by norm_num : (0 : ℝ) ≤ 3), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3),
    Real.rpow_natCast]
  field_simp

/-- For every word `I` of weighted length `j` there is a constant
`C(j)` (depending on the chart, the gauge and the compact set `Kc` of centres, not on the centre
or on `s < r < ρ / 2`) with `‖X̃_I φ‖_∞ ≤ C (r - s)^{-j}` (BB p. 579, Lem 11.36). -/
theorem radialCutoff_sup_bound (C : LiftedChart w st Ω hΩ X x₀ m) (ν : G2.HomogeneousNorm C.G)
    (hν : ν.Smooth) {Kc : Set (Fin (n + m) → ℝ)} (hKc : IsCompact Kc) (hKU : Kc ⊆ C.U)
    {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hT : ∀ η ∈ Kc, ∀ u, ν u ≤ ρ → (η, u) ∈ C.T) (I : List (Fin k)) :
    ∃ CI : ℝ, 0 ≤ CI ∧ ∀ ξ₀ ∈ Kc, ∀ s r : ℝ, 0 < s → s < r → r < ρ / 2 → ∀ ξ,
      |wordDerivative C.Xl I (radialCutoff C ν ξ₀ s r) ξ| ≤
        CI * (r - s) ^ (-(wordWeight w I : ℤ)) := by
  by_cases hI : I = []
  · subst hI
    refine ⟨1, zero_le_one, fun ξ₀ _ s r _ hsr _ ξ => ?_⟩
    have h := radialCutoff_range C ν ξ₀ s r ξ
    simp only [wordDerivative, wordWeight, List.map_nil, List.sum_nil, Nat.cast_zero, neg_zero,
      zpow_zero, mul_one]
    rw [abs_of_nonneg h.1]
    exact h.2
  · -- gauge word bounds on the punctured ball of radius `ρ / 2`
    have hρ2 : 0 < ρ / 2 := by linarith
    have hT2 : ∀ η ∈ Kc, ∀ u, ν u ≤ ρ / 2 → (η, u) ∈ C.T :=
      fun η hη u hu => hT η hη u (hu.trans (by linarith))
    choose M₀ hM₀ using fun K : List (Fin k) =>
      zIter_gauge_bound C ν hν hKc hKU hρ2 (by linarith) hT2 K
    obtain ⟨κ, hκ, hprofile⟩ := H3.exists_profile_word_constants
    let M : List (Fin k) → ℝ := fun K => |M₀ K|
    have hM : ∀ K, 0 ≤ M K := fun K => abs_nonneg _
    refine ⟨H3.radialWordBoundConstant κ M I * 3 ^ (wordWeight w I),
      mul_nonneg (H3.radialWordBoundConstant_nonneg κ M hκ hM I) (by positivity), ?_⟩
    intro ξ₀ hξ₀ s r hs hsr hrρ ξ
    have ha : 0 < r - s := sub_pos.2 hsr
    have hξ₀U : ξ₀ ∈ C.U := hKU hξ₀
    have hTξ : ∀ u, ν u ≤ ρ → (ξ₀, u) ∈ C.T := fun u hu => hT ξ₀ hξ₀ u hu
    set W := wordWeight w I with hW
    -- the bound for the truncated word derivative at every point of the gauge space
    have hmain : ∀ u : Fin (n + m) → ℝ,
        |wordDerivative (zCut C ν ρ ξ₀) I (gaugeProfile C ν s r) u| ≤
          H3.radialWordBoundConstant κ M I * 3 ^ W * (r - s) ^ (-(W : ℤ)) := by
      intro u
      have hconst : 0 ≤ H3.radialWordBoundConstant κ M I * 3 ^ W * (r - s) ^ (-(W : ℤ)) :=
        mul_nonneg (mul_nonneg (H3.radialWordBoundConstant_nonneg κ M hκ hM I) (by positivity))
          (zpow_nonneg ha.le _)
      set t' := s + (r - s) / 3 with ht'
      set s' := s + 2 * (r - s) / 3 with hs'
      have hts : t' < s' := by rw [ht', hs']; linarith
      by_cases h1 : ν u < t'
      · have := H3.radialProfile_wordDerivative_zero_below C.G ν (zCut C ν ρ ξ₀) I hI hts h1
        change |wordDerivative (zCut C ν ρ ξ₀) I (H3.quasiballProfile t' s' ∘ ν) u| ≤ _
        rw [this, abs_zero]
        exact hconst
      · by_cases h2 : ν u < ρ / 2
        · have hx : u ≠ 0 := by
            intro h0
            rw [h0, (ν.gauge.2.2.1 0).mpr rfl] at h1
            exact h1 (by rw [ht']; linarith)
          have hpos : 0 < ν u := lt_of_lt_of_le (by rw [ht']; linarith) (not_lt.1 h1)
          have hgap : s' - t' = (r - s) / 3 := by rw [ht', hs']; ring
          have hg : ∀ K, |wordDerivative (zCut C ν ρ ξ₀) K (⇑ν) u| ≤
              M K * (ν u) ^ (1 - (wordWeight w K : ℝ)) := by
            intro K
            have e := zCut_wordDerivative C ν hρ0 ξ₀ K u hpos h2
            have hb := hM₀ K ξ₀ hξ₀ u hpos h2
            change |wordDerivative (zCut C ν ρ ξ₀) K (fun v => ν v) u| ≤ _
            rw [e]
            have hz : (ν u) ^ (1 - (wordWeight w K : ℝ)) = (ν u) ^ (1 - (wordWeight w K : ℤ)) := by
              rw [← Real.rpow_intCast]
              push_cast
              rfl
            rw [hz]
            exact hb.trans (mul_le_mul_of_nonneg_right (le_abs_self _)
              (zpow_nonneg hpos.le _))
          have hp : ∀ t ∈ H3.radialWordTerms I,
              |iteratedDeriv t.1 (H3.quasiballProfile t' s') (ν u)| ≤
                κ t.1 * (2 / ((r - s) / 3)) ^ t.1 := by
            intro t ht
            have := hprofile t.1 (H3.radialWordTerms_profile_pos w I hI ht) t' s' hts (ν u)
            rwa [hgap] at this
          have hav : (r - s) / 3 ≤ ν u := by
            have : (r - s) / 3 ≤ t' := by rw [ht']; linarith
            exact this.trans (not_lt.1 h1)
          have hb := H3.wordDerivative_radial_gap_bound (zCut C ν ρ ξ₀)
            (zCut_contDiff C ν hν hρ0 hTξ) hν (H3.quasiballProfile_contDiff t' s') w κ M hκ hM I
            hx (by positivity) hav hg hp
          change |wordDerivative (zCut C ν ρ ξ₀) I (H3.quasiballProfile t' s' ∘ ν) u| ≤ _
          refine hb.trans ?_
          rw [gap_rpow_third ha W]
          have hz : (r - s) ^ (-(W : ℝ)) = (r - s) ^ (-(W : ℤ)) := by
            rw [← Real.rpow_intCast]
            push_cast
            rfl
          rw [hz]
          apply le_of_eq
          ring
        · have h3 : ρ / 2 ≤ ν u := not_lt.1 h2
          have hev : gaugeProfile C ν s r =ᶠ[𝓝 u] fun _ => (0 : ℝ) := by
            filter_upwards [(isOpen_lt continuous_const ν.gauge.1).mem_nhds
              (show (s + r) / 2 < ν u by linarith)] with v hv
            exact gaugeProfile_eq_zero C ν hsr hv.le
          rw [(H3.wordDerivative_germ (zCut C ν ρ ξ₀) I hev).self_of_nhds,
            H3.wordDerivative_const]
          simp only [hI, ite_false, abs_zero]
          exact hconst
    by_cases hξ : ξ ∈ C.U
    · rw [wordDerivative_radialCutoff_of_mem C ν hν hξ₀U hs hsr hρ0 (by linarith) hTξ I hξ]
      exact hmain _
    · rw [wordDerivative_radialCutoff_of_notMem C ν hξ₀U hs hsr (by linarith) hTξ I hξ, abs_zero]
      exact mul_nonneg (mul_nonneg (H3.radialWordBoundConstant_nonneg κ M hκ hM I)
        (by positivity)) (zpow_nonneg ha.le _)

end RothschildStein.P2
