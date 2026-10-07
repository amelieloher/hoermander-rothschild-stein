-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.LocalizedFirstRealEstimate
public import RothschildStein.H3.FrozenHolderRestriction
public import RothschildStein.H3.FrozenDriftEquationRestriction
public import RothschildStein.H3.QuasiballControlBuffer
public import RothschildStein.H3.QuasiballDriftTestCutoff

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped ENNReal NNReal
namespace RothschildStein.H3

/-- Actual smooth-gauge cutoffs and the fixed distribution
forcing yield the full first-order scale estimate on nested quasiballs.
All constants precede the center, outer radius, input and forcing. -/
theorem quasiball_first_scale_estimate_of_controlNorm {N q : ℕ} (G : HomogeneousGroup N)
    (H : H1.StandingHypotheses G q) (K : H1.FundamentalKernel G H)
    (Hc : G2.ControlNormConclusion G driftWeight H.fields)
    (hQ : 2 < (G.homogeneousDimension : ℝ)) (μ : G2.GroupMollifier G H.norm)
    (ν : G2.HomogeneousNorm G) (hν : ν.Smooth)
    {α : ℝ≥0} (hα : 0 < α) (hα1 : (α : ℝ) < 1) {Rmax : ℝ} (hRmax : 0 < Rmax) :
    ∃ a b C : ℝ, 0 < a ∧ 0 < b ∧ 0 < C ∧
      ∀ z : Fin N → ℝ, ∀ R : ℝ, 0 < R → R ≤ Rmax →
      ∀ u f : (Fin N → ℝ) → ℝ,
      memHolderX driftWeight H.fields (controlDistance univ driftWeight H.fields)
        (quasiballDomain G ν z R) 2 (α : ℝ) u →
      hasDistributionEquationWithDrift (quasiballDomain G ν z R) H.fields
        (fun i => (H.fields_smooth G i).contDiffOn)
        (Distribution.ofFun (quasiballDomain G ν z R) u volume (⊤ : ℕ∞)) f →
      ∀ t s : ℝ, R / 2 ≤ t → t < s → s ≤ R →
      ∀ ε : ℝ, 0 < ε → ε < 1 →
      (holderXENorm driftWeight H.fields (controlDistance univ driftWeight H.fields)
        (quasiballDomain G ν z t) 1 (α : ℝ) u).toReal ≤
      ε * (lpNorm f ∞ (volume.restrict (G2.gaugeBall G ν z R)) +
        b / (s - t) ^ 2 * lpNorm u ∞ (volume.restrict (G2.gaugeBall G ν z R)) +
        (2 * a / (s - t)) * (holderXENorm driftWeight H.fields
          (controlDistance univ driftWeight H.fields) (quasiballDomain G ν z s) 1 (α : ℝ) u).toReal) +
      C * ε ^ (-(2 * (3 + (G.homogeneousDimension : ℝ)) / (1 - (α : ℝ)))) *
        lpNorm u ∞ (volume.restrict (G2.gaugeBall G ν z R)) := by
  obtain ⟨ρ, hρ, hbuffer⟩ := exists_uniform_gauge_ball_buffer G ν Hc.norm hRmax
  obtain ⟨C, hC, hcompact⟩ := localized_first_equation_real_estimate_of_controlNorm G H K Hc hQ μ ν hν hα hα1 hρ
  obtain ⟨a, c₂, ha, hc₂, hcut⟩ := exists_quasiball_drift_test_cutoff G H ν hν
  let b := ((q + 1 : ℕ) : ℝ) * c₂
  have hb : 0 < b := mul_pos (by positivity) hc₂
  let Dgeom := S.groupControlGeometry_of_controlNorm G driftWeight H.fields Hc ⊤
  refine ⟨a, b, C, ha, hb, hC, ?_⟩
  intro z R hR hRR u f hu heq t s ht hts hs ε hε hε1
  let UR := quasiballDomain G ν z R
  let Us := quasiballDomain G ν z s
  let Ut := quasiballDomain G ν z t
  have hsub : (Us : Set (Fin N → ℝ)) ⊆ UR := fun _ hx => hx.trans_le hs
  have ht0 : 0 < t := lt_of_lt_of_le (half_pos hR) ht
  have hhalf : s / 2 ≤ t := (div_le_div_of_nonneg_right hs (by norm_num)).trans ht
  obtain ⟨φ, hone, hn, hA, hB⟩ := hcut z t s ht0 hts hhalf
  have hus := frozen_holderX_restrict ⊤ UR Us Dgeom (subset_univ _) hsub
    driftWeight H.fields (fun i => (H.fields_smooth G i).contDiffOn) 2
    (show 0 < (α : ℝ) from hα) hu
  obtain ⟨huTop, hfTop, _⟩ := frozen_holder_equation_norm_data ⊤ UR Dgeom (subset_univ _)
    H.fields (fun i => (H.fields_smooth G i).contDiffOn)
    (show 0 < (α : ℝ) from hα) u f hu heq
  have huLoc : LocallyIntegrableOn u (UR : Set (Fin N → ℝ)) volume := locallyIntegrableOn_of_locallyIntegrable_restrict (huTop.locallyIntegrable (by simp))
  have heqs := frozen_drift_equation_restrict UR Us hsub H.fields
    (fun i => (H.fields_smooth G i).contDiffOn) u f huLoc heq
  have hnlocal := (eLpNorm_mono_measure φ (Measure.restrict_le_self (μ := volume) (s := (Us : Set (Fin N → ℝ))))).trans hn
  have hAlocal (i : Fin q) :=
    (eLpNorm_mono_measure (fieldDerivative (H.fields i.succ) φ) (Measure.restrict_le_self (μ := volume) (s := (Us : Set (Fin N → ℝ))))).trans (hA i)
  have hBlocal : eLpNorm (sumSquaresWithDrift H.fields φ) ⊤
      (volume.restrict (Us : Set (Fin N → ℝ))) ≤ ENNReal.ofReal (b / (s - t) ^ 2) := by
    have hh := (eLpNorm_mono_measure (sumSquaresWithDrift H.fields φ) (Measure.restrict_le_self (μ := volume) (s := (Us : Set (Fin N → ℝ))))).trans hB
    have hcoeff : (q + 1 : ℝ≥0∞) * ENNReal.ofReal (c₂ / (s - t) ^ 2) =
        ENNReal.ofReal (b / (s - t) ^ 2) := by
      rw [show b / (s - t) ^ 2 = ((q + 1 : ℕ) : ℝ) * (c₂ / (s - t) ^ 2) by dsimp [b]; ring,
        ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
      simp only [Nat.cast_add, Nat.cast_one]
    exact hh.trans_eq hcoeff
  have hh := hcompact z Us Ut (hbuffer z s (hs.trans hRR)) u hus f heqs φ hone
    (a / (s - t)) (b / (s - t) ^ 2) (div_nonneg ha.le (sub_pos.mpr hts).le)
    (div_nonneg hb.le (sq_nonneg _)) hnlocal hAlocal hBlocal ε hε hε1
  have hmono (v : (Fin N → ℝ) → ℝ) (hv : MemLp v ⊤ (volume.restrict (UR : Set (Fin N → ℝ)))) :
      lpNorm v ∞ (volume.restrict (Us : Set (Fin N → ℝ))) ≤
        lpNorm v ∞ (volume.restrict (UR : Set (Fin N → ℝ))) :=
    ENNReal.toReal_mono hv.eLpNorm_ne_top (eLpNorm_mono_measure v (Measure.restrict_mono_set volume hsub))
  have hFu := hmono f hfTop
  have hUu := hmono u huTop
  have hbcoeff : 0 ≤ b / (s - t) ^ 2 := div_nonneg hb.le (sq_nonneg _)
  have hCcoeff : 0 ≤ C * ε ^ (-(2 * (3 + (G.homogeneousDimension : ℝ)) / (1 - (α : ℝ)))) :=
    mul_nonneg hC.le (Real.rpow_nonneg hε.le _)
  have hnear := mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add hFu (mul_le_mul_of_nonneg_left hUu hbcoeff))
      (le_refl (2 * (a / (s - t)) * (holderXENorm driftWeight H.fields
        (controlDistance univ driftWeight H.fields) Us 1 (α : ℝ) u).toReal))) hε.le
  have hfar := mul_le_mul_of_nonneg_left hUu hCcoeff
  have hfinal := hh.trans (add_le_add hnear hfar)
  simpa only [UR, Us, Ut, quasiballDomain, Opens.coe_mk, show 2 * (a / (s - t)) = 2 * a / (s - t) by ring] using hfinal

end RothschildStein.H3
