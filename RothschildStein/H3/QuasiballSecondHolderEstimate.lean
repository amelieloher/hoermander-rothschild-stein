-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.QuasiballSecondLocalizedEstimate
public import RothschildStein.H3.QuasiballSourceLoss
public import RothschildStein.H3.QuasiballFirstInterpolation
public import RothschildStein.H3.LocalSecondHolderLossENNReal
public import RothschildStein.H3.FrozenDriftEquationRestriction
public import RothschildStein.H3.FrozenHolderEquationNormData

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped ENNReal NNReal
namespace RothschildStein.H3

/-- The complete local fixed weight-two norm satisfies the
exact beta loss on smooth-gauge quasiballs. Constants precede all
centers, radii and inputs; the actual fixed equation is used. -/
theorem quasiball_second_holder_estimate_of_controlNorm {N q : ℕ}
    (G : HomogeneousGroup N) (H : H1.StandingHypotheses G q)
    (K : H1.FundamentalKernel G H) (hQ : 2 < (G.homogeneousDimension : ℝ))
    (C : G2.ControlNormConclusion G driftWeight H.fields)
    (μ : G2.GroupMollifier G H.norm) (φ₀ : G2.GroupMollifier G C.norm)
    (ν : G2.HomogeneousNorm G) (hν : ν.Smooth)
    {a : ℝ≥0} (ha : 0 < a) (ha1 : (a : ℝ) < 1)
    {Rmax : ℝ} (hRmax : 0 < Rmax) :
    let γ := 2 * (3 + (G.homogeneousDimension : ℝ)) / (1 - (a : ℝ))
    let β := 2 + (a : ℝ) + γ
    ∃ A : ℝ, 0 < A ∧ ∀ z : Fin N → ℝ, ∀ R t : ℝ,
      0 < R → R ≤ Rmax → R / 2 ≤ t → t < R →
      ∀ u f : (Fin N → ℝ) → ℝ,
      memHolderX driftWeight H.fields (controlDistance univ driftWeight H.fields)
        (quasiballDomain G ν z R) 2 a u →
      holderENorm (controlDistance univ driftWeight H.fields) a
        (quasiballDomain G ν z R : Set (Fin N → ℝ)) f < ⊤ →
      hasDistributionEquationWithDrift (quasiballDomain G ν z R) H.fields
        (fun i => (H.fields_smooth G i).contDiffOn)
        (Distribution.ofFun (quasiballDomain G ν z R) u volume (⊤ : ℕ∞)) f →
      holderXENorm driftWeight H.fields (controlDistance univ driftWeight H.fields)
        (quasiballDomain G ν z t) 2 a u ≤ ENNReal.ofReal (A * (R - t) ^ (-β)) *
          (holderENorm (controlDistance univ driftWeight H.fields) a
            (quasiballDomain G ν z R : Set (Fin N → ℝ)) f +
            eLpNorm u ⊤ (volume.restrict (G2.gaugeBall G ν z R))) := by
  let γ := 2 * (3 + (G.homogeneousDimension : ℝ)) / (1 - (a : ℝ))
  let β := 2 + (a : ℝ) + γ
  have hγ : 0 < γ := div_pos (by linarith) (sub_pos.mpr ha1)
  obtain ⟨L, hL, hstep⟩ := quasiball_second_localized_estimate_of_controlNorm G H K hQ C μ φ₀ ν hν ha ha1 hRmax
  obtain ⟨A, B, hA, hB, hsource⟩ := quasiball_source_holder_loss_of_controlNorm G H C ν hν ha ha1.le hRmax
  obtain ⟨c, hc, hinterp⟩ := quasiball_first_interpolation_of_controlNorm G H K C hQ μ ν hν ha ha1 hRmax
  let c' := c * (1 / 2 : ℝ) ^ (-γ)
  have hc' : 0 ≤ c' := by dsimp [c']; positivity
  obtain ⟨T, hT, hscalar⟩ := local_second_holder_loss_ennreal (α := (a : ℝ))
    (γ := γ) (show 0 ≤ (a : ℝ) from a.coe_nonneg) hγ.le hRmax (mul_nonneg hL.le hA.le)
    (mul_nonneg hL.le hB.le) hc' hL.le
  refine ⟨T * (2⁻¹ : ℝ) ^ (-β), by positivity, ?_⟩
  intro z R t hR hRR hhalf ht u f hu hf heq
  let s := (R + t) / 2
  let d := s - t
  let UR := quasiballDomain G ν z R
  let Us := quasiballDomain G ν z s
  let D := controlDistanceGeometry_of_controlNorm G driftWeight H.fields C
  let F := holderENorm (controlDistance univ driftWeight H.fields) a (UR : Set (Fin N → ℝ)) f
  let U := eLpNorm u ⊤ (volume.restrict (G2.gaugeBall G ν z R))
  let ψ := holderXENorm driftWeight H.fields (controlDistance univ driftWeight H.fields) Us 1 a u
  let Ψ := holderXENorm driftWeight H.fields (controlDistance univ driftWeight H.fields)
    (quasiballDomain G ν z t) 2 a u
  have ht0 : 0 < t := by linarith
  have hts : t < s := by dsimp [s]; linarith
  have hsR : s < R := by dsimp [s]; linarith
  have hd : 0 < d := sub_pos.mpr hts
  have hdR : d ≤ Rmax := by dsimp [d, s]; linarith
  have hsub : (Us : Set (Fin N → ℝ)) ⊆ UR := fun _ hx => hx.trans hsR
  have hus : memHolderX driftWeight H.fields (controlDistance univ driftWeight H.fields) Us 2 a u :=
    memHolderX_restrict_intrinsic driftWeight H.fields _ UR Us hsub 2 a hu
  have hfs : holderENorm (controlDistance univ driftWeight H.fields) a (Us : Set (Fin N → ℝ)) f < ⊤ :=
    (RothschildStein.S.holderENorm_mono _ a (UR : Set (Fin N → ℝ)) f hsub).trans_lt hf
  have hucont := RothschildStein.S.continuousOn_of_holderENorm_lt_top_on_subset ⊤ D
    (subset_univ _) (show 0 < (a : ℝ) from ha) hu.1
  have heqs := frozen_drift_equation_restrict UR Us hsub H.fields
    (fun i => (H.fields_smooth G i).contDiffOn) u f
    (hucont.locallyIntegrableOn UR.isOpen.measurableSet) heq
  obtain ⟨jet, hz, hj, hlocal⟩ := hstep z t s ht0 hts (by dsimp [s]; linarith)
    (hsR.le.trans hRR) u hus
  have hsrc := hsource z t s ht0 hts (by dsimp [s]; linarith) hdR u f jet hz hj hfs heqs
  have hFnorm : holderENorm (controlDistance univ driftWeight H.fields) a
      (Us : Set (Fin N → ℝ)) f ≤ F :=
    RothschildStein.S.holderENorm_mono _ a (UR : Set (Fin N → ℝ)) f hsub
  have hsup : eLpNorm u ⊤ (volume.restrict (G2.gaugeBall G ν z s)) ≤ U :=
    eLpNorm_mono_measure u (Measure.restrict_mono hsub le_rfl)
  have hdata := frozen_holder_equation_norm_data ⊤ UR D (subset_univ _) H.fields
    (fun i => (H.fields_smooth G i).contDiffOn) (show 0 < (a : ℝ) from ha) u f hu heq
  have hU : U < ⊤ := hdata.1
  have hψ : ψ < ⊤ := ((holderXENorm_restrict_le driftWeight H.fields _ UR Us hsub 1 a u).trans_lt hdata.2.2)
  have hfSup := eLpNorm_top_le_local_holderNorm ⊤ UR D (subset_univ _)
    (show 0 < (a : ℝ) from ha) hf
  have hi := hinterp z R hR hRR u f hu heq (1 / 2) s (by norm_num) le_rfl
    (by dsimp [s]; linarith) hsR
  have hi' : ψ.toReal ≤ F.toReal / 2 + c' * d ^ (-γ) * U.toReal := by
    have hfReal := ENNReal.toReal_mono hf.ne hfSup
    have hg : R - s = d := by dsimp [s, d]; ring
    change ψ.toReal ≤ (1 / 2) * (eLpNorm f ⊤ (volume.restrict (UR : Set (Fin N → ℝ)))).toReal +
      c * (1 / 2 : ℝ) ^ (-γ) * (R - s) ^ (-γ) * U.toReal at hi
    rw [hg] at hi
    dsimp only [c']
    nlinarith [hi, hfReal]
  have he : Ψ ≤ ENNReal.ofReal (L * A * d ^ (-(a : ℝ))) * F +
      ENNReal.ofReal (L * B * d ^ (-(2 + (a : ℝ)))) * ψ + ENNReal.ofReal L * U := by
    have hb := hlocal.trans (mul_le_mul' le_rfl (add_le_add
      (hsrc.trans (add_le_add (mul_le_mul' le_rfl hFnorm) le_rfl)) hsup))
    change Ψ ≤ _ at hb
    apply hb.trans_eq
    rw [mul_add, mul_add]
    simp only [← mul_assoc]
    rw [← ENNReal.ofReal_mul hL.le, ← ENNReal.ofReal_mul hL.le]
    dsimp only [d, ψ, Us]
    congr 2 <;> ring_nf
  have hh := hscalar d F U ψ Ψ hd hdR hf hU hψ hi' he
  have hp : T * d ^ (-β) = (T * (2⁻¹ : ℝ) ^ (-β)) * (R - t) ^ (-β) := by
    have he : d = (R - t) * (2⁻¹ : ℝ) := by dsimp [d, s]; ring
    rw [he, Real.mul_rpow (by linarith : 0 ≤ R - t) (by norm_num : 0 ≤ (2⁻¹ : ℝ))]
    ring
  simpa only [β, hp] using hh

end RothschildStein.H3
