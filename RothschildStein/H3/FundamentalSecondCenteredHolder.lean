-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.FundamentalSecondHolder
public import RothschildStein.H3.FrozenHolderTranslation
public import RothschildStein.H3.TranslatedCompactSource
public import RothschildStein.H3.PrincipalValueConvolutionTranslation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set
open scoped ENNReal NNReal
namespace RothschildStein.H3

/-- The actual second-kernel PV estimates have constants uniform
in the center of a ball of fixed radius. Translation is applied first to
sources and then inversely to the bounded PV output, avoiding any assumed
finiteness of the desired output norm. -/
theorem exists_fundamental_second_centered_PV_holder_bounds_of_controlNorm {N q : ℕ}
    (G : HomogeneousGroup N) (H : H1.StandingHypotheses G q)
    (K : H1.FundamentalKernel G H)
    (C : G2.ControlNormConclusion G driftWeight H.fields)
    {a : ℝ≥0} (ha : 0 < a) (ha1 : (a : ℝ) < 1)
    {R : ℝ} (hR : 0 < R) :
    ∃ B : Fin q → Fin q → ℝ, (∀ i j, 0 ≤ B i j) ∧
      ∀ z : Fin N → ℝ, ∀ F : (Fin N → ℝ) → ℝ,
        Continuous F → HasCompactSupport F →
        tsupport F ⊆ (quasiballDomain G C.norm z R : Set (Fin N → ℝ)) →
        holderENorm (controlDistance univ driftWeight H.fields) a univ F < ⊤ →
        ∀ i j,
          holderENorm (controlDistance univ driftWeight H.fields) a
            (quasiballDomain G C.norm z R : Set (Fin N → ℝ))
            (H1.principalValueConvolution G C.norm
              (fieldDerivative (H.fields i.succ) (fieldDerivative (H.fields j.succ) K)) F) ≤
          ENNReal.ofReal (B i j) *
            holderENorm (controlDistance univ driftWeight H.fields) a
              (quasiballDomain G C.norm z R : Set (Fin N → ℝ)) F := by
  let metric : MetricSpace (ControlCarrier N) :=
    gaugeMetric G C.norm C.constant_one C.symmetric
  let V := quasiballDomain G C.norm 0 R
  obtain ⟨B, hB, hb⟩ := exists_fundamental_second_PV_holder_bounds_of_controlNorm
    G H K C ha ha1 V hR (by
      intro x hx
      change C.norm (G.mul (G.inv 0) x) < R at hx
      simpa only [G2.inv_zero, G2.zero_mul] using hx)
  refine ⟨B, hB, ?_⟩
  intro z F hF hc hs hf i j
  let Fz := F ∘ G.mul z
  obtain ⟨hFz, hcz, hsz⟩ := translated_compact_source G C.norm z R F hF hc hs
  have hng := fixed_holder_norm_left_pullback_eq_of_controlNorm
    G driftWeight H.fields C z a univ F hf
  have hfz : holderENorm (controlDistance univ driftWeight H.fields) a univ Fz < ⊤ := by
    simpa only [preimage_univ] using hng.trans_lt hf
  have hfz' : @H2.BoundedHolder (ControlCarrier N) metric a univ Fz := by
    rw [frozen_holderENorm_eq_control_norm G driftWeight H.fields C] at hfz
    exact hfz
  have hbz := hb Fz hFz hcz hsz hfz' i j
  rw [← frozen_holderENorm_eq_control_norm G driftWeight H.fields C,
    ← frozen_holderENorm_eq_control_norm G driftWeight H.fields C] at hbz
  have hnF := fixed_holder_norm_left_pullback_eq_of_controlNorm G driftWeight H.fields C z a
    (quasiballDomain G C.norm z R : Set (Fin N → ℝ)) F
    ((S.holderENorm_mono _ a univ F (subset_univ _)).trans_lt hf)
  rw [quasiball_left_pullback] at hnF
  let P := H1.principalValueConvolution G C.norm
    (fieldDerivative (H.fields i.succ) (fieldDerivative (H.fields j.succ) K))
  have hpz : holderENorm (controlDistance univ driftWeight H.fields) a
      (V : Set (Fin N → ℝ)) (P Fz) < ⊤ :=
    hbz.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (by simpa only [V] using (hnF.trans_lt
        ((S.holderENorm_mono _ a univ F (subset_univ _)).trans_lt hf))))
  have hnP := fixed_holder_norm_left_pullback_eq_of_controlNorm G driftWeight H.fields C
    (G.inv z) a (V : Set (Fin N → ℝ)) (P Fz) hpz
  have hfun : (P Fz) ∘ G.mul (G.inv z) = P F := by
    rw [show P Fz = (P F) ∘ G.mul z from principalValueConvolution_left_pullback G _ _ F z]
    funext x
    exact congrArg (P F) ((G2.gaugeLeftTranslation G z).right_inv x)
  rw [show (V : Set (Fin N → ℝ)) =
    (quasiballDomain G C.norm 0 R : Set (Fin N → ℝ)) from rfl,
    quasiball_inverse_left_pullback, hfun] at hnP
  exact hnP.le.trans (hbz.trans_eq (congrArg (fun n => ENNReal.ofReal (B i j) * n) hnF))

end RothschildStein.H3
