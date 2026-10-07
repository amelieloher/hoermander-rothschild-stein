-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.FullHolderPatchGluing
public import RothschildStein.H3.QuasiballSecondHolderEstimate

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped ENNReal NNReal
namespace RothschildStein.H3

/-- The actual local beta estimate and a buffered cover with
positive pair radius yield the full interior fixed Holder estimate.
The geometric constant is selected before every solution and forcing. -/
theorem finite_cover_estimate_of_controlNorm {N q : ℕ} {ι : Type*}
    (G : HomogeneousGroup N) (H : H1.StandingHypotheses G q)
    (K : H1.FundamentalKernel G H) (hQ : 2 < (G.homogeneousDimension : ℝ))
    (C : G2.ControlNormConclusion G driftWeight H.fields)
    (μ : G2.GroupMollifier G H.norm) (φ : G2.GroupMollifier G C.norm)
    (ν : G2.HomogeneousNorm G) (hν : ν.Smooth)
    (U E : Opens (Fin N → ℝ)) (hEU : (E : Set (Fin N → ℝ)) ⊆ U)
    {a : ℝ≥0} (ha : 0 < a) (ha1 : (a : ℝ) < 1)
    (centers : ι → Fin N → ℝ) {r ell : ℝ} (hr : 0 < r) (hell : 0 < ell)
    (hballs : ∀ i, (quasiballDomain G ν (centers i) (2 * r) : Set (Fin N → ℝ)) ⊆ U)
    (hcover : ∀ x ∈ (E : Set (Fin N → ℝ)), ∃ i, x ∈ quasiballDomain G ν (centers i) r)
    (hpairs : ∀ x ∈ (E : Set (Fin N → ℝ)), ∀ y ∈ (E : Set (Fin N → ℝ)),
      (controlDistance univ driftWeight H.fields x y).toReal < ell →
      ∃ i, x ∈ quasiballDomain G ν (centers i) r ∧ y ∈ quasiballDomain G ν (centers i) r) :
    ∃ B : ℝ, 0 < B ∧ ∀ u f : (Fin N → ℝ) → ℝ,
      memHolderX driftWeight H.fields (controlDistance univ driftWeight H.fields) U 2 a u →
      holderENorm (controlDistance univ driftWeight H.fields) a (U : Set (Fin N → ℝ)) f < ⊤ →
      hasDistributionEquationWithDrift U H.fields (fun i => (H.fields_smooth G i).contDiffOn)
        (Distribution.ofFun U u volume (⊤ : ℕ∞)) f →
      holderXENorm driftWeight H.fields (controlDistance univ driftWeight H.fields) E 2 a u ≤
        ENNReal.ofReal B * (holderENorm (controlDistance univ driftWeight H.fields) a
          (U : Set (Fin N → ℝ)) f + eLpNorm u ⊤ (volume.restrict (U : Set (Fin N → ℝ)))) := by
  let β := 2 + (a : ℝ) + 2 * (3 + (G.homogeneousDimension : ℝ)) / (1 - (a : ℝ))
  obtain ⟨L, hL, hstep⟩ := quasiball_second_holder_estimate_of_controlNorm G H K hQ C μ φ ν hν ha ha1
    (Rmax := 2 * r) (by linarith)
  let c := ((wordFamily (driftWeight (q := q)) 2).card : ℝ) * ((1 + 2 / ell ^ (a : ℝ)) + 1)
  let B := c * (L * r ^ (-β)) + 1
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hLp : 0 ≤ L * r ^ (-β) := by positivity
  refine ⟨B, by dsimp [B]; positivity, ?_⟩
  intro u f hu hf heq
  let D := controlDistanceGeometry_of_controlNorm G driftWeight H.fields C
  let W := holderENorm (controlDistance univ driftWeight H.fields) a (U : Set (Fin N → ℝ)) f +
    eLpNorm u ⊤ (volume.restrict (U : Set (Fin N → ℝ)))
  have hucont := RothschildStein.S.continuousOn_of_holderENorm_lt_top_on_subset ⊤ D
    (subset_univ _) (show 0 < (a : ℝ) from ha) hu.1
  have husup := eLpNorm_top_le_local_holderNorm ⊤ U D (subset_univ _)
    (show 0 < (a : ℝ) from ha) hu.1
  have hW : W < ⊤ := ENNReal.add_lt_top.mpr ⟨hf, husup.trans_lt hu.1⟩
  let M := (ENNReal.ofReal (L * r ^ (-β)) * W).toReal
  have hM : ENNReal.ofReal M = ENNReal.ofReal (L * r ^ (-β)) * W :=
    ENNReal.ofReal_toReal (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hW.ne)
  let P := fun i => quasiballDomain G ν (centers i) r
  have hPU (i : ι) : (P i : Set (Fin N → ℝ)) ⊆ U := by
    intro x hx
    exact hballs i (hx.trans (by linarith : r < 2 * r))
  have hn (i : ι) : holderXENorm driftWeight H.fields (controlDistance univ driftWeight H.fields)
      (P i) 2 a u ≤ ENNReal.ofReal M := by
    let V := quasiballDomain G ν (centers i) (2 * r)
    have hv := hballs i
    have huf := memHolderX_restrict_intrinsic driftWeight H.fields _ U V hv 2 a hu
    have hff := (RothschildStein.S.holderENorm_mono _ a (U : Set (Fin N → ℝ)) f hv).trans_lt hf
    have he := frozen_drift_equation_restrict U V hv H.fields
      (fun j => (H.fields_smooth G j).contDiffOn) u f
      (hucont.locallyIntegrableOn U.isOpen.measurableSet) heq
    have hb := hstep (centers i) (2 * r) r (by linarith) le_rfl (by linarith) (by linarith) u f huf hff he
    rw [show 2 * r - r = r by ring] at hb
    rw [hM]
    exact hb.trans (mul_le_mul' le_rfl (add_le_add
      (RothschildStein.S.holderENorm_mono _ a (U : Set (Fin N → ℝ)) f hv)
      (eLpNorm_mono_measure u (Measure.restrict_mono_set volume hv))))
  have hb := full_holder_norm_patch_gluing_of_controlNorm G H C U E hEU P hPU 2 a
    (M := M) ENNReal.toReal_nonneg hell hcover hpairs u hu hn
  change holderXENorm _ _ _ E 2 a u ≤ ENNReal.ofReal (c * M) at hb
  rw [ENNReal.ofReal_mul hc, hM, ← mul_assoc, ← ENNReal.ofReal_mul hc] at hb
  exact hb.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal (by dsimp [B]; linarith)) le_rfl)

end RothschildStein.H3
