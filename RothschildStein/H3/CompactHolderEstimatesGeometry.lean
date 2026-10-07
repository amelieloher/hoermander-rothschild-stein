-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.HolderSeminormFromGeometry
public import RothschildStein.H3.HolderCenteredEstimate
public import RothschildStein.H3.IntrinsicWordRestriction
public import RothschildStein.Provider.GroupRegularityInputs

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped ENNReal NNReal BigOperators
namespace RothschildStein.H3

/-- The compact Hölder estimate gives a global seminorm bound and
center-uniform full norm bounds for the stated source class and equation,
under the fundamental-kernel and uniform metric hypotheses (BB pp. 379–380). -/
theorem compactHolderEstimates_of_controlNorm {N q : ℕ}
    (G : HomogeneousGroup N) (H : H1.StandingHypotheses G q)
    (K : H1.FundamentalKernel G H) (hQ : 2 < (G.homogeneousDimension : ℝ))
    (P : G2.ControlNormConclusion G driftWeight H.fields) :
    Provider.CompactHolderEstimates G driftWeight H.fields
      (fun Ω T f => hasDistributionEquationWithDrift Ω H.fields
        (fun i => (H.fields_smooth G i).contDiffOn) T f) P.norm := by
  classical
  obtain ⟨φ⟩ := G2.nonempty_groupMollifier G P.norm
  constructor
  · intro α ha ha1
    let a : ℝ≥0 := ⟨α,ha.le⟩
    obtain ⟨C,hC,hbound⟩ := seminorm_estimate_of_controlNorm G H K hQ P φ ⊤ a ha ha1
    refine ⟨C,hC,?_⟩
    intro u hu
    obtain ⟨jet,hzero,hwords,hsource⟩ := hbound u hu
    simp only [Opens.coe_top, indicator_univ] at hwords hsource
    rcases hsource with ⟨hclass,heq,hb⟩
    refine ⟨_,hclass,heq,jet,?_,hb⟩
    intro I hI
    exact (hwords I ((mem_driftSecondWordFamily_iff I).mp hI).le).1
  · intro α ha ha1 R hR
    let a : ℝ≥0 := ⟨α,ha.le⟩
    obtain ⟨C,hC,hbound⟩ := center_uniform_estimate_of_controlNorm G H K hQ P φ a ha ha1 hR
    refine ⟨C,hC,?_⟩
    intro z u hu hs
    let U := quasiballDomain G P.norm z R
    have hsupport : tsupport u ⊆ (U : Set (Fin N → ℝ)) := by
      intro x hx
      have hd := hs hx
      change controlDistance univ driftWeight H.fields z x < ENNReal.ofReal R at hd
      rw [P.distance_eq] at hd
      have hd' := (ENNReal.ofReal_lt_ofReal_iff hR).mp hd
      change G2.gaugeDistance G P.norm x z < R
      rw [G2.gaugeDistance_symmetric G P.norm P.symmetric z x]
      exact hd'
    have hc : HasCompactSupport u := by
      change IsCompact (closure (Function.support u))
      simpa only [Opens.coe_top, univ_inter] using hu.2.1
    have hclose : closure ((U : Set (Fin N → ℝ)) ∩ Function.support u) ⊆ tsupport u :=
      closure_mono inter_subset_right
    have huU : memHolderXCompact driftWeight H.fields
        (controlDistance univ driftWeight H.fields) U 2 a u :=
      ⟨memHolderX_restrict_intrinsic driftWeight H.fields
          (controlDistance univ driftWeight H.fields) ⊤ U (subset_univ _) 2 a hu.1,
        hc.isCompact.of_isClosed_subset isClosed_closure hclose, hclose.trans hsupport⟩
    have he : (U : Set (Fin N → ℝ)).indicator u = u := by
      funext x
      by_cases hx : x ∈ (U : Set (Fin N → ℝ))
      · exact indicator_of_mem hx u
      · rw [indicator_of_notMem hx]
        exact (image_eq_zero_of_notMem_tsupport (fun ht => hx (hsupport ht))).symm
    obtain ⟨jet,hzero,hwords,hsource⟩ := hbound z u huU
    rw [he] at hsource
    dsimp only at hsource
    exact ⟨_,hsource.1,hsource.2.1,hsource.2.2⟩

end RothschildStein.H3
