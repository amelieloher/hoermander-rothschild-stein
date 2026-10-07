-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.Standing
public import RothschildStein.G2.ControlRankBridge
public import RothschildStein.G2.ControlNormConstruction
public import RothschildStein.G1.ActualControlComparison
public import RothschildStein.Definitions.driftWeight

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace RothschildStein.H3

/-- The standing origin span has a uniform
finite weighted step. Words above the homogeneous dimension vanish at
the origin because an invariant field's nonzero degree is a coordinate
weight. This removes an extra geometry premise from the H3 assembly. -/
def standingHomogeneousHormanderSystem {N q : ℕ}
    (G : HomogeneousGroup N) (H : H1.StandingHypotheses G q) :
    G2.HomogeneousHormanderSystem G q where
  q_pos := H.q_pos
  fields := H.fields
  invariant := H.invariant
  homogeneous := H.homogeneous
  step := max 2 G.homogeneousDimension
  span_origin := by
    apply top_unique
    rw [← H.span_origin]
    apply Submodule.span_le.mpr
    rintro v ⟨t, rfl⟩
    by_cases ht : G2.lieWordWeight (fun i : Fin (q + 1) => if i = 0 then 2 else 1) t ≤
        max 2 G.homogeneousDimension
    · exact Submodule.subset_span ⟨⟨t, ht⟩, rfl⟩
    · have hzero : Hormander.Interface.LieWord.eval H.fields t 0 = 0 := by
        by_contra hn
        have hh := G2.lieWord_homogeneous G H.fields
          (fun i : Fin (q + 1) => if i = 0 then 2 else 1) H.invariant
          (fun i => by simpa only [Nat.cast_ite, Nat.cast_ofNat, Nat.cast_one] using H.homogeneous i) t
        rw [(G2.lieWord_invariant G H.fields H.invariant t).eq_leftField G] at hh
        obtain ⟨j, hj⟩ := G2.leftField_homogeneous_degree G hn hh
        have hw : G.weight j ≤ G.homogeneousDimension :=
          Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
        have he : G.weight j = G2.lieWordWeight (fun i : Fin (q + 1) => if i = 0 then 2 else 1) t := by
          exact_mod_cast hj
        rw [he] at hw
        exact ht (hw.trans (Nat.le_max_right _ _))
      change Hormander.Interface.LieWord.eval H.fields t 0 ∈ _
      rw [hzero]
      exact Submodule.zero_mem _

/-- The exact full shared control-norm
certificate is constructed from the standing hypotheses and the proved
smooth finite-step G1 comparison theorem. -/
def standingControlNormConclusion {N q : ℕ}
    (G : HomogeneousGroup N) (H : H1.StandingHypotheses G q) :
    G2.ControlNormConclusion G driftWeight H.fields := by
  let S := standingHomogeneousHormanderSystem G H
  have hs : 1 ≤ S.step := by change 1 ≤ max 2 G.homogeneousDimension; omega
  have hw : ∀ i : Fin (q + 1), (driftWeight i : ℕ) ≤ S.step := by
    intro i
    change (driftWeight i : ℕ) ≤ max 2 G.homogeneousDimension
    by_cases hi : i = 0 <;> simp [driftWeight, hi]
  have hew : (G2.systemWeights : Fin (q + 1) → ℕ+) = driftWeight := by
    funext i
    by_cases hi : i = 0 <;> simp [G2.systemWeights, driftWeight, hi]
  have hstep : bracketStepOn univ driftWeight H.fields S.step := by
    simpa only [hew, S, standingHomogeneousHormanderSystem] using S.standard_step G
  have hhom : ∀ i : Fin (q + 1), G2.IsHomogeneousField G (H.fields i) (driftWeight i : ℕ) := by
    intro i
    by_cases hi : i = 0 <;> simpa [driftWeight, hi] using H.homogeneous i
  exact G2.controlNormConclusion_of_local_comparison G driftWeight H.fields
    (fun i => (H.fields_smooth G i).continuous) H.invariant hhom (by omega : 0 < S.step)
    (G1.localControlComparison_of_smooth_bracketStep isOpen_univ driftWeight H.fields
      (fun i => (H.fields_smooth G i).contDiffOn) hs hw hstep)

end RothschildStein.H3
