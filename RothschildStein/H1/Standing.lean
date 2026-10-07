-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.HormanderSystem
public import RothschildStein.G2.Gauge
public import RothschildStein.G2.InvariantDivergence

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

@[expose] public section
noncomputable section
namespace RothschildStein.H1
open Hormander.Interface
variable {N q : ℕ} (G : HomogeneousGroup N)

/-- The class of homogeneous Hörmander operators, with optional drift
(BB Definitions 6.5–6.8, pp. 254–256). -/
structure StandingHypotheses (q : ℕ) where
  q_pos : 0 < q
  norm : G2.HomogeneousNorm G
  fields : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ)
  invariant : ∀ i, G2.IsLeftInvariantField G (fields i)
  homogeneous : ∀ i, G2.IsHomogeneousField G (fields i) (if i = 0 then 2 else 1)
  horizontal_nonzero : ∃ i : Fin q, fields i.succ ≠ 0
  span_origin : Submodule.span ℝ (Set.range (fun w : LieWord q => LieWord.eval fields w 0)) = ⊤

/-- Smoothness is automatic for the prescribed invariant fields (BB p. 110). -/
theorem StandingHypotheses.fields_smooth (H : StandingHypotheses G q) (i : Fin (q + 1)) :
    ContDiff ℝ (⊤ : ℕ∞) (H.fields i) := by
  rw [(H.invariant i).eq_leftField G]
  exact G2.contDiff_leftField G _

/-- The bracket-span condition at the origin implies bracket spanning on every open set
(BB pp. 124, 135). -/
theorem StandingHypotheses.spansOn (H : StandingHypotheses G q) (U : Set (Fin N → ℝ)) :
    LieAlgebraSpansOn U H.fields := by
  intro x _
  exact G2.lieAlgebraSpansOn_of_origin G H.fields H.invariant H.span_origin x (Set.mem_univ x)

/-- The first coordinate, without a global nonzero-dimension typeclass. -/
def firstIndex : Fin N := ⟨0, G.dimension_pos⟩

/-- A nonzero horizontal field forces the first coordinate weight to be one
(BB Proposition 6.9, pp. 256–257). -/
theorem StandingHypotheses.first_weight (H : StandingHypotheses G q) :
    G.weight (firstIndex G) = 1 := by
  obtain ⟨i, hi⟩ := H.horizontal_nonzero
  have hzero : H.fields i.succ 0 ≠ 0 := by
    intro hz
    apply hi
    rw [(H.invariant i.succ).eq_leftField G, hz]
    funext x
    exact map_zero _
  have hh : G2.IsHomogeneousField G (G2.leftField G (H.fields i.succ 0)) 1 := by
    rw [← (H.invariant i.succ).eq_leftField G]
    simpa using H.homogeneous i.succ
  obtain ⟨j, hj⟩ := G2.leftField_homogeneous_degree G hzero hh
  have hjn : G.weight j = 1 := by exact_mod_cast hj
  have hle := G.weight_mono (show firstIndex G ≤ j by
    change 0 ≤ j.val
    exact Nat.zero_le _)
  have hp := G.weight_pos (firstIndex G)
  omega

/-- The dimension threshold Q>2 is exactly the integer threshold Q≥3
(BB Theorem 6.18, p. 264). -/
theorem dimension_gt_two_iff : (2 : ℝ) < G.homogeneousDimension ↔ 3 ≤ G.homogeneousDimension := by
  constructor
  · intro h
    have hn : 2 < G.homogeneousDimension := by exact_mod_cast h
    omega
  · intro h
    have hn : 2 < G.homogeneousDimension := by omega
    exact_mod_cast hn

end RothschildStein.H1
