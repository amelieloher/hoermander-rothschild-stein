-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.FirstCoordinate

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

@[expose] public section
noncomputable section
namespace RothschildStein.H1
open Hormander.Interface
open scoped BigOperators
variable {N q : ℕ} (G : HomogeneousGroup N)

/-- Generator weights, with index-zero drift of weight two. -/
def generatorWeight (i : Fin (q + 1)) : ℕ := if i = 0 then 2 else 1

/-- Every nonempty Lie word has positive weighted length (BB Definition 1.17, p. 10). -/
theorem lieWordWeight_pos (w : LieWord q) : 0 < G2.lieWordWeight generatorWeight w := by
  induction w with
  | generator i => simp only [G2.lieWordWeight, generatorWeight]; split_ifs <;> omega
  | bracket a b iha ihb => change 0 < G2.lieWordWeight generatorWeight a + G2.lieWordWeight generatorWeight b; omega

/-- Every word in the standing system has its assigned weight as degree (BB p. 114). -/
theorem StandingHypotheses.word_homogeneous (H : StandingHypotheses G q) (w : LieWord q) :
    G2.IsHomogeneousField G (LieWord.eval H.fields w) (G2.lieWordWeight generatorWeight w) := by
  apply G2.lieWord_homogeneous G H.fields generatorWeight H.invariant
  intro i
  simpa [generatorWeight] using H.homogeneous i

/-- A genuine bracket word has no first-coordinate component
(BB Proposition 6.9, p. 257). -/
theorem StandingHypotheses.bracket_first_zero (H : StandingHypotheses G q)
    (a b : LieWord q) : LieWord.eval H.fields (.bracket a b) 0 (firstIndex G) = 0 := by
  have hh := H.word_homogeneous G (.bracket a b)
  have hi := G2.lieWord_invariant G H.fields H.invariant (.bracket a b)
  rw [hi.eq_leftField G] at hh
  apply (G2.leftField_homogeneous_iff G _ _).mp hh
  rw [H.first_weight]
  have ha := lieWordWeight_pos a
  have hb := lieWordWeight_pos b
  have hwt : 2 ≤ G2.lieWordWeight generatorWeight (.bracket a b) := by
    change 2 ≤ G2.lieWordWeight generatorWeight a + G2.lieWordWeight generatorWeight b
    omega
  exact_mod_cast (show (1 : ℕ) ≠ G2.lieWordWeight generatorWeight (.bracket a b) by omega)

/-- The first-coordinate square sum is strictly positive
(BB Proposition 6.9, pp. 256–257). -/
theorem StandingHypotheses.horizontalFirstSquareSum_pos (H : StandingHypotheses G q) :
    0 < horizontalFirstSquareSum G H := by
  have hn : 0 ≤ horizontalFirstSquareSum G H := Finset.sum_nonneg fun i _ => sq_nonneg _
  by_contra hp
  have hs : horizontalFirstSquareSum G H = 0 := le_antisymm (le_of_not_gt hp) hn
  have hz : ∀ i : Fin q, H.fields i.succ 0 (firstIndex G) = 0 := by
    intro i
    have hi := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j (_ : j ∈ (Finset.univ : Finset (Fin q))) => sq_nonneg (H.fields j.succ 0 (firstIndex G)))).mp hs i (Finset.mem_univ i)
    exact sq_eq_zero_iff.mp hi
  let K := LinearMap.ker (LinearMap.proj (firstIndex G) : (Fin N → ℝ) →ₗ[ℝ] ℝ)
  have hle : Submodule.span ℝ (Set.range (fun w : LieWord q => LieWord.eval H.fields w 0)) ≤ K := by
    apply Submodule.span_le.mpr
    rintro v ⟨w, rfl⟩
    change LieWord.eval H.fields w 0 (firstIndex G) = 0
    cases w with
    | generator i =>
      change H.fields i 0 (firstIndex G) = 0
      exact Fin.cases (H.drift_first_zero G 0) hz i
    | bracket a b => exact H.bracket_first_zero G a b
  rw [H.span_origin] at hle
  have he := hle (show Hormander.Interface.basisVec (firstIndex G) ∈
    (⊤ : Submodule ℝ (Fin N → ℝ)) from trivial)
  change Hormander.Interface.basisVec (firstIndex G) (firstIndex G) = 0 at he
  simp [Hormander.Interface.basisVec] at he

end RothschildStein.H1
