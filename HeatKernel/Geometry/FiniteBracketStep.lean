-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.InvariantBracket
public import RothschildStein.Definitions.HomogeneousGroup.horizontalFields
public import RothschildStein.Definitions.bracketSpansOn
public import RothschildStein.Definitions.bracketStepOn
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-! Finite bracket generation for left-invariant vector fields. -/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section
open Set
open scoped BigOperators

namespace HeatKernel
open RothschildStein

/-- Every iterated bracket of left-invariant fields is left invariant. -/
theorem isLeftInvariantField_wordBracket {N q : ℕ} (G : HomogeneousGroup N)
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, G2.IsLeftInvariantField G (X i)) (I : List (Fin q)) :
    G2.IsLeftInvariantField G (wordBracket X I) := by
  induction I with
  | nil => intro x y; simp [wordBracket]
  | cons i I ih =>
    cases I with
    | nil => exact hX i
    | cons j J => exact (hX i).lieBracket G ih

/-- A spanning bracket family has a finite weight bound at a fixed point. -/
theorem exists_bracketStepOn_singleton {N q : ℕ}
    (w : Fin q → ℕ+) (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (x : Fin N → ℝ) (hx : bracketSpansOn {x} X) :
    ∃ s, bracketStepOn {x} w X s := by
  classical
  let S := {v | ∃ I : List (Fin q), I ≠ [] ∧ v = wordBracket X I x}
  obtain ⟨t, ht, _, hspan, _⟩ := Submodule.exists_finset_span_eq_linearIndepOn ℝ S
  have hs : Submodule.span ℝ (t : Set (Fin N → ℝ)) = ⊤ :=
    hspan.trans (hx x (by simp))
  have hw : ∀ v : t, ∃ I : List (Fin q), I ≠ [] ∧ v.val = wordBracket X I x :=
    fun v => ht v.property
  choose I hI he using hw
  refine ⟨∑ v : t, wordWeight w (I v), ?_⟩
  intro y hy
  have hxy : y = x := by simpa using hy
  subst y
  apply top_unique
  rw [← hs]
  apply Submodule.span_mono
  intro v hv
  refine ⟨I ⟨v, hv⟩, hI _, ?_, he ⟨v, hv⟩⟩
  exact Finset.single_le_sum (s := Finset.univ)
    (f := fun v : t => wordWeight w (I v)) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ (⟨v, hv⟩ : t))

/-- The tangent map of a left translation is surjective. -/
theorem surjective_fderiv_leftTranslation {N : ℕ} (G : HomogeneousGroup N)
    (x y : Fin N → ℝ) : Function.Surjective (fderiv ℝ (G.mul x) y) := by
  have hx := (G2.contDiff_leftTranslation G x).differentiable (by simp)
  have hi := (G2.contDiff_leftTranslation G (G.inv x)).differentiable (by simp)
  have he : G.mul x ∘ G.mul (G.inv x) = id := by
    funext z
    simp only [Function.comp_apply, ← G2.mul_assoc, G2.mul_inv, G2.zero_mul, id_eq]
  have hd := fderiv_comp (G.mul x y) hx.differentiableAt hi.differentiableAt
  have hy : G.mul (G.inv x) (G.mul x y) = y := by
    rw [← G2.mul_assoc, G2.inv_mul, G2.zero_mul]
  rw [he, hy, fderiv_id] at hd
  intro v
  refine ⟨fderiv ℝ (G.mul (G.inv x)) (G.mul x y) v, ?_⟩
  exact (congrArg (fun L : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ) => L v) hd).symm

/-- Bracket generation at the identity gives one uniform finite step for invariant fields. -/
theorem exists_bracketStepOn_of_isLeftInvariantField {N q : ℕ} (G : HomogeneousGroup N)
    (w : Fin q → ℕ+) (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, G2.IsLeftInvariantField G (X i)) (hspan : bracketSpansOn {0} X) :
    ∃ s, bracketStepOn univ w X s := by
  obtain ⟨s, hs⟩ := exists_bracketStepOn_singleton w X 0 hspan
  refine ⟨s, fun x _ => ?_⟩
  let S := {v | ∃ I : List (Fin q), I ≠ [] ∧ wordWeight w I ≤ s ∧
    v = wordBracket X I 0}
  let T := {v | ∃ I : List (Fin q), I ≠ [] ∧ wordWeight w I ≤ s ∧
    v = wordBracket X I x}
  let L := (fderiv ℝ (G.mul x) 0).toLinearMap
  have himage : L '' S ⊆ T := by
    rintro _ ⟨v, ⟨I, hne, hw, rfl⟩, rfl⟩
    refine ⟨I, hne, hw, ?_⟩
    exact (G2.mul_zero G x) ▸ (isLeftInvariantField_wordBracket G X hX I x 0)
  have htop : Submodule.map L (Submodule.span ℝ S) = ⊤ := by
    rw [show Submodule.span ℝ S = ⊤ from hs 0 (by simp), Submodule.map_top]
    exact LinearMap.range_eq_top.mpr (surjective_fderiv_leftTranslation G x 0)
  apply top_unique
  rw [← htop, Submodule.map_span]
  exact Submodule.span_mono himage

/-- The generating horizontal fields of a homogeneous group have a uniform finite bracket step. -/
theorem exists_bracketStepOn_horizontalFields {N q : ℕ} (G : HomogeneousGroup N)
    (hq : q ≤ N) (hspan : bracketSpansOn univ (G.horizontalFields hq)) :
    ∃ s, bracketStepOn univ (fun _ : Fin q => 1) (G.horizontalFields hq) s := by
  apply exists_bracketStepOn_of_isLeftInvariantField G
  · intro i
    exact G2.leftField_invariant G _
  · intro x _
    exact hspan x (mem_univ x)

end HeatKernel
