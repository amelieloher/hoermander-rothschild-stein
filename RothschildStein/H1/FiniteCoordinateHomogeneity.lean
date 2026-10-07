-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.LocalFinitePartialPairing
public import RothschildStein.H1.PuncturedFieldHomogeneity
public import RothschildStein.G2.OperatorCoefficientCriterion

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped BigOperators
namespace RothschildStein.H1
variable {N : ℕ} (G : HomogeneousGroup N)

/-- a coordinate word subtracts its precise
weighted degree with only its length of punctured differentiability. -/
theorem coordinateWord_punctured_homogeneity_finite (l : List (Fin N))
    {f : (Fin N → ℝ) → ℝ} {β : ℝ}
    (hc : ContDiffOn ℝ l.length f {(0 : Fin N → ℝ)}ᶜ)
    (hf : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 → f (G.dilate t x) = t ^ β * f x) :
    ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 →
      wordDerivative G2.coordinateFields l f (G.dilate t x) =
        t ^ (β - (l.map fun j => (G.weight j : ℝ)).sum) * wordDerivative G2.coordinateFields l f x := by
  induction l with
  | nil => simpa only [wordDerivative, List.map_nil, List.sum_nil, sub_zero] using hf
  | cons j l ih =>
    have htail := ih (hc.of_le (by simp))
    let U : Opens (Fin N → ℝ) := ⟨{0}ᶜ, isOpen_compl_singleton⟩
    have hX (a : Fin N) : ContDiffOn ℝ (⊤ : ℕ∞) (G2.coordinateFields a) (U : Set (Fin N → ℝ)) := contDiffOn_const
    have hct : ContDiffOn ℝ 1 (wordDerivative G2.coordinateFields l f) {(0 : Fin N → ℝ)}ᶜ :=
      S.contDiffOn_wordDerivative_finite U G2.coordinateFields hX l 1 f
        (by change ContDiffOn ℝ (1 + l.length : ℕ) f {(0 : Fin N → ℝ)}ᶜ
            simpa only [List.length_cons, Nat.add_comm] using hc)
    have hV : G2.IsHomogeneousField G (G2.coordinateFields j) (G.weight j : ℝ) := by
      intro t ht x
      change G.dilate t (Hormander.Interface.basisVec j) = t ^ (G.weight j : ℝ) • Hormander.Interface.basisVec j
      rw [← G2.dilationDifferential_apply, G2.dilationDifferential_basis, Real.rpow_natCast]
    intro t ht x hx
    have hs := fieldDerivative_punctured_homogeneity G hV hct htail ht hx
    have hd : β - (l.map fun a => (G.weight a : ℝ)).sum - (G.weight j : ℝ) =
        β - ((j :: l).map fun a => (G.weight a : ℝ)).sum := by
      simp only [List.map_cons, List.sum_cons]
      ring
    rw [hd] at hs
    exact hs

/-- The fixed multi-index coordinate word has
exactly its stated weighted degree. -/
theorem coordinateWord_weight_sum (a : Fin N → ℕ) :
    ((G2.coordinateWord a).map fun j => (G.weight j : ℝ)).sum =
      (∑ j, G.weight j * a j : ℕ) := by
  classical
  have h (l : List (Fin N)) :
      ((l.flatMap fun j => List.replicate (a j) j).map fun j => (G.weight j : ℝ)).sum =
        (l.map fun j => (a j : ℝ) * (G.weight j : ℝ)).sum := by
    induction l with
    | nil => simp
    | cons j l ih => simp [List.flatMap_cons, List.map_append, ih, nsmul_eq_mul]
  rw [G2.coordinateWord, h, ← Fin.sum_univ_def]
  push_cast
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The kernel multi-index derivative has degree
β−weight(a), using exactly |a| punctured derivatives. -/
theorem euclideanPartial_punctured_homogeneity_finite (a : Fin N → ℕ)
    {f : (Fin N → ℝ) → ℝ} {β : ℝ}
    (hc : ContDiffOn ℝ (∑ j, a j : ℕ) f {(0 : Fin N → ℝ)}ᶜ)
    (hf : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 → f (G.dilate t x) = t ^ β * f x)
    {t : ℝ} (ht : 0 < t) {x : Fin N → ℝ} (hx : x ≠ 0) :
    euclideanPartial a f (G.dilate t x) =
      t ^ (β - (∑ j, G.weight j * a j : ℕ)) * euclideanPartial a f x := by
  have hs := coordinateWord_punctured_homogeneity_finite G (G2.coordinateWord a)
    (by simpa only [G2.coordinateWord_length] using hc) hf t ht x hx
  simpa only [G2.coordinate_word_partial, coordinateWord_weight_sum] using hs

end RothschildStein.H1
