-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.MixedExteriorBounds
public import RothschildStein.H3.FieldDerivativeOperatorSum

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace RothschildStein.H3

/-- far part. The actual right sum-of-squares on the exterior
kernel and each prescribed left-field derivative have fixed global
bounds with loss epsilon^(gamma-4). This common loss is sufficient for
both the type-one and type-two kernels (BB p. 383). -/
theorem exists_right_exterior_operator_bounds {N q : ℕ} (G : HomogeneousGroup N)
    (H : H1.StandingHypotheses G q)
    {ν F : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    (hsν : ContDiffOn ℝ (⊤ : ℕ∞) ν {0}ᶜ)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hone : ∀ t : ℝ, t ≤ 1 / 2 → φ t = 1)
    (hzero : ∀ t : ℝ, 1 ≤ t → φ t = 0)
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F {0}ᶜ) {γ : ℝ} (hγ : γ ≤ 0)
    (hhom : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 → F (G.dilate t x) = t ^ γ * F x) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ ε : ℝ, 0 < ε → ε < 1 →
      let P := sumSquaresWithDrift (fun i => G2.rightField G (H.fields i 0))
        (exteriorCutoffKernel ν φ F ε)
      ContDiff ℝ (⊤ : ℕ∞) P ∧
      (∀ x, |P x| ≤ A * ε ^ (γ - 4)) ∧
      (∀ j x, |fieldDerivative (H.fields j) P x| ≤ B * ε ^ (γ - 4)) := by
  classical
  obtain ⟨C, hC, hb⟩ := exists_mixed_exterior_word_bounds G H hν hsν hφ hone hzero hF hγ hhom
  let r := fun i : Fin (q + 1) => Fin.natAdd (q + 1) i
  let l := fun i : Fin (q + 1) => Fin.castAdd (q + 1) i
  let Yr := fun i : Fin (q + 1) => G2.rightField G (H.fields i 0)
  let A := C [r 0] + ∑ i : Fin q, C [r i.succ, r i.succ]
  let D := fun j : Fin (q + 1) => C [l j, r 0] + ∑ i : Fin q, C [l j, r i.succ, r i.succ]
  let B := ∑ j : Fin (q + 1), D j
  have hD (j : Fin (q + 1)) : 0 ≤ D j :=
    add_nonneg (hC _) (Finset.sum_nonneg (fun i _ => hC _))
  have hDj (j : Fin (q + 1)) : D j ≤ B :=
    Finset.single_le_sum (fun j _ => hD j) (Finset.mem_univ j)
  refine ⟨A, B, add_nonneg (hC _) (Finset.sum_nonneg (fun i _ => hC _)),
    Finset.sum_nonneg (fun j _ => hD j), ?_⟩
  intro ε hε hε1
  dsimp only
  let E := exteriorCutoffKernel ν φ F ε
  have hE : ContDiff ℝ (⊤ : ℕ∞) E := contDiff_kernel_exterior_cutoff hν hsν hφ hone hF hε
  have hword (I : List (Fin (q + 1))) : ContDiff ℝ (⊤ : ℕ∞) (wordDerivative Yr I E) :=
    contDiffOn_univ.mp (S.contDiffOn_wordDerivative ⊤ Yr
      (fun i => (G2.contDiff_rightField G (H.fields i 0)).contDiffOn) I E hE.contDiffOn)
  have hP : ContDiff ℝ (⊤ : ℕ∞) (sumSquaresWithDrift Yr E) :=
    (hword [0]).add (ContDiff.sum (fun i _ => hword [i.succ, i.succ]))
  have hsmall (I : List (Fin ((q + 1) + (q + 1))))
      (hw : wordWeight (mixedInvariantWeights q) I ≤ 4) (x : Fin N → ℝ) :
      |wordDerivative (mixedInvariantFields G H) I E x| ≤ C I * ε ^ (γ - 4) := by
    have hw' : (wordWeight (mixedInvariantWeights q) I : ℝ) ≤ 4 := by exact_mod_cast hw
    exact (hb I ε hε x).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_ge hε hε1.le (by linarith)) (hC I))
  have hw0 : wordWeight (mixedInvariantWeights q) [r 0] ≤ 4 := by
    simp only [wordWeight, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      mixedInvariantWeights, r, Fin.addCases_right]
    norm_num [driftWeight]
  have hw2 (i : Fin q) : wordWeight (mixedInvariantWeights q) [r i.succ, r i.succ] ≤ 4 := by
    simp only [wordWeight, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      mixedInvariantWeights, r, Fin.addCases_right]
    norm_num [driftWeight]
  have hwl0 (j : Fin (q + 1)) : wordWeight (mixedInvariantWeights q) [l j, r 0] ≤ 4 := by
    simp only [wordWeight, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      mixedInvariantWeights, l, r, Fin.addCases_left, Fin.addCases_right]
    by_cases hj : j = 0 <;> norm_num [driftWeight, hj]
  have hwl2 (j : Fin (q + 1)) (i : Fin q) :
      wordWeight (mixedInvariantWeights q) [l j, r i.succ, r i.succ] ≤ 4 := by
    simp only [wordWeight, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      mixedInvariantWeights, l, r, Fin.addCases_left, Fin.addCases_right]
    by_cases hj : j = 0 <;> norm_num [driftWeight, hj]
  refine ⟨hP, ?_, ?_⟩
  · intro x
    have h0 := hsmall [r 0] hw0 x
    have h2 (i : Fin q) := hsmall [r i.succ, r i.succ] (hw2 i) x
    simp only [wordDerivative, mixedInvariantFields, r, Fin.addCases_right] at h0 h2
    change |fieldDerivative (Yr 0) E x + ∑ i : Fin q,
      fieldDerivative (Yr i.succ) (fieldDerivative (Yr i.succ) E) x| ≤ A * ε ^ (γ - 4)
    calc
      _ ≤ |fieldDerivative (Yr 0) E x| + ∑ i : Fin q,
          |fieldDerivative (Yr i.succ) (fieldDerivative (Yr i.succ) E) x| :=
        (abs_add_le _ _).trans (add_le_add le_rfl (Finset.abs_sum_le_sum_abs _ _))
      _ ≤ C [r 0] * ε ^ (γ - 4) + ∑ i : Fin q, C [r i.succ, r i.succ] * ε ^ (γ - 4) :=
        add_le_add h0 (Finset.sum_le_sum (fun i _ => h2 i))
      _ = _ := by dsimp [A]; rw [← Finset.sum_mul]; ring
  · intro j x
    have h0 := hsmall [l j, r 0] (hwl0 j) x
    have h2 (i : Fin q) := hsmall [l j, r i.succ, r i.succ] (hwl2 j i) x
    simp only [wordDerivative, mixedInvariantFields, l, r, Fin.addCases_left, Fin.addCases_right] at h0 h2
    rw [fieldDerivative_sumSquaresWithDrift Yr
      (fun i => G2.contDiff_rightField G (H.fields i 0)) (H.fields j) hE x]
    calc
      _ ≤ |fieldDerivative (H.fields j) (fieldDerivative (Yr 0) E) x| + ∑ i : Fin q,
          |fieldDerivative (H.fields j) (fieldDerivative (Yr i.succ) (fieldDerivative (Yr i.succ) E)) x| :=
        (abs_add_le _ _).trans (add_le_add le_rfl (Finset.abs_sum_le_sum_abs _ _))
      _ ≤ C [l j, r 0] * ε ^ (γ - 4) + ∑ i : Fin q, C [l j, r i.succ, r i.succ] * ε ^ (γ - 4) :=
        add_le_add h0 (Finset.sum_le_sum (fun i _ => h2 i))
      _ = D j * ε ^ (γ - 4) := by dsimp [D]; rw [← Finset.sum_mul]; ring
      _ ≤ B * ε ^ (γ - 4) := mul_le_mul_of_nonneg_right (hDj j) (Real.rpow_nonneg hε.le _)

end RothschildStein.H3
