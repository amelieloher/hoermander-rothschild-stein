-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.CompletedBCH
public import RothschildStein.G3.BCHSecondOrder
@[expose] public section
noncomputable section
namespace RothschildStein.G3

/-- Ordinary homogeneous component of a completed associative word series
(BB pp. 470–471). -/
def homogeneousComponent {a : ℕ} (n : ℕ) (f : CoefficientSeries a) : CoefficientSeries a :=
  fun J => if J.length = n then f J else 0

/-- The universal associative BCH series in two noncommuting letters
(BB Theorem 9.68, pp. 469–471). -/
def universalBCH : CoefficientSeries 2 := formalBCH (letterSeries 0) (letterSeries 1)

/-- Universal homogeneous associative BCH coefficients (BB p. 471).
This definition alone does not assert the Lie-polynomial property. -/
def bchComponent (n : ℕ) : CoefficientSeries 2 := homogeneousComponent n universalBCH

/-- The universal coefficient has precisely ordinary degree n (BB p. 471). -/
theorem bchComponent_homogeneous (n : ℕ) :
    Homogeneous (fun _ : Fin 2 => 1) n (bchComponent n) := by
  intro J hJ
  simp only [ordinary_weight] at hJ
  exact ite_eq_right hJ

/-- Universal letters have zero constant coefficient (BB p. 468). -/
theorem letterSeries_positive {a : ℕ} (i : Fin a) : PositiveSeries (letterSeries i) := by
  simp [PositiveSeries, coefficient, letterSeries]

/-- The universal BCH series has no constant component (BB p. 470). -/
theorem bchComponent_zero : bchComponent 0 = 0 := by
  funext J
  change bchComponent 0 J = 0
  by_cases h : J = []
  · subst J
    exact formalBCH_positive (letterSeries_positive 0) (letterSeries_positive 1)
  · have hl : J.length ≠ 0 := fun he => h (List.length_eq_zero_iff.mp he)
    simp [bchComponent, homogeneousComponent, hl]

/-- C₁(x,y)=x+y coefficientwise (BB Lemma 9.69, p. 471). -/
theorem bchComponent_one : bchComponent 1 = letterSeries 0 + letterSeries 1 := by
  funext J
  change bchComponent 1 J = letterSeries 0 J + letterSeries 1 J
  by_cases h : J.length = 1
  · have hd := finiteBCH_sub_add_order
      (ordinaryTrunc_positive (letterSeries_positive (0 : Fin 2)) 1)
      (ordinaryTrunc_positive (letterSeries_positive (1 : Fin 2)) 1)
    have hb : wordWeight (fun _ : Fin 2 => 1) J ≤ 1 := by rw [ordinary_weight, h]
    have he := (finiteOrderAtLeast_iff 2 _).mp hd (boundedWord (fun _ => 1) J hb)
      (by simpa only [boundedWord, ordinary_weight, h] using (show 1 < 2 by omega))
    have hz := sub_eq_zero.mp he
    change finiteBCH (ordinaryTrunc 1 (letterSeries 0)) (ordinaryTrunc 1 (letterSeries 1))
      (boundedWord (fun _ => 1) J hb) = letterSeries 0 J + letterSeries 1 J at hz
    unfold bchComponent homogeneousComponent
    rw [ite_eq_left h]
    change formalBCH (letterSeries 0) (letterSeries 1) J = _
    unfold formalBCH
    obtain ⟨i, rfl⟩ := List.length_eq_one_iff.mp h
    exact hz
  · have h₀ : J ≠ [0] := by intro he; subst J; simp at h
    have h₁ : J ≠ [1] := by intro he; subst J; simp at h
    simp [bchComponent, homogeneousComponent, h, letterSeries, h₀, h₁]

/-- C₂(x,y)=[x,y]/2 coefficientwise (BB Lemma 9.69, p. 471). -/
theorem bchComponent_two :
    bchComponent 2 = (1 / 2 : ℝ) • (formalBracket [0, 1] : CoefficientSeries 2) := by
  funext J
  change bchComponent 2 J = (1 / 2 : ℝ) * formalBracket [0, 1] J
  by_cases h : J.length = 2
  · have hb : wordWeight (fun _ : Fin 2 => 1) J ≤ 2 := by rw [ordinary_weight, h]
    have hbr : ⁅ordinaryTrunc 2 (letterSeries (0 : Fin 2)),
        ordinaryTrunc 2 (letterSeries (1 : Fin 2))⁆ =
        (truncatedBracket [0, 1] : FiniteWordAlgebra 2 2 (fun _ => 1)) :=
      nested_eval_truncatedBracket (.bracket 0 (.letter 1))
    have heq := finiteBCH_cutoff_two
      (ordinaryTrunc_positive (letterSeries_positive (0 : Fin 2)) 2)
      (ordinaryTrunc_positive (letterSeries_positive (1 : Fin 2)) 2)
    rw [hbr] at heq
    have he := congrFun heq (boundedWord (fun _ => 1) J hb)
    change finiteBCH (ordinaryTrunc 2 (letterSeries 0)) (ordinaryTrunc 2 (letterSeries 1))
      (boundedWord (fun _ => 1) J hb) =
      letterSeries 0 J + letterSeries 1 J + (1 / 2 : ℝ) * formalBracket [0, 1] J at he
    have h₀ : J ≠ [0] := by intro he; subst J; simp at h
    have h₁ : J ≠ [1] := by intro he; subst J; simp at h
    simp only [letterSeries, ite_eq_right h₀, ite_eq_right h₁, zero_add] at he
    unfold bchComponent homogeneousComponent
    rw [ite_eq_left h]
    change formalBCH (letterSeries 0) (letterSeries 1) J = _
    unfold formalBCH
    obtain ⟨i, j, rfl⟩ := List.length_eq_two.mp h
    exact he
  · have hz := formalBracket_homogeneous (fun _ : Fin 2 => 1) [0, 1] J
      (by simpa [ordinary_weight] using h)
    simp only [bchComponent, homogeneousComponent, ite_eq_right h, hz, mul_zero]

end RothschildStein.G3
