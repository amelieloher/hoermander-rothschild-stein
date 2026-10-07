-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.CurveConcatenation

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped ENNReal

namespace RothschildStein.G1

/-- Rescaling an interval by its share of the total parameter respects
all positive integer weights (BB Prop 1.41, pp. 22–23). -/
theorem weighted_speed_bound {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (p : ℕ+) :
    a ^ (p : ℕ) / (a / (a + b)) ≤ (a + b) ^ (p : ℕ) := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by have := p.pos; omega : (p : ℕ) ≠ 0)
  rw [hk, pow_succ, pow_succ]
  have heq : a ^ k * a / (a / (a + b)) = a ^ k * (a + b) := by
    field_simp
  rw [heq]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ha.le (by linarith) k) (by linarith)

/-- Concatenating weighted controlled curves at δ/(δ+ε) gives parameter
δ+ε, with the endpoints preserved (BB Prop 1.41, pp. 22–23). -/
theorem exists_controlledCurve_concat {m n : ℕ} {Ω : Set (Fin n → ℝ)}
    {w : Fin m → ℕ+} {X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)}
    {δ ε : ℝ} {γ η : ℝ → (Fin n → ℝ)}
    (hγ : isControlledCurve Ω w X δ γ) (hη : isControlledCurve Ω w X ε η)
    (hends : γ 1 = η 0) :
    ∃ α, isControlledCurve Ω w X (δ + ε) α ∧ α 0 = γ 0 ∧ α 1 = η 1 := by
  let θ := δ / (δ + ε)
  have hsum : 0 < δ + ε := add_pos hγ.1 hη.1
  have hθ : 0 < θ := div_pos hγ.1 hsum
  have hθ1 : θ < 1 := (div_lt_one hsum).mpr (by linarith [hη.1])
  have hc : 1 - θ = ε / (δ + ε) := by dsimp [θ]; field_simp; ring
  refine ⟨joinedCurve θ γ η, isControlledCurve_join hγ hη hends hθ hθ1 hsum
    (fun i => weighted_speed_bound hγ.1 hη.1 (w i))
    (fun i => ?_), ?_, ?_⟩
  · rw [hc, add_comm δ ε]
    exact weighted_speed_bound hη.1 hγ.1 (w i)
  · simp only [joinedCurve, ite_eq_left hθ.le, zero_div]
  · simp only [joinedCurve, ite_eq_right (not_le.mpr hθ1), div_self (ne_of_gt (sub_pos.mpr hθ1))]

/-- Triangle inequality for the extended weighted distance, even
when a connecting class is empty or a distance is infinite
(BB Prop 1.41, pp. 22–23). -/
theorem controlDistance_triangle {m n : ℕ} (Ω : Set (Fin n → ℝ))
    (w : Fin m → ℕ+) (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)) (x y z : Fin n → ℝ) :
    controlDistance Ω w X x z ≤ controlDistance Ω w X x y + controlDistance Ω w X y z := by
  conv_rhs => rw [controlDistance, controlDistance, sInf_eq_iInf, sInf_eq_iInf]
  simp only [ENNReal.iInf_add, ENNReal.add_iInf]
  apply le_iInf
  intro a
  apply le_iInf
  rintro ⟨δ, rfl, γ, hγ, hγ0, hγ1⟩
  apply le_iInf
  intro b
  apply le_iInf
  rintro ⟨ε, rfl, η, hη, hη0, hη1⟩
  obtain ⟨α, hα, hα0, hα1⟩ := exists_controlledCurve_concat hη hγ (hη1.trans hγ0.symm)
  have hm := controlDistance_le_of_curve hα
  rw [hα0, hα1, hη0, hγ1, ENNReal.ofReal_add hη.1.le hγ.1.le] at hm
  exact hm

end RothschildStein.G1
