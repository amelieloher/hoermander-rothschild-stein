-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.WeightedScheduleCost
public import RothschildStein.G3.FiniteWords

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped ENNReal
namespace RothschildStein.G1

/-- The actual primitive quasiexponential has a uniform scalar
cost depending only on the step (BB proof of Theorem 1.53, p. 35). -/
theorem controlDistance_quasiExponentialPoint {m n : ℕ}
    {Ω : Set (Fin n → ℝ)} (w : Fin m → ℕ+)
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (U : Fin m → Set (Fin n → ℝ)) (hUΩ : ∀ i, U i ⊆ Ω)
    (τ : Fin m → ℝ)
    (Φ : Fin m → ((Fin n → ℝ) × ℝ) → (Fin n → ℝ))
    (hΦ : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Φ i) (U i ×ˢ Ioo (-τ i) (τ i)))
    (hODE : ∀ i x, x ∈ U i → Φ i (x, 0) = x ∧ ∀ v ∈ Ioo (-τ i) (τ i),
      HasDerivAt (fun z => Φ i (x, z)) (X i (Φ i (x, v))) v ∧ Φ i (x, v) ∈ Ω)
    (s : ℕ) (I : List (Fin m)) (hne : I ≠ []) (hI : wordWeight w I ≤ s)
    (t : ℝ) (ht : t ≠ 0)
    (x : Fin n → ℝ) (hx : x ∈ Ω)
    (hS : FlowScheduleAdmissible Φ (fun i t => t ^ (w i : ℕ)) U τ t (commutatorSchedule I) x) :
    controlDistance Ω w X x (G3.quasiExponentialPointMap w Φ I t x) ≤
      ENNReal.ofReal ((3 * 2 ^ (s - 1) : ℕ) * |t|) := by
  have hh := controlDistance_weighted_schedule w X U hUΩ τ Φ hΦ hODE t ht
    (commutatorSchedule I) x hx hS
  have hlen : (commutatorSchedule I).length ≤ 3 * 2 ^ (s - 1) := by
    have he := commutatorSchedule_length I hne
    have hl := (G3.length_le_weight w I).trans hI
    have hp : 2 ^ (I.length - 1) ≤ 2 ^ (s - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  apply hh.trans
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hlen) (abs_nonneg _)

/-- The reversed genuine primitive schedule has the same uniform cost. -/
theorem controlDistance_inverseQuasiExponentialPoint {m n : ℕ}
    {Ω : Set (Fin n → ℝ)} (w : Fin m → ℕ+)
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (U : Fin m → Set (Fin n → ℝ)) (hUΩ : ∀ i, U i ⊆ Ω)
    (τ : Fin m → ℝ)
    (Φ : Fin m → ((Fin n → ℝ) × ℝ) → (Fin n → ℝ))
    (hΦ : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Φ i) (U i ×ˢ Ioo (-τ i) (τ i)))
    (hODE : ∀ i x, x ∈ U i → Φ i (x, 0) = x ∧ ∀ v ∈ Ioo (-τ i) (τ i),
      HasDerivAt (fun z => Φ i (x, z)) (X i (Φ i (x, v))) v ∧ Φ i (x, v) ∈ Ω)
    (s : ℕ) (I : List (Fin m)) (hne : I ≠ []) (hI : wordWeight w I ≤ s)
    (t : ℝ) (ht : t ≠ 0)
    (x : Fin n → ℝ) (hx : x ∈ Ω)
    (hS : FlowScheduleAdmissible Φ (fun i t => t ^ (w i : ℕ)) U τ t (inverseSchedule (commutatorSchedule I)) x) :
    controlDistance Ω w X x (G3.inverseQuasiExponentialPointMap w Φ I t x) ≤
      ENNReal.ofReal ((3 * 2 ^ (s - 1) : ℕ) * |t|) := by
  have hh := controlDistance_weighted_schedule w X U hUΩ τ Φ hΦ hODE t ht
    (inverseSchedule (commutatorSchedule I)) x hx hS
  have hlen : (inverseSchedule (commutatorSchedule I)).length ≤ 3 * 2 ^ (s - 1) := by
    rw [inverseSchedule_length]
    have he := commutatorSchedule_length I hne
    have hl := (G3.length_le_weight w I).trans hI
    have hp : 2 ^ (I.length - 1) ≤ 2 ^ (s - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  apply hh.trans
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hlen) (abs_nonneg _)

end RothschildStein.G1
