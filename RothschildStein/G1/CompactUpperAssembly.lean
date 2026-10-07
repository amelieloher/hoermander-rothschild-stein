-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.LocalControlLowerBound
public import RothschildStein.G1.ComparisonControlTopology
public import Mathlib.Data.Finset.Lattice.Fold

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
open scoped ENNReal
namespace RothschildStein.G1

/-- A finite subcover makes the locally constructed upper
chart constants uniform on any compact set (BB p. 35). -/
theorem exists_compact_control_upper_of_local_upper {m n : ℕ}
    {Ω K : Set (Fin n → ℝ)} (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (w : Fin m → ℕ+) (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)) (α : ℝ)
    (hloc : ∀ z ∈ Ω, ∃ ρ C : ℝ, 0 < ρ ∧ 0 < C ∧ ∀ x ∈ ball z ρ,
      ∀ y : Fin n → ℝ, ‖y - x‖ < ρ →
        controlDistance Ω w X x y ≤ ENNReal.ofReal (C * ‖y - x‖ ^ α)) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 < C ∧ ∀ x ∈ K, ∀ y : Fin n → ℝ,
      ‖y - x‖ < ρ → controlDistance Ω w X x y ≤ ENNReal.ofReal (C * ‖y - x‖ ^ α) := by
  classical
  rcases K.eq_empty_or_nonempty with hKempty | hKne
  · refine ⟨1, 1, by norm_num, by norm_num, ?_⟩
    intro x hx
    exact False.elim (by simp only [hKempty, mem_empty_iff_false] at hx)
  choose ρ C hρ hC hbound using (fun z : K => hloc z.val (hKΩ z.property))
  have hcover : K ⊆ ⋃ z : K, ball z.val (ρ z) := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, mem_ball_self (hρ ⟨x, hx⟩)⟩
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun z : K => ball z.val (ρ z))
    (fun _ => isOpen_ball) hcover
  obtain ⟨x₀, hx₀⟩ := hKne
  obtain ⟨z₀, hz₀⟩ := mem_iUnion.mp (ht hx₀)
  obtain ⟨hz₀t, _⟩ := mem_iUnion.mp hz₀
  have htne : t.Nonempty := ⟨z₀, hz₀t⟩
  refine ⟨t.inf' htne ρ, t.sup' htne C,
    (Finset.lt_inf'_iff htne).mpr (fun z _ => hρ z),
    (hC z₀).trans_le (Finset.le_sup' C hz₀t), ?_⟩
  intro x hx y hy
  obtain ⟨z, hz⟩ := mem_iUnion.mp (ht hx)
  obtain ⟨hzt, hxz⟩ := mem_iUnion.mp hz
  have hh := hbound z x hxz y (hy.trans_le (Finset.inf'_le ρ hzt))
  exact hh.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
    (Finset.le_sup' C hzt) (Real.rpow_nonneg (norm_nonneg _) _)))

/-- The compact lower bound and local upper estimates give the full
comparison whenever the local upper bound holds. -/
theorem localControlComparison_of_local_upper {m n s : ℕ}
    {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) (w : Fin m → ℕ+)
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContinuousOn (X i) Ω)
    (hloc : ∀ z ∈ Ω, ∃ ρ C : ℝ, 0 < ρ ∧ 0 < C ∧ ∀ x ∈ ball z ρ,
      ∀ y : Fin n → ℝ, ‖y - x‖ < ρ →
        controlDistance Ω w X x y ≤ ENNReal.ofReal (C * ‖y - x‖ ^ (1 / (s : ℝ)))) :
    LocalControlComparison Ω w X s := by
  intro K hK hKΩ
  obtain ⟨ρl, cminus, hρl, hminus, hlow⟩ :=
    exists_compact_local_control_lower_bound hΩ hK hKΩ w X hX
  obtain ⟨ρu, cplus, hρu, hplus, hupp⟩ :=
    exists_compact_control_upper_of_local_upper hK hKΩ w X (1 / (s : ℝ)) hloc
  refine ⟨min ρl ρu, cminus, cplus, lt_min hρl hρu, hminus, hplus, ?_⟩
  intro x hx y _hy hnear
  exact ⟨hlow x hx y (hnear.trans_le (min_le_left _ _)),
    hupp x hx y (hnear.trans_le (min_le_right _ _))⟩

end RothschildStein.G1
