-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.SmoothAuxiliaryBallProviders
public import Mathlib.Data.Finset.Lattice.Fold

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal BigOperators
namespace RothschildStein.G4

/-- Arbitrary compact center sets have actual auxiliary-ball
volume bounds from smoothness and the bracket-step hypothesis alone.
A finite subcover preserves the original-radius volume polynomial
(BB Theorem 9.12, pp. 405–406). -/
theorem exists_compact_auxiliary_ball_volume_provider {k n s : ℕ}
    (hn : 0 < n) (hs : 0 < s) (w : Fin (k + 1) → ℕ+)
    {Ω K : Set (Fin n → ℝ)} (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (X : Fin (k + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (hstep : bracketStepOn Ω w X s) :
    ∃ c C ε : ℝ, 0 < c ∧ 0 < C ∧ 0 < ε ∧
      ∀ x ∈ K, ∀ r, 0 < r → r ≤ ε →
        let Λ := volumePolynomial
          (fun B : Fin n → ShortWord w s => frameDet (shortField w X) B x)
          (fun B => ∑ i, (shortWeight w (B i) : ℕ)) r
        ENNReal.ofReal (c * Λ) ≤
          volume {y | auxiliaryDistance (s := s) Ω w X x y < ENNReal.ofReal r} ∧
        volume {y | auxiliaryDistance (s := s) Ω w X x y < ENNReal.ofReal r} ≤
          ENNReal.ofReal (C * Λ) := by
  classical
  rcases K.eq_empty_or_nonempty with he | hne
  · refine ⟨1, 1, 1, by norm_num, by norm_num, by norm_num, ?_⟩
    intro x hx
    simp only [he, mem_empty_iff_false] at hx
  choose R c C ε hR hc hC hε hRΩ hb using
    (fun z : K => exists_smooth_auxiliary_ball_volume_provider hn hs w hΩ X hX hstep (hKΩ z.property))
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun z : K => ball z.val (R z / 16))
    (fun _ => isOpen_ball) (fun x hx => mem_iUnion.mpr
      ⟨⟨x, hx⟩, mem_ball_self (div_pos (hR ⟨x, hx⟩) (by norm_num))⟩)
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨z₀, hz₀, _hxz₀⟩ := mem_iUnion₂.mp (ht hx₀)
  have htne : t.Nonempty := ⟨z₀, hz₀⟩
  refine ⟨t.inf' htne c, t.sup' htne C, t.inf' htne ε,
    (Finset.lt_inf'_iff htne).mpr (fun z _ => hc z),
    (hC z₀).trans_le (Finset.le_sup' C hz₀),
    (Finset.lt_inf'_iff htne).mpr (fun z _ => hε z), ?_⟩
  intro x hx r hr hrr
  obtain ⟨z, hz, hxz⟩ := mem_iUnion₂.mp (ht hx)
  have hh := hb z x (ball_subset_closedBall hxz) r hr (hrr.trans (Finset.inf'_le ε hz))
  have hΛ : 0 ≤ volumePolynomial
      (fun B : Fin n → ShortWord w s => frameDet (shortField w X) B x)
      (fun B => ∑ i, (shortWeight w (B i) : ℕ)) r := volumePolynomial_nonneg _ _ hr.le
  constructor
  · exact (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (Finset.inf'_le c hz) hΛ)).trans hh.1
  · exact hh.2.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
      (Finset.le_sup' C hz) hΛ))

end RothschildStein.G4
