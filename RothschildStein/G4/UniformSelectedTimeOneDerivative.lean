-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.UniformBufferedDerivativeSmallness
public import RothschildStein.G4.SelectedFlowDerivativeBounds

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
open scoped BigOperators

namespace RothschildStein.G4

/-- The actual selected-plus-auxiliary flow has uniformly small
selected-coordinate derivative errors. The numerical radius precedes
all primitive fields and selected frames; the flow itself is constructed
from the primitive jets (BB Lemma 9.49, p. 444). -/
theorem exists_uniform_selected_timeOne_derivative (k n s h q : ℕ)
    (hn : 0 < n) (hs : 0 < s) (horder : q + 1 = n * s + s) (hq : q + 1 ≤ h)
    (w : Fin (k + 1) → ℕ+) (M Δ R t κ : ℝ)
    (hM : 0 ≤ M) (hΔ : 0 < Δ) (hR : 0 < R) (ht : 0 < t) (ht1 : t ≤ 1) (hκ : 0 < κ) :
    let m := n + Fintype.card (ShortWord w s)
    let δ := R / (64 * (1 + (m : ℝ) * wordJetBase n 0 s M ^ s))
    ∃ e : ℝ, 0 < e ∧ e ≤ 1 ∧ e ≤ t ∧ e < δ ∧
      ∀ (Ω : Set (Fin n → ℝ)), IsOpen Ω →
      ∀ (X : Fin (k + 1) → (Fin n → ℝ) → (Fin n → ℝ)),
      (∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (X j) Ω) → bracketStepOn Ω w X s →
      ∀ x₀ : Fin n → ℝ, closedBall x₀ R ⊆ Ω →
      (∀ j, HasJetBound Ω (closedBall x₀ R) (X j)
        (max (2 * (n * s) + 2 * s) (max ((q + 1) * s) (h + 1 + s))) M) →
      (∀ y ∈ closedBall x₀ R, ∃ B : Fin n → ShortWord w s,
        Δ ≤ |frameDet (shortField w X) B y|) →
      ∀ B : Fin n → ShortWord w s,
      ∃ Φ : (((Fin m → ℝ) × (Fin n → ℝ)) × ℝ) → (Fin n → ℝ),
        ContDiffOn ℝ (⊤ : ℕ∞) Φ ((ball 0 δ ×ˢ ball x₀ (R / 4)) ×ˢ Ioo (-2) 2) ∧
        (∀ a ∈ ball 0 δ, ∀ x ∈ ball x₀ (R / 4), Φ ((a, x), 0) = x ∧
          ∀ τ ∈ Ioo (-2 : ℝ) 2, Φ ((a, x), τ) ∈ ball x₀ R ∧
            HasDerivAt (fun v => Φ ((a, x), v))
              (∑ j, a j • shortField w X (selectedAuxiliaryIndex w B j) (Φ ((a, x), τ))) τ) ∧
        ∀ x ∈ ball x₀ (R / 8), ∀ r : ℝ, 0 < r → r ≤ 1 →
          IsSuboptimal (shortField w X) (shortWeight w) B x t r →
        ∀ (u : Fin n → ℝ) (v : Fin (Fintype.card (ShortWord w s)) → ℝ),
          (∀ j, |Fin.append u v j| ≤
            (e * r) ^ (shortWeight w (selectedAuxiliaryIndex w B j) : ℕ)) →
        (|frameDet (shortField w X) B (Φ ((Fin.append u v, x), 1)) -
          frameDet (shortField w X) B x| ≤ |frameDet (shortField w X) B x| / 2) ∧
        ∀ (i ℓ : Fin n),
          |frameCoefficient (shortField w X) B (fun y =>
            fderiv ℝ (fun a => Φ ((Fin.append a v, x), 1)) u (Pi.single i 1) -
              shortField w X (B i) y) ℓ (Φ ((Fin.append u v, x), 1))| ≤
            κ * r ^ (((shortWeight w (B ℓ) : ℕ) : ℤ) - ((shortWeight w (B i) : ℕ) : ℤ)) := by
  intro m δ
  have hA : 0 ≤ (m : ℝ) * wordJetBase n 0 s M ^ s :=
    mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (wordJetBase_nonneg_and_le hM).1 _)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨e, he, he1, het, heδ, hsmall⟩ := exists_uniform_buffered_mapped_derivative_smallness
    k n s m h q hn hs horder hq w M Δ R δ t κ hM hΔ hR hδ ht ht1 hκ le_rfl
  refine ⟨e, he, he1, het, heδ, ?_⟩
  intro Ω hΩ X hX hstep x₀ hRΩ hjets hmax B
  let I := selectedAuxiliaryIndex w B
  obtain ⟨Φ, hsmooth, hflow, _hforward⟩ := exists_uniform_mapped_buffered_timeOne_flow
    (m := m) hΩ w X hX I x₀ hR hM hRΩ (fun j => (hjets j).mono (by omega))
  have hclosed : ∀ a ∈ ball 0 δ, ∀ x ∈ ball x₀ (R / 4), Φ ((a, x), 0) = x ∧
      ∀ τ ∈ Ioo (-2 : ℝ) 2, Φ ((a, x), τ) ∈ closedBall x₀ R ∧
        HasDerivAt (fun v => Φ ((a, x), v))
          (∑ j, a j • shortField w X (I j) (Φ ((a, x), τ))) τ := by
    intro a ha x hx
    exact ⟨(hflow a ha x hx).1, fun τ hτ =>
      ⟨ball_subset_closedBall ((hflow a ha x hx).2 τ hτ).1, ((hflow a ha x hx).2 τ hτ).2⟩⟩
  refine ⟨Φ, hsmooth, hflow, ?_⟩
  intro x hx r hr hr1 hB u v ha
  have her1 : e * r ≤ 1 := (mul_le_mul_of_nonneg_right he1 hr.le).trans (by simpa using hr1)
  have hnorm := weighted_coefficients_norm_le (fun j => shortWeight w (I j))
    (mul_nonneg he.le hr.le) her1 ha
  have hz : Fin.append u v ∈ ball 0 δ := by
    rw [mem_ball, dist_zero_right]
    exact (hnorm.trans (mul_le_of_le_one_right he.le hr1)).trans_lt heδ
  have hxin : x ∈ ball x₀ (R / 4) := ball_subset_ball (by linarith) hx
  have hcoef := timeOne_coefficient_slice_differentiableAt isOpen_ball Φ hsmooth hz hxin
  obtain ⟨hselected, hcoords⟩ := hsmall Ω hΩ X hX hstep I x₀ hRΩ hjets hmax Φ hsmooth hclosed
    B x hx r hr hr1 hB (Fin.append u v) ha
  exact ⟨hselected, selected_timeOne_derivative_frame_bound (shortField w X) (shortWeight w)
    B I (selectedAuxiliaryIndex_selected w B) Φ u v x hcoef hcoords⟩

end RothschildStein.G4
