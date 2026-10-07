-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.UniformSelectedTimeOneDerivative
public import RothschildStein.G4.MappedFlowFramePersistence
public import RothschildStein.G4.SelectedFlowDerivativeBounds

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
open scoped BigOperators

namespace RothschildStein.G4

/-- One constructed flow satisfies selected derivative and all-frame persistence bounds, with the determinant constant chosen before suboptimality. -/
theorem exists_uniform_selected_timeOne_persistence (k n s h q : ℕ)
    (hn : 0 < n) (hs : 0 < s) (horder : q + 1 = n * s + s) (hq : q + 1 ≤ h)
    (w : Fin (k + 1) → ℕ+) (M Δ R κ : ℝ)
    (hM : 0 ≤ M) (hΔ : 0 < Δ) (hR : 0 < R) (hκ : 0 < κ) :
    let m := n + Fintype.card (ShortWord w s)
    let δ := R / (64 * (1 + (m : ℝ) * wordJetBase n 0 s M ^ s))
    ∃ D : ℝ, 0 < D ∧ ∀ t : ℝ, 0 < t → t ≤ 1 →
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
        (∀ C : Fin n → ShortWord w s,
          |frameDet (shortField w X) C (Φ ((Fin.append u v, x), 1))| ≤
            D * t⁻¹ ^ n * r ^ (frameWeight (shortWeight w) B - frameWeight (shortWeight w) C) *
              |frameDet (shortField w X) B x|) ∧
        ∀ (i ℓ : Fin n),
          |frameCoefficient (shortField w X) B (fun y =>
            fderiv ℝ (fun a => Φ ((Fin.append a v, x), 1)) u (Pi.single i 1) -
              shortField w X (B i) y) ℓ (Φ ((Fin.append u v, x), 1))| ≤
            κ * r ^ (((shortWeight w (B ℓ) : ℕ) : ℤ) - ((shortWeight w (B i) : ℕ) : ℤ)) := by
  intro m δ
  have hA : 0 ≤ (m : ℝ) * wordJetBase n 0 s M ^ s :=
    mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (wordJetBase_nonneg_and_le hM).1 _)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨D, hD, hpersist⟩ := exists_uniform_mapped_flow_frame_persistence
    k n s m δ hδ hn hs w M Δ hM hΔ
  refine ⟨D, hD, ?_⟩
  intro t ht ht1
  obtain ⟨es, hes, hes1, hest, hesδ, hselected⟩ := exists_uniform_selected_timeOne_derivative
    k n s h q hn hs horder hq w M Δ R t κ hM hΔ hR ht ht1 hκ
  obtain ⟨ep, hep, hep1, hept, hepδ, hother⟩ := hpersist t ht ht1
  let e := min es ep
  have he : 0 < e := lt_min hes hep
  have hees : e ≤ es := min_le_left _ _
  have heep : e ≤ ep := min_le_right _ _
  refine ⟨e, he, hees.trans hes1, hees.trans hest, hees.trans_lt hesδ, ?_⟩
  intro Ω hΩ X hX hstep x₀ hRΩ hjets hmax B
  obtain ⟨Φ, hsmooth, hflow, hderivative⟩ := hselected Ω hΩ X hX hstep x₀ hRΩ hjets hmax B
  have hUK : ball x₀ (R / 4) ⊆ closedBall x₀ R :=
    (ball_subset_ball (by linarith)).trans ball_subset_closedBall
  have hclosed : ∀ a ∈ ball 0 δ, ∀ x ∈ ball x₀ (R / 4), Φ ((a, x), 0) = x ∧
      ∀ τ ∈ Ioo (-2 : ℝ) 2, Φ ((a, x), τ) ∈ closedBall x₀ R ∧
        HasDerivAt (fun v => Φ ((a, x), v))
          (∑ j, a j • shortField w X (selectedAuxiliaryIndex w B j) (Φ ((a, x), τ))) τ := by
    intro a ha x hx
    exact ⟨(hflow a ha x hx).1, fun τ hτ =>
      ⟨ball_subset_closedBall ((hflow a ha x hx).2 τ hτ).1, ((hflow a ha x hx).2 τ hτ).2⟩⟩
  refine ⟨Φ, hsmooth, hflow, ?_⟩
  intro x hx r hr hr1 hB u v ha
  have has : ∀ j, |Fin.append u v j| ≤
      (es * r) ^ (shortWeight w (selectedAuxiliaryIndex w B j) : ℕ) := fun j =>
    (ha j).trans (pow_le_pow_left₀ (mul_nonneg he.le hr.le)
      (mul_le_mul_of_nonneg_right hees hr.le) _)
  have hap : ∀ j, |Fin.append u v j| ≤
      (ep * r) ^ (shortWeight w (selectedAuxiliaryIndex w B j) : ℕ) := fun j =>
    (ha j).trans (pow_le_pow_left₀ (mul_nonneg he.le hr.le)
      (mul_le_mul_of_nonneg_right heep hr.le) _)
  obtain ⟨hhalf, hcoords⟩ := hderivative x hx r hr hr1 hB u v has
  obtain ⟨_, hdet⟩ := hother Ω (closedBall x₀ R) hΩ hRΩ X hX hstep
    (fun j => (hjets j).mono (by omega)) hmax (selectedAuxiliaryIndex w B)
    (ball x₀ (R / 4)) hUK Φ hsmooth hclosed B x
    (ball_subset_ball (by linarith) hx) r hr hr1 hB (Fin.append u v) hap
  exact ⟨hhalf, hdet, hcoords⟩

end RothschildStein.G4
