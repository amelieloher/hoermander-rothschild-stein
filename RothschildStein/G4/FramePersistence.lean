-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.OtherFramePersistence

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators

namespace RothschildStein.G4

/-- Both persistence conclusions share one numerical radius.
The other-determinant constant is chosen before t; the radius is chosen
before actual fields and flows. The two pinned Taylor orders are retained. -/
theorem exists_uniform_frame_persistence (k n s : ℕ) (hn : 0 < n) (hs : 0 < s)
    (w : Fin (k + 1) → ℕ+) (M Δ : ℝ) (hM : 0 ≤ M) (hΔ : 0 < Δ) :
    ∃ D : ℝ, 0 < D ∧ ∀ t : ℝ, 0 < t → t ≤ 1 →
      ∃ e : ℝ, 0 < e ∧ e ≤ 1 ∧ e ≤ t ∧
      ∀ (Ω K : Set (Fin n → ℝ)), IsOpen Ω → K ⊆ Ω →
      ∀ (X : Fin (k + 1) → (Fin n → ℝ) → (Fin n → ℝ)),
      (∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω) → bracketStepOn Ω w X s →
      (∀ i, HasJetBound Ω K (X i) (2 * (n * s) + 2 * s) M) →
      (∀ x ∈ K, ∃ C : Fin n → ShortWord w s, Δ ≤ |frameDet (shortField w X) C x|) →
      ∀ (B : Fin n → ShortWord w s) x, x ∈ K → ∀ r : ℝ, 0 < r → r ≤ 1 →
      IsSuboptimal (shortField w X) (shortWeight w) B x t r →
      ∀ a : ShortWord w s → ℝ, (∀ I, |a I| ≤ (e * r) ^ (shortWeight w I : ℕ)) →
      ∀ γ : ℝ → (Fin n → ℝ), γ 0 = x → ContDiffOn ℝ (⊤ : ℕ∞) γ (Icc 0 1) →
      MapsTo γ (Icc 0 1) K →
      (∀ τ ∈ Icc 0 1, HasDerivAt γ (∑ I, a I • shortField w X I (γ τ)) τ) →
      |frameDet (shortField w X) B (γ 1) - frameDet (shortField w X) B x| ≤
        |frameDet (shortField w X) B x| / 2 ∧
      ∀ C : Fin n → ShortWord w s, |frameDet (shortField w X) C (γ 1)| ≤ D * t⁻¹ ^ n *
        r ^ (frameWeight (shortWeight w) B - frameWeight (shortWeight w) C) *
          |frameDet (shortField w X) B x| := by
  obtain ⟨D, hD, hother⟩ := exists_other_frame_persistence_bound k n s hn hs w M Δ hM hΔ
  refine ⟨D, hD, ?_⟩
  intro t ht ht1
  obtain ⟨e, he, he1, het, hselected⟩ := exists_selected_frame_persistence_radius k n s hn hs w M Δ t hM hΔ ht ht1
  refine ⟨e, he, he1, het, ?_⟩
  intro Ω K hΩ hKΩ X hX hstep hjets hmax B x hx r hr hr1 hB a ha γ hinit hγs hmap hγ
  constructor
  · exact hselected Ω K hΩ hKΩ X hX hstep (fun i => (hjets i).mono (by omega))
      hmax B x hx r hr hr1 hB a ha γ hinit hγs hmap hγ
  · intro C
    exact hother t ht ht1 Ω K hΩ hKΩ X hX hstep hjets hmax B C x hx r hr hr1 hB
      e he.le he1 het a ha γ hinit hγs hmap hγ

end RothschildStein.G4
