-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.FramePersistence
public import RothschildStein.G4.MappedControlAggregation

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators

namespace RothschildStein.G4

/-- Persistence for a mapped short-field control family, including
repeated selected and auxiliary fields, uses one numerical radius.
The other-determinant constant is chosen before t; the radius is chosen
before actual fields and flows. The two pinned Taylor orders are retained. -/
theorem exists_uniform_mapped_frame_persistence {ι : Type*} [Fintype ι] (k n s : ℕ) (hn : 0 < n) (hs : 0 < s)
    (w : Fin (k + 1) → ℕ+) (M Δ : ℝ) (hM : 0 ≤ M) (hΔ : 0 < Δ) :
    ∃ D : ℝ, 0 < D ∧ ∀ t : ℝ, 0 < t → t ≤ 1 →
      ∃ e : ℝ, 0 < e ∧ e ≤ 1 ∧ e ≤ t ∧
      ∀ (Ω K : Set (Fin n → ℝ)), IsOpen Ω → K ⊆ Ω →
      ∀ (X : Fin (k + 1) → (Fin n → ℝ) → (Fin n → ℝ)),
      (∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω) → bracketStepOn Ω w X s →
      (∀ i, HasJetBound Ω K (X i) (2 * (n * s) + 2 * s) M) →
      (∀ x ∈ K, ∃ C : Fin n → ShortWord w s, Δ ≤ |frameDet (shortField w X) C x|) →
      ∀ I : ι → ShortWord w s, ∀ (B : Fin n → ShortWord w s) x, x ∈ K → ∀ r : ℝ, 0 < r → r ≤ 1 →
      IsSuboptimal (shortField w X) (shortWeight w) B x t r →
      ∀ a : ι → ℝ, (∀ u, |a u| ≤ (e * r) ^ (shortWeight w (I u) : ℕ)) →
      ∀ γ : ℝ → (Fin n → ℝ), γ 0 = x → ContDiffOn ℝ (⊤ : ℕ∞) γ (Icc 0 1) →
      MapsTo γ (Icc 0 1) K →
      (∀ τ ∈ Icc 0 1, HasDerivAt γ (∑ u, a u • shortField w X (I u) (γ τ)) τ) →
      |frameDet (shortField w X) B (γ 1) - frameDet (shortField w X) B x| ≤
        |frameDet (shortField w X) B x| / 2 ∧
      ∀ C : Fin n → ShortWord w s, |frameDet (shortField w X) C (γ 1)| ≤ D * t⁻¹ ^ n *
        r ^ (frameWeight (shortWeight w) B - frameWeight (shortWeight w) C) *
          |frameDet (shortField w X) B x| := by
  classical
  obtain ⟨D, hD, hpersist⟩ := exists_uniform_frame_persistence k n s hn hs w M Δ hM hΔ
  refine ⟨D, hD, ?_⟩
  intro t ht ht1
  obtain ⟨e₀, he₀, he₀1, he₀t, hmain⟩ := hpersist t ht ht1
  let C := (Fintype.card ι : ℝ) + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hC1 : 1 ≤ C := by
    dsimp [C]
    have hn := Nat.cast_nonneg (α := ℝ) (Fintype.card ι)
    linarith
  let e := e₀ / C
  have he : 0 < e := div_pos he₀ hC
  have he₀le : e ≤ e₀ := (div_le_iff₀ hC).mpr (by nlinarith)
  refine ⟨e, he, he₀le.trans he₀1, he₀le.trans he₀t, ?_⟩
  intro Ω K hΩ hKΩ X hX hstep hjets hmax I B x hx r hr hr1 hB a ha γ hinit hγs hmap hγ
  have heq : C * e = e₀ := by dsimp [e]; field_simp
  have hagg : ∀ J : ShortWord w s,
      |aggregateMappedControls I a J| ≤ (e₀ * r) ^ (shortWeight w J : ℕ) := by
    intro J
    have hb := aggregateMappedControls_weighted_bound I a (shortWeight w) he.le hr.le ha J
    change |aggregateMappedControls I a J| ≤ (C * e * r) ^ (shortWeight w J : ℕ) at hb
    rw [heq] at hb
    exact hb
  apply hmain Ω K hΩ hKΩ X hX hstep hjets hmax B x hx r hr hr1 hB
    (aggregateMappedControls I a) hagg γ hinit hγs hmap
  intro τ hτ
  rw [aggregateMappedControls_field_eq]
  exact hγ τ hτ

end RothschildStein.G4
