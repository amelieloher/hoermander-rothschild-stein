-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.MappedFramePersistence
public import RothschildStein.G4.WeightedCoefficientBounds

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
open scoped BigOperators

namespace RothschildStein.G4

/-- The ACTUAL mapped-family unit-time flow satisfies selected and
other-frame persistence throughout one weighted coefficient domain.
The radius is chosen before the original sets, fields, frame and flow
(BB Lemma 9.49, p. 444; persistence adapter). -/
theorem exists_uniform_mapped_flow_frame_persistence (k n s m : ℕ) (δ : ℝ) (hδ : 0 < δ) (hn : 0 < n) (hs : 0 < s)
    (w : Fin (k + 1) → ℕ+) (M Δ : ℝ) (hM : 0 ≤ M) (hΔ : 0 < Δ) :
    ∃ D : ℝ, 0 < D ∧ ∀ t : ℝ, 0 < t → t ≤ 1 →
      ∃ e : ℝ, 0 < e ∧ e ≤ 1 ∧ e ≤ t ∧ e < δ ∧
      ∀ (Ω K : Set (Fin n → ℝ)), IsOpen Ω → K ⊆ Ω →
      ∀ (X : Fin (k + 1) → (Fin n → ℝ) → (Fin n → ℝ)),
      (∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω) → bracketStepOn Ω w X s →
      (∀ i, HasJetBound Ω K (X i) (2 * (n * s) + 2 * s) M) →
      (∀ x ∈ K, ∃ C : Fin n → ShortWord w s, Δ ≤ |frameDet (shortField w X) C x|) →
      ∀ I : Fin m → ShortWord w s,
      ∀ (U : Set (Fin n → ℝ)), U ⊆ K →
      ∀ Φ : (((Fin m → ℝ) × (Fin n → ℝ)) × ℝ) → (Fin n → ℝ),
      ContDiffOn ℝ (⊤ : ℕ∞) Φ ((ball 0 δ ×ˢ U) ×ˢ Ioo (-2) 2) →
      (∀ a ∈ ball 0 δ, ∀ x ∈ U, Φ ((a, x), 0) = x ∧ ∀ τ ∈ Ioo (-2) 2,
        Φ ((a, x), τ) ∈ K ∧ HasDerivAt (fun v => Φ ((a, x), v))
          (∑ u, a u • shortField w X (I u) (Φ ((a, x), τ))) τ) →
      ∀ (B : Fin n → ShortWord w s) x, x ∈ U → ∀ r : ℝ, 0 < r → r ≤ 1 →
      IsSuboptimal (shortField w X) (shortWeight w) B x t r →
      ∀ a : Fin m → ℝ, (∀ u, |a u| ≤ (e * r) ^ (shortWeight w (I u) : ℕ)) →
      |frameDet (shortField w X) B (Φ ((a, x), 1)) - frameDet (shortField w X) B x| ≤
        |frameDet (shortField w X) B x| / 2 ∧
      ∀ C : Fin n → ShortWord w s, |frameDet (shortField w X) C (Φ ((a, x), 1))| ≤ D * t⁻¹ ^ n *
        r ^ (frameWeight (shortWeight w) B - frameWeight (shortWeight w) C) *
          |frameDet (shortField w X) B x| := by
  obtain ⟨D, hD, hpersist⟩ := exists_uniform_mapped_frame_persistence (ι := Fin m)
    k n s hn hs w M Δ hM hΔ
  refine ⟨D, hD, ?_⟩
  intro t ht ht1
  obtain ⟨e₀, he₀, he₀1, he₀t, hmain⟩ := hpersist t ht ht1
  let e := min e₀ (δ / 2)
  have he : 0 < e := lt_min he₀ (by positivity)
  have hee₀ : e ≤ e₀ := min_le_left _ _
  have heδ : e < δ := (min_le_right e₀ (δ / 2)).trans_lt (half_lt_self hδ)
  refine ⟨e, he, hee₀.trans he₀1, hee₀.trans he₀t, heδ, ?_⟩
  intro Ω K hΩ hKΩ X hX hstep hjets hmax I U hUK Φ hΦsmooth hΦ B x hx r hr hr1 hB a ha
  have he1 : e ≤ 1 := hee₀.trans he₀1
  have her1 : e * r ≤ 1 := (mul_le_mul_of_nonneg_right he1 hr.le).trans (by simpa using hr1)
  have hanorm := weighted_coefficients_norm_le (fun u => shortWeight w (I u))
    (mul_nonneg he.le hr.le) her1 ha
  have haa : a ∈ ball 0 δ := by
    rw [mem_ball, dist_zero_right]
    exact (hanorm.trans (mul_le_of_le_one_right he.le hr1)).trans_lt heδ
  have ha₀ : ∀ u, |a u| ≤ (e₀ * r) ^ (shortWeight w (I u) : ℕ) := fun u =>
    (ha u).trans (pow_le_pow_left₀ (mul_nonneg he.le hr.le)
      (mul_le_mul_of_nonneg_right hee₀ hr.le) _)
  have hseg : ∀ τ ∈ Icc (0 : ℝ) 1, τ ∈ Ioo (-2 : ℝ) 2 := by
    intro τ hτ; constructor <;> linarith [hτ.1, hτ.2]
  have hγsmooth : ContDiffOn ℝ (⊤ : ℕ∞) (fun τ => Φ ((a, x), τ)) (Icc 0 1) :=
    hΦsmooth.comp (contDiffOn_const.prodMk contDiffOn_id)
      (fun τ hτ => ⟨⟨haa, hx⟩, hseg τ hτ⟩)
  exact hmain Ω K hΩ hKΩ X hX hstep hjets hmax I B x (hUK hx) r hr hr1 hB a ha₀
    (fun τ => Φ ((a, x), τ)) (hΦ a haa x hx).1 hγsmooth
    (fun τ hτ => ((hΦ a haa x hx).2 τ (hseg τ hτ)).1)
    (fun τ hτ => ((hΦ a haa x hx).2 τ (hseg τ hτ)).2)

end RothschildStein.G4
