-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.L1.FreeBallVolume
public import RothschildStein.G4.CompactOrdinaryBallVolumeProvider
public import RothschildStein.G4.ControlTopology

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal BigOperators
namespace RothschildStein.L1

/-- Explicit domain restriction does not change an actual
positive-radius ordinary ball, whose endpoints already lie in the
original domain. -/
theorem ordinary_ball_inter_domain_eq {m n : ℕ}
    (Ω : Set (Fin n → ℝ)) (w : Fin m → ℕ+)
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)) (x : Fin n → ℝ) (r : ℝ) :
    {y ∈ Ω | controlDistance Ω w X x y < ENNReal.ofReal r} =
      {y | controlDistance Ω w X x y < ENNReal.ofReal r} := by
  ext y
  constructor
  · exact And.right
  · intro hy
    exact ⟨G4.controlBall_subset_domain Ω w X x r hy, hy⟩

/-- Free ordinary balls have actual compact-uniform power
volume growth from smoothness, the bracket-step hypothesis and
freeness, with no volume premise (BB Corollary 10.37, pp. 515–516). -/
theorem exists_free_ordinary_ball_volume_provider_of_local_comparison {k n s : ℕ}
    (hn : 0 < n) (hs : 1 ≤ s) {Ω K : Set (Fin n → ℝ)}
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (w : Fin (k + 1) → ℕ+)
    (D₀ : G3.FreeModelData (k+1) s w) (hweights : ∀ i, (w i : ℕ) ≤ s)
    (X : Fin (k + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (hstep : bracketStepOn Ω w X s)
    (hcomparison : G1.LocalControlComparison Ω w X s) (hFree : ∀ x ∈ K, FreeAt w s X x)
    {x₀ : Fin n → ℝ} (hx₀ : x₀ ∈ K) :
    ∃ B : Fin n → G4.ShortWord w s, G4.frameDet (G4.shortField w X) B x₀ ≠ 0 ∧
      ∃ A D r₀ : ℝ, 0 < A ∧ 0 < D ∧ 0 < r₀ ∧
        ∀ x ∈ K, ∀ r, 0 < r → r ≤ r₀ →
          ENNReal.ofReal (A * r ^ (∑ i, (G4.shortWeight w (B i) : ℕ))) ≤
            volume {y ∈ Ω | controlDistance Ω w X x y < ENNReal.ofReal r} ∧
          volume {y ∈ Ω | controlDistance Ω w X x y < ENNReal.ofReal r} ≤
            ENNReal.ofReal (D * r ^ (∑ i, (G4.shortWeight w (B i) : ℕ))) := by
  obtain ⟨B, hB⟩ := G4.exists_short_frame hstep (hKΩ hx₀)
  obtain ⟨c, C, r₀, hc, hC, hr₀, hvol⟩ :=
    G4.exists_compact_ordinary_ball_volume_provider_of_local_comparison hn hs w D₀ hweights hΩ hK hKΩ X hX hstep hcomparison
  obtain ⟨A, D, hA, hD, hpower⟩ :=
    exists_free_control_ball_volume_bounds_of_frame_volume_bounds hΩ hK hKΩ w X hX
      hFree hx₀ B hB hc hC (fun x hx r hr hrr => by
        simpa only [rsBall, ordinary_ball_inter_domain_eq] using hvol x hx r hr hrr)
  exact ⟨B, hB, A, D, r₀, hA, hD, hr₀, hpower⟩

end RothschildStein.L1
