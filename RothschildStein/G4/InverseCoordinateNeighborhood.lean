-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.ActualInverseNeighborhood
public import RothschildStein.G4.ActualLocalInverseFrameDerivative

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology

namespace RothschildStein.G4

/-- Actual Jacobian and Cramer-error bounds on a coefficient box
produce an inverse neighborhood with the weighted frame-direction bound
at every point of its target (BB Prop 9.52, (9.51), p. 448). -/
theorem exists_inverse_coordinate_neighborhood {ι : Type*} {n : ℕ}
    (Z : ι → (Fin n → ℝ) → (Fin n → ℝ)) (w : ι → ℕ+) (B : Fin n → ι)
    {Q : Set (Fin n → ℝ)} (hQ : IsOpen Q)
    (F : (Fin n → ℝ) → (Fin n → ℝ))
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F Q)
    (hjac : ∀ u ∈ Q, Matrix.det (coordinateDerivativeMatrix (fderiv ℝ F u)) ≠ 0)
    (hdet : ∀ u ∈ Q, frameDet Z B (F u) ≠ 0)
    {r κ : ℝ} (hr : 0 < r) (hκ : 0 ≤ κ) (hsmall : (n : ℝ) * κ ≤ 1 / 4)
    (herror : ∀ u ∈ Q, ∀ i j, |frameCoefficient Z B
      (fun z => fderiv ℝ F u (Pi.single j 1) - Z (B j) z) i (F u)| ≤
        κ * r ^ (((w (B i) : ℕ) : ℤ) - ((w (B j) : ℕ) : ℤ)))
    {u : Fin n → ℝ} (hu : u ∈ Q) :
    ∃ Ψ : (Fin n → ℝ) → (Fin n → ℝ), ∃ V : Set (Fin n → ℝ),
      IsOpen V ∧ F u ∈ V ∧ ContDiffOn ℝ 1 Ψ V ∧ Ψ (F u) = u ∧
      MapsTo Ψ V Q ∧ EqOn (F ∘ Ψ) id V ∧
      ((fun a => Ψ (F a)) =ᶠ[𝓝 u] (fun a => a)) ∧
      ∀ y ∈ V, ∀ i j, |fderiv ℝ Ψ y (Z (B j) y) i| ≤ (4 / 3 : ℝ) *
        r ^ (((w (B i) : ℕ) : ℤ) - ((w (B j) : ℕ) : ℤ)) := by
  obtain ⟨Ψ, V, hV, hmem, hΨ, hpoint, hmap, hright, hleft⟩ :=
    exists_actual_inverse_neighborhood hQ F hu (hF.contDiffAt (hQ.mem_nhds hu)) (hjac u hu)
  refine ⟨Ψ, V, hV, hmem, hΨ, hpoint, hmap, hright, hleft, ?_⟩
  intro y hy i j
  have hFy : F (Ψ y) = y := hright hy
  have hrightAt : (fun z => F (Ψ z)) =ᶠ[𝓝 y] (fun z => z) :=
    Filter.mem_of_superset (hV.mem_nhds hy) (fun z hz => hright hz)
  have hdetAt : frameDet Z B y ≠ 0 := by
    simpa only [hFy] using hdet (Ψ y) (hmap hy)
  have herrorAt : ∀ i j, |frameCoefficient Z B
      (fun z => fderiv ℝ F (Ψ y) (Pi.single j 1) - Z (B j) z) i y| ≤
        κ * r ^ (((w (B i) : ℕ) : ℤ) - ((w (B j) : ℕ) : ℤ)) := by
    simpa only [hFy] using herror (Ψ y) (hmap hy)
  exact local_inverse_frame_derivative_bound Z w B F Ψ rfl
    ((hF.contDiffAt (hQ.mem_nhds (hmap hy))).differentiableAt (by simp))
    ((hΨ.contDiffAt (hV.mem_nhds hy)).differentiableAt (by simp))
    hrightAt hdetAt hr hκ hsmall herrorAt j i

end RothschildStein.G4
