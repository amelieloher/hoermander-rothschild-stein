-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.UniformTriangularFrameCompletion
public import RothschildStein.L1.CoordinateApproximationData
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
namespace RothschildStein.L1.CoordinateApproximationData

/-- Every compact subset of the actual coordinate patch has
one strict positive suboptimality factor for all completed frames,
at every application scale. The empty-center case is included
(BB pp. 519–520). -/
theorem exists_uniform_completed_frame {n k s m : ℕ} {w : Fin k → ℕ+}
    {Ω : Set (Fin n → ℝ)} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)}
    {x₀ : Fin n → ℝ} {L : FixedLiftData w s Ω X x₀ m}
    {M : ModelData k s (n+m) w} (A : CoordinateApproximationData L M)
    (hΩ : IsOpen Ω) (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    {K : Set (Fin (n+m) → ℝ)} (hK : IsCompact K) (hKU : K ⊆ A.U) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ ∀ ξ ∈ K, ∀ B : Fin n → G4.ShortWord w s,
      G4.frameDet (G4.shortField w X) B (basePoint ξ) ≠ 0 →
      ∃ J : Fin m → G4.ShortWord w s,
        G4.frameDet (G4.shortField w (triangularLift X L.P)) (Fin.addCases B J) ξ ≠ 0 ∧
        ∀ r : ℝ, 0 < r → G4.IsSuboptimal (G4.shortField w (triangularLift X L.P))
          (G4.shortWeight w) (Fin.addCases B J) ξ t r := by
  classical
  by_cases hne : K.Nonempty
  · obtain ⟨ξ₀,hξ₀⟩ := hne
    have hKL : K ⊆ (L.U : Set _) := fun ξ hξ =>
      A.closure_subset_lift (subset_closure (hKU hξ))
    exact exists_uniform_triangularLift_frame_completion hΩ hK
      (hKL.trans L.subset_domain) w X hX L.P
      (fun ξ hξ => (L.free_spanning ξ (hKL hξ)).1)
      (fun ξ hξ => (L.free_spanning ξ (hKL hξ)).2) hξ₀
  · refine ⟨1/2,by norm_num,by norm_num,?_⟩
    intro ξ hξ
    exact (hne ⟨ξ,hξ⟩).elim

end RothschildStein.L1.CoordinateApproximationData
