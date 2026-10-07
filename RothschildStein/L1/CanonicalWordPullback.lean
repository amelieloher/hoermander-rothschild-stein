-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.JointPullbackFields
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric Filter
open scoped Topology
namespace RothschildStein.L1
namespace CanonicalFrameChartData
variable {N a : ℕ} {Ω : Set (Fin N → ℝ)}
variable {Y : Fin N → (Fin N → ℝ) → (Fin N → ℝ)} {x : Fin N → ℝ}

/-- Actual pullback respects every nested commutator word throughout the
coefficient patch. No high-weight vanishing assertion is required. -/
theorem pullbackField_wordBracket (D : CanonicalFrameChartData Ω Y x) (hΩ : IsOpen Ω)
    (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (η : Fin N → ℝ) (hη : η ∈ ball x D.radius) (I : List (Fin a)) :
    ∀ u ∈ ball 0 D.radius,
    D.pullbackField η (wordBracket X I) u = wordBracket (fun i => D.pullbackField η (X i)) I u := by
  induction I with
  | nil => intro u hu; simp only [wordBracket, pullbackField, Pi.zero_apply, map_zero]
  | cons i I ih =>
    cases I with
    | nil => intro u hu; rfl
    | cons j I =>
      intro u hu
      have hcoef := D.coefficients (η,u) ⟨hη,hu⟩
      have hξ := D.forward_mem (q := (η,u)) ⟨hη,hu⟩
      have htail := G1.wordBracket_contDiffOn hΩ X hX (j :: I)
      have hb := D.pullbackField_lieBracket η (canonicalFrameMap D.time D.flow (η,u))
        hcoef.2.1 (X i) (wordBracket X (j :: I))
        ((hX i).contDiffAt (hΩ.mem_nhds hξ)) (htail.contDiffAt (hΩ.mem_nhds hξ))
      rw [hcoef.2.2] at hb
      have he : D.pullbackField η (wordBracket X (j :: I)) =ᶠ[𝓝 u]
          wordBracket (fun i => D.pullbackField η (X i)) (j :: I) :=
        Filter.Eventually.mono (isOpen_ball.mem_nhds hu) (fun v hv => ih v hv)
      change D.pullbackField η (VectorField.lieBracket ℝ (X i) (wordBracket X (j :: I))) u =
        VectorField.lieBracket ℝ (D.pullbackField η (X i))
          (wordBracket (fun i => D.pullbackField η (X i)) (j :: I)) u
      rw [hb]
      simp only [VectorField.lieBracket]
      rw [he.fderiv_eq, he.self_of_nhds]

/-- Actual canonical commutator coefficients are jointly smooth in the
base point and the canonical coordinate, for every word. -/
theorem pulled_wordBracket_contDiffOn_joint (D : CanonicalFrameChartData Ω Y x) (hΩ : IsOpen Ω)
    (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω) (I : List (Fin a)) :
    ContDiffOn ℝ (⊤ : ℕ∞)
      (fun q : (Fin N → ℝ) × (Fin N → ℝ) => wordBracket (fun i => D.pullbackField q.1 (X i)) I q.2)
      (ball x D.radius ×ˢ ball 0 D.radius) := by
  apply (D.pullbackField_contDiffOn_joint (wordBracket X I)
    (G1.wordBracket_contDiffOn hΩ X hX I)).congr
  intro q hq
  exact (D.pullbackField_wordBracket hΩ X hX q.1 hq.1 I q.2 hq.2).symm
end CanonicalFrameChartData
end RothschildStein.L1
