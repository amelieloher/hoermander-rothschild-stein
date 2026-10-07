-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.DifferentialWordEvaluation
@[expose] public section
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.G3

/-- Fields agreeing on the open coefficient domain have the same
bundled differential operator on smooth representatives. -/
theorem smoothFieldOperator_eqOn {N : ℕ} (Ω : Opens (Fin N → ℝ))
    (U V : (Fin N → ℝ) → (Fin N → ℝ))
    (hU : ContDiffOn ℝ (⊤ : ℕ∞) U Ω) (hV : ContDiffOn ℝ (⊤ : ℕ∞) V Ω)
    (he : EqOn U V Ω) : smoothFieldOperator Ω U hU = smoothFieldOperator Ω V hV := by
  classical
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  funext x
  change (if x ∈ Ω then (fderiv ℝ f.val x) (U x) else 0) =
    (if x ∈ Ω then (fderiv ℝ f.val x) (V x) else 0)
  by_cases hx : x ∈ Ω
  · rw [ite_eq_left hx, ite_eq_left hx, he hx]
  · rw [ite_eq_right hx, ite_eq_right hx]

/-- Differential polynomial evaluation depends only on field values
on the open coefficient domain, even for iterated operators. -/
theorem differentialWordEvaluation_eqOn {a N : ℕ} (Ω : Opens (Fin N → ℝ))
    (X Y : Fin a → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (hY : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Y i) Ω)
    (he : ∀ i, EqOn (X i) (Y i) Ω) :
    differentialWordEvaluation Ω X hX = differentialWordEvaluation Ω Y hY := by
  have ho : (fun i => smoothFieldOperator Ω (X i) (hX i)) =
      (fun i => smoothFieldOperator Ω (Y i) (hY i)) := by
    funext i
    exact smoothFieldOperator_eqOn Ω _ _ _ _ (he i)
  unfold differentialWordEvaluation
  rw [ho]
end RothschildStein.G3
