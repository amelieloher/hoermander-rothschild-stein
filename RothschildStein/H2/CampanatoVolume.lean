-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.H2.CampanatoBounded
public import RothschildStein.H2.CampanatoNear
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal
namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- The uniform maximal-radius ball volume m₆. -/
def campanatoMinVolume (P : DoublingPatch X) : ℝ :=
  (⨅ x : P.S, P.μ (ball (x : X) (6 * P.ρ))).toReal

/-- The compact-centre volume infimum is positive when S is nonempty. -/
theorem campanatoMinVolume_pos (P : DoublingPatch X) {x : X} (hx : x ∈ P.S) :
    0 < campanatoMinVolume P := by
  have hp := P.iInf_volume_pos (show 0 < 6 * P.ρ by linarith [P.ρ_pos]) le_rfl
  have ht := (iInf_le (fun x : P.S => P.μ (ball (x : X) (6 * P.ρ))) ⟨x, hx⟩).trans_lt
    (P.doubling x hx (6 * P.ρ) (by linarith [P.ρ_pos]) le_rfl).2.1
  exact ENNReal.toReal_pos hp.ne' ht.ne

/-- Every maximal-radius volume dominates m₆. -/
theorem campanatoMinVolume_le (P : DoublingPatch X) {x : X} (hx : x ∈ P.S) :
    campanatoMinVolume P ≤ (P.μ (ball x (6 * P.ρ))).toReal := by
  exact ENNReal.toReal_mono (P.doubling x hx (6 * P.ρ) (by linarith [P.ρ_pos]) le_rfl).2.1.ne
    (iInf_le (fun x : P.S => P.μ (ball (x : X) (6 * P.ρ))) ⟨x, hx⟩)

/-- The exact uniform absolute estimate from BB Proposition 7.43. -/
theorem campanatoRepresentative_uniform_abs (P : DoublingPatch X) {α : ℝ} (hα : 0 < α)
    {u : X → ℝ} (hu : MemCampanato α P u) {x : X} (hx : x ∈ P.S) :
    |campanatoRepresentative P α u x| ≤ (1 + campanatoTailConstant P α) *
      (6 * P.ρ) ^ α * (campanatoSeminorm α P u).toReal +
      (∫ y in P.W, |u y| ∂P.μ) / campanatoMinVolume P := by
  apply (campanatoRepresentative_abs P hα hu hx).trans
  apply add_le_add le_rfl
  exact div_le_div_of_nonneg_left (integral_nonneg fun _ => abs_nonneg _)
    (campanatoMinVolume_pos P hx) (campanatoMinVolume_le P hx)
end RothschildStein.H2
