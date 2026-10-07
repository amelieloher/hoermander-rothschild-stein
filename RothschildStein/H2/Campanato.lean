-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.H2.CampanatoFar
public import RothschildStein.H2.CampanatoAE
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal
namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]

/-- Campanato's theorem on a doubling patch gives explicit local and far estimates and a uniform absolute bound (BB Theorem 7.38, pp. 327–331). The estimates use centers in S, where the minima are attained. -/
theorem DoublingPatch.campanato_theorem (P : DoublingPatch X) {α : ℝ}
    (hα : 0 < α) (hα₁ : α < 1) {u : X → ℝ} (hu : MemCampanato α P u) :
    BoundedHolder ⟨α, hα.le⟩ P.S (campanatoRepresentative P α u) ∧
    (∀ᵐ x ∂P.μ, x ∈ P.S → campanatoRepresentative P α u x = u x) ∧
    (∀ x ∈ P.S, ∀ y ∈ P.S, dist x y ≤ 3 * P.ρ →
      |campanatoRepresentative P α u x - campanatoRepresentative P α u y| ≤
        4 * (campanatoTailConstant P α + P.C_D) * (campanatoSeminorm α P u).toReal * dist x y ^ α) ∧
    (∀ x ∈ P.S, ∀ y ∈ P.S, 3 * P.ρ < dist x y →
      |campanatoRepresentative P α u x - campanatoRepresentative P α u y| ≤
        campanatoFarConstant P α * ((campanatoSeminorm α P u).toReal +
          (∫ z in P.W, |u z| ∂P.μ)) * dist x y ^ α) ∧
    (∀ x ∈ P.S, |campanatoRepresentative P α u x| ≤
      (1 + campanatoTailConstant P α) * (6 * P.ρ) ^ α * (campanatoSeminorm α P u).toReal +
        (∫ z in P.W, |u z| ∂P.μ) / campanatoMinVolume P) := by
  refine ⟨?_, campanatoRepresentative_ae_eq P hα hu,
    fun x hx y hy => campanatoRepresentative_near P hα hα₁.le hu hx hy,
    fun x hx y hy => campanatoRepresentative_far P hα hu hx hy,
    fun x hx => campanatoRepresentative_uniform_abs P hα hu hx⟩
  obtain ⟨B, hB⟩ := campanatoRepresentative_bounded P hα hu
  let H := max (4 * (campanatoTailConstant P α + P.C_D) * (campanatoSeminorm α P u).toReal)
    (campanatoFarConstant P α * ((campanatoSeminorm α P u).toReal + (∫ z in P.W, |u z| ∂P.μ)))
  have hN : 0 ≤ 4 * (campanatoTailConstant P α + P.C_D) * (campanatoSeminorm α P u).toReal :=
    mul_nonneg (by linarith [campanatoTailConstant_pos P hα, P.one_lt_C_D]) ENNReal.toReal_nonneg
  have hH : 0 ≤ H := hN.trans (le_max_left _ _)
  have hb : holderSemi ⟨α, hα.le⟩ P.S (campanatoRepresentative P α u) ≤ ENNReal.ofReal H := by
    apply holderSemi_le_of_bound hH
    intro x hx y hy
    by_cases hxy : dist x y ≤ 3 * P.ρ
    · exact (campanatoRepresentative_near P hα hα₁.le hu hx hy hxy).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg dist_nonneg α))
    · exact (campanatoRepresentative_far P hα hu hx hy (lt_of_not_ge hxy)).trans
        (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg dist_nonneg α))
  have hs := holderSup_le_of_bound hB
  exact (add_le_add hs hb).trans_lt (ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩)
end RothschildStein.H2
