-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.UniformSharpRows
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace RothschildStein.P1
variable {N : ℕ} {L : Set (Fin N → ℝ)}
  {ρ f : (Fin N → ℝ) → (Fin N → ℝ) → ℝ}

/-- Uniform sharp errors supply the outer
integrable majorant needed to pass a tested identity to the limit. -/
theorem UniformSharpRows.tendsto_tested_integral (D : UniformSharpRows L ρ f)
    (g : (Fin N → ℝ) → ℝ) (hs : Function.support g ⊆ L)
    (hg : Integrable g) (hv : Integrable (fun ξ => g ξ * D.value ξ))
    (hm : ∀ ε : ℝ, 0 < ε → AEStronglyMeasurable (fun ξ =>
      g ξ * (∫ η in {η | ε < ρ ξ η}, f ξ η)) volume) :
    Tendsto (fun ε : ℝ => ∫ ξ, g ξ * (∫ η in {η | ε < ρ ξ η}, f ξ η))
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ ξ, g ξ * D.value ξ)) := by
  obtain ⟨r, A, hr, hA, hb⟩ := D.error
  let b := fun ξ => ‖g ξ * D.value ξ‖ + A * ‖g ξ‖
  apply tendsto_integral_filter_of_dominated_convergence b
  · filter_upwards [self_mem_nhdsWithin] with ε hε
    exact hm ε hε
  · have her : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), ε < min r 1 :=
      (eventually_lt_nhds (lt_min hr zero_lt_one)).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, her] with ε hε hεr
    apply Eventually.of_forall
    intro ξ
    by_cases hz : g ξ = 0
    · simp only [hz, zero_mul, norm_zero, b, mul_zero, add_zero, le_refl]
    · have hξ := hs hz
      have he := hb ξ hξ ε hε (hεr.trans_le (min_le_left _ _))
      have heA : ‖(∫ η in {η | ε < ρ ξ η}, f ξ η) - D.value ξ‖ ≤ A :=
        he.trans (mul_le_of_le_one_right hA (hεr.trans_le (min_le_right _ _)).le)
      have heRow : ‖∫ η in {η | ε < ρ ξ η}, f ξ η‖ ≤ ‖D.value ξ‖ + A := by
        have ht := norm_add_le ((∫ η in {η | ε < ρ ξ η}, f ξ η) - D.value ξ) (D.value ξ)
        simp only [sub_add_cancel] at ht
        linarith
      dsimp only [b]
      rw [norm_mul, norm_mul]
      calc
        _ ≤ ‖g ξ‖ * (‖D.value ξ‖ + A) := mul_le_mul_of_nonneg_left heRow (norm_nonneg _)
        _ = ‖g ξ‖ * ‖D.value ξ‖ + A * ‖g ξ‖ := by ring
  · exact hv.norm.add (hg.norm.const_mul A)
  · apply Eventually.of_forall
    intro ξ
    by_cases hz : g ξ = 0
    · simp only [hz, zero_mul]
      exact tendsto_const_nhds
    · exact (D.limit ξ (hs hz)).const_mul (g ξ)

end RothschildStein.P1
