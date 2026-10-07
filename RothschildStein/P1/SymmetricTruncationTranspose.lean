-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.BilinearTranspose

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory
namespace RothschildStein.P1

/-- The same symmetric gauge truncation is used by the
operator and its bilinear transpose (BB Proposition 11.14,
pp. 545–546). No assertion of gauge-independent principal values is made. -/
theorem integral_symmetricTruncation_bilinearTranspose {E : Type*} [MeasurableSpace E]
    (μ : Measure E) [SFinite μ] (ρ K : E → E → ℝ)
    (hρ : ∀ x y, ρ x y = ρ y x) (ε : ℝ) (f g : E → ℝ)
    (hi : Integrable (fun p : E × E =>
      g p.1 * ((if ε < ρ p.1 p.2 then K p.1 p.2 else 0) * f p.2)) (μ.prod μ)) :
    (∫ x, g x * (∫ y, (if ε < ρ x y then K x y else 0) * f y ∂μ) ∂μ) =
      ∫ y, f y * (∫ x, (if ε < ρ y x then K x y else 0) * g x ∂μ) ∂μ := by
  calc
    _ = ∫ y, f y * (∫ x, (if ε < ρ x y then K x y else 0) * g x ∂μ) ∂μ :=
      integral_kernel_bilinearTranspose μ μ (fun x y => if ε < ρ x y then K x y else 0)
        f g hi
    _ = _ := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro y
      change f y * (∫ x, (if ε < ρ x y then K x y else 0) * g x ∂μ) =
        f y * (∫ x, (if ε < ρ y x then K x y else 0) * g x ∂μ)
      congr 1
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun x => by
        change (if ε < ρ x y then K x y else 0) * g x =
          (if ε < ρ y x then K x y else 0) * g x
        rw [hρ x y])

end RothschildStein.P1
