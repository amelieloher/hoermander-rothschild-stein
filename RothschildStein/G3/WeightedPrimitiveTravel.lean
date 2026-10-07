-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.ActualQuasiExponentialPoints
public import RothschildStein.G3.SignedPrimitiveCoordinates
public import RothschildStein.G3.PrimitiveFlowDisplacement
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
namespace RothschildStein.G3

/-- Every signed weighted primitive arc obeys the same scalar travel budget. -/
theorem norm_weightedPrimitiveArc_displacement_le {a N : ℕ} (p : Fin a → ℕ+)
    (Ψ : Fin a → ((Fin N → ℝ) × ℝ) → (Fin N → ℝ))
    (X : Fin a → (Fin N → ℝ) → (Fin N → ℝ)) {Ω : Set (Fin N → ℝ)}
    {κ B t : ℝ} (hκ : 0 < κ) (hB : 0 ≤ B) (htκ : |t| < κ) (ht1 : |t| ≤ 1)
    (b : Fin a × Bool) (x : Fin N → ℝ) (hzero : Ψ b.1 (x,0) = x)
    (hODE : ∀ v ∈ Ioo (-κ) κ, Ψ b.1 (x,v) ∈ Ω ∧
      HasDerivAt (fun w => Ψ b.1 (x,w)) (X b.1 (Ψ b.1 (x,v))) v)
    (hbound : ∀ y ∈ Ω, ‖X b.1 y‖ ≤ B) :
    ‖weightedPrimitiveArc p Ψ b (t,x)-x‖ ≤ B*|t| := by
  have ht : signedPrimitiveTime p b t ∈ Ioo (-κ) κ :=
    abs_lt.mp ((signedPrimitiveTime_abs_le p b ht1).trans_lt htκ)
  have he := primitiveFlow_displacement_le hκ (Ψ b.1) x hzero
    (fun v hv => ⟨(hODE v hv).2,(hODE v hv).1⟩) hbound ht
  change ‖Ψ b.1 (x,signedPrimitiveTime p b t)-x‖ ≤ B*|t|
  exact he.trans (mul_le_mul_of_nonneg_left (signedPrimitiveTime_abs_le p b ht1) hB)
end RothschildStein.G3
