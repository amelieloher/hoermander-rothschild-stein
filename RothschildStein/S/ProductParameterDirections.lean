-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.ProductSectionDerivative

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Function
namespace RothschildStein.S
variable {n : ℕ}

/-- An x-direction derivative of a kernel section with ε
fixed is exactly its joint derivative with y,ε held fixed (BB pp. 76–78). -/
theorem fderiv_xyParameter_first_apply
    {f : ((Fin n → ℝ) × (Fin n → ℝ)) × ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (ε : ℝ) (x y v : Fin n → ℝ) :
    fderiv ℝ (fun x => f ((x,y),ε)) x v =
      fderiv ℝ f ((x,y),ε) ((v,0),0) := by
  have hε : ContDiff ℝ (⊤ : ℕ∞) (fun p => f (p,ε)) :=
    hf.comp (contDiff_id.prodMk contDiff_const)
  rw [fderiv_productSection_first_apply hε x y v]
  exact fderiv_productSection_first_apply hf (x,y) ε (v,0)

/-- A y-direction derivative of a kernel section with ε
fixed is exactly its joint derivative with x,ε held fixed (BB pp. 76–78). -/
theorem fderiv_xyParameter_second_apply
    {f : ((Fin n → ℝ) × (Fin n → ℝ)) × ℝ → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (ε : ℝ) (x y v : Fin n → ℝ) :
    fderiv ℝ (fun y => f ((x,y),ε)) y v =
      fderiv ℝ f ((x,y),ε) ((0,v),0) := by
  have hε : ContDiff ℝ (⊤ : ℕ∞) (fun p => f (p,ε)) :=
    hf.comp (contDiff_id.prodMk contDiff_const)
  rw [fderiv_productSection_second_apply hε x y v]
  exact fderiv_productSection_first_apply hf (x,y) ε (0,v)

end RothschildStein.S
