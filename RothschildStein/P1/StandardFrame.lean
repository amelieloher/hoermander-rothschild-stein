-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.ContinuityPositive
public import RothschildStein.H1.KernelAssembly
public import RothschildStein.H1.KernelReflection

/-!
# The standard kernel frame for a lifted chart

The kernel integrability, endpoint differentiation, transfer and parametrix statements are stated
for an arbitrary `KernelFrame`. This file defines the class of frames built from a lifted chart,
its model hypotheses and its fundamental kernels, so those results can share one set of assumptions.
An arbitrary frame may have a zero gauge, in which case endpoint type bounds need not hold.

`H` is intended to be the chart's model `C.driftModel hq ν` (drift alphabet) or
`C.noDriftModel hq ν` (no drift), see `RothschildStein.P1.ModelHypotheses`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
namespace RothschildStein.P1

namespace LiftedChart

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}

/-- The standard frame of a lifted chart: the frame lives on the
chart (`IsLiftedFrame`), its poles are an H1 fundamental kernel `Γ` of the model and its
reflection `Γ*(u) = Γ(u⁻¹)` (BB Thm 11.5(e)), its truncation gauge is the model's smooth
symmetric homogeneous norm, and `Γ` has all the properties of BB Thm 11.5 (BB pp. 538–539, 543–545). -/
structure IsStandardFrame (C : LiftedChart w s Ω hΩ X x₀ m) (F : KernelFrame (n + m))
    {q : ℕ} (H : H1.StandingHypotheses C.G q) (K : H1.FundamentalKernel C.G H)
    (hQ : 2 < (C.G.homogeneousDimension : ℝ)) : Prop where
  lifted : C.IsLiftedFrame F
  Γ_eq : F.Γ = K
  Γs_eq : F.Γs = K.reflection hQ
  gauge_eq : F.gauge = H.norm
  norm_symm : ∀ u, H.norm (-u) = H.norm u
  norm_smooth : H.norm.Smooth
  kernel_props : H1.FundamentalKernelProperties K

end LiftedChart

end RothschildStein.P1
