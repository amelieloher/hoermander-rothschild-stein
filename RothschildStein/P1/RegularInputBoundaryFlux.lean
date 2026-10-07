-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.SmoothInputBoundaryLimit
public import RothschildStein.P1.StandardFrame

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace RothschildStein.P1.LiftedChart
variable {n k m q : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {F : KernelFrame (n + m)}
  {H : H1.StandingHypotheses C.G q} {K : H1.FundamentalKernel C.G H}
  {hQ : 2 < (C.G.homogeneousDimension : ℝ)}

/-- The actual regular component of a type
kernel has zero prescribed radial input boundary flux. -/
theorem tendsto_regularInput_boundary_flux (hF : C.IsStandardFrame F H K hQ)
    {r : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ}
    (hr : IsRegularKernel F 1 r) (i : Fin k)
    {ξ : Fin (n + m) → ℝ} (hξ : ξ ∈ (F.V : Set (Fin (n + m) → ℝ)))
    (φ : TestFunction F.V ℝ (⊤ : ℕ∞)) :
    Tendsto (fun ε : ℝ => ∫ η, -(fieldDerivative (C.Xl i)
      (fun ζ => 1 - radialCutoffProfile (H.norm (C.G.dilate ε⁻¹ (C.Θ ζ ξ)))) η) * r ξ η * φ η)
      (𝓝[>] (0 : ℝ)) (𝓝 0) :=
  C.tendsto_smoothInput_boundary_flux hF.lifted i hξ H.norm.gauge hF.norm_smooth
    (r ξ) (hr.1.comp (contDiff_const.prodMk contDiff_id)).contDiffOn φ

end RothschildStein.P1.LiftedChart
