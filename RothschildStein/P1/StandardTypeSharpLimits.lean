-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.ContinuityTheorem

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal
namespace RothschildStein.P1.LiftedChart
variable {n k m q : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {F : KernelFrame (n + m)}
  {H : H1.StandingHypotheses C.G q} {K : H1.FundamentalKernel C.G H}
  {hQ : 2 < (C.G.homogeneousDimension : ℝ)}

/-- Reuse the sharp values, from the continuity theorem, of a
type-zero kernel on a test. Both finite truncation integrability and
convergence are exported, with the exact frame gauge. -/
theorem isTypeKernel_zero_sharpValue (hF : C.IsStandardFrame F H K hQ)
    {κ : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ}
    (hκ : IsTypeKernel F 0 κ) (φ : TestFunction F.V ℝ (⊤ : ℕ∞)) (ξ : Fin (n + m) → ℝ) :
    (∀ ε : ℝ, 0 < ε → IntegrableOn (fun η => κ ξ η * φ η)
      {η | ε < F.rho ξ η} volume) ∧
    Tendsto (fun ε : ℝ => ∫ η in {η | ε < F.rho ξ η}, κ ξ η * φ η)
      (𝓝[>] (0 : ℝ))
      (𝓝 (limUnder (𝓝[>] (0 : ℝ))
        (fun ε : ℝ => ∫ η in {η | ε < F.rho ξ η}, κ ξ η * φ η))) := by
  let T : TypeOperator F 0 := {
    kernel := κ
    isType := hκ
    mult := 0
    mult_eq_zero := fun _ => rfl }
  have hφ := holderENorm_ne_top_of_contDiff_compact hF.lifted.subset_U
    φ.contDiff φ.hasCompactSupport (φ.tsupport_subset.trans hF.lifted.subset_U)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) ≤ 1)
  have hv := (T.apply_eq_rhoPV_add hF (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1) hφ).1 ξ
  simpa [TypeOperator.HasValue, TypeOperator.apply, TypeOperator.truncated, T] using hv

end RothschildStein.P1.LiftedChart
