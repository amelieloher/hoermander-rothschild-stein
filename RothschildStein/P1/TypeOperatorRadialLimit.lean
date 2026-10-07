-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.ActualKernelRadialRows
public import RothschildStein.P1.PositiveTypeRadialLimit

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

/-- The full actual type-zero kernel has
prescribed sharp/smooth agreement on every interior test. -/
theorem tendsto_typeZero_radialIntegral (hF : C.IsStandardFrame F H K hQ)
    {κ : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ}
    (hκ : IsTypeKernel F 0 κ) (φ : TestFunction F.V ℝ (⊤ : ℕ∞))
    {ξ : Fin (n + m) → ℝ} (hξ : ξ ∈ (F.V : Set (Fin (n + m) → ℝ))) :
    Tendsto (fun ε : ℝ => ∫ η,
      (1 - radialCutoffProfile (H.norm (C.G.dilate ε⁻¹ (C.Θ η ξ)))) * (κ ξ η * φ η))
      (𝓝[>] (0 : ℝ)) (𝓝 (limUnder (𝓝[>] (0 : ℝ))
        (fun ε : ℝ => ∫ η in {η | ε < F.rho ξ η}, κ ξ η * φ η))) := by
  simpa only [KernelFrame.rho, hF.lifted.Θ_eq, hF.gauge_eq] using
    (C.typeZeroInput_radialSharpRowData hF hκ φ hξ).tendsto_radial_to_sharp

/-- For every type, smooth radial truncation
converges to the actual operator action minus its declared multiplier. -/
theorem typeOperator_tendsto_radialIntegral {lam : ℕ}
    (hF : C.IsStandardFrame F H K hQ) (T : TypeOperator F lam)
    (φ : TestFunction F.V ℝ (⊤ : ℕ∞))
    {ξ : Fin (n + m) → ℝ} (hξ : ξ ∈ (F.V : Set (Fin (n + m) → ℝ))) :
    Tendsto (fun ε : ℝ => ∫ η,
      (1 - radialCutoffProfile (H.norm (C.G.dilate ε⁻¹ (C.Θ η ξ)))) * (T.kernel ξ η * φ η))
      (𝓝[>] (0 : ℝ)) (𝓝 (T.apply φ ξ - T.mult ξ * φ ξ)) := by
  by_cases hlam : lam = 0
  · subst lam
    have he : T.apply φ ξ - T.mult ξ * φ ξ =
        limUnder (𝓝[>] (0 : ℝ)) (fun ε : ℝ => ∫ η in {η | ε < F.rho ξ η},
          T.kernel ξ η * φ η) := by
      simp [TypeOperator.apply, TypeOperator.truncated]
    rw [he]
    exact C.tendsto_typeZero_radialIntegral hF T.isType φ hξ
  · have hμ : T.mult ξ = 0 := by
      simpa using congrFun (T.mult_eq_zero hlam) ξ
    have he : T.apply φ ξ - T.mult ξ * φ ξ = ∫ η, T.kernel ξ η * φ η := by
      simp [TypeOperator.apply, hlam, hμ]
    rw [he]
    exact C.tendsto_positiveType_radialIntegral (Nat.one_le_iff_ne_zero.mpr hlam) hF.lifted
      T.isType (hF.lifted.closure_subset (subset_closure hξ)) H.norm.gauge φ

end RothschildStein.P1.LiftedChart
