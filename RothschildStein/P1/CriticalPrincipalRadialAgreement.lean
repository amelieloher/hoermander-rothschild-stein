-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.RadialCriticalVariableFamilyChartLimit
public import RothschildStein.P1.RadialGaugeCutoff
public import RothschildStein.P1.ContinuityReconstruction
public import RothschildStein.P1.ContinuityPositive

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace RothschildStein.P1.LiftedChart
variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {F : KernelFrame (n + m)}

/-- The actual critical principal term, including
both endpoint cutoffs, has the same smooth-radial and prescribed sharp
principal value. No regularization agreement is assumed. -/
theorem tendsto_criticalPrincipal_radial_to_sharp
    (hF : C.IsLiftedFrame F) (t : PrincipalTerm F) (hd : t.degree = 2)
    {ξ : Fin (n + m) → ℝ} (hξ : ξ ∈ C.U)
    {ν : (Fin (n + m) → ℝ) → ℝ} (hν : C.G.IsHomogeneousGauge ν)
    (φ : TestFunction F.V ℝ (⊤ : ℕ∞)) :
    Tendsto (fun ε : ℝ => ∫ η, (1 - radialCutoffProfile (ν (C.G.dilate ε⁻¹ (C.Θ η ξ)))) *
      t.kernel ξ η * φ η) (𝓝[>] (0 : ℝ))
      (𝓝 (limUnder (𝓝[>] (0 : ℝ)) (fun ε : ℝ => ∫ η in {η | ε < ν (C.Θ η ξ)},
        t.kernel ξ η * φ η))) := by
  have hVU : (F.V : Set (Fin (n + m) → ℝ)) ⊆ C.U :=
    subset_closure.trans hF.closure_subset
  let ψ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞) :=
    ⟨fun η => t.b η * φ η, t.b.contDiff.mul φ.contDiff,
      φ.hasCompactSupport.mul_left,
      tsupport_mul_subset_right.trans (φ.tsupport_subset.trans hVU)⟩
  let A := H1.principalValueConvolution C.G ν ((t.D ξ ξ).apply (F.pole t.star))
    (C.reflectedTransport ξ ψ ∘ C.G.inv) 0 +
      ∫ η, ((t.D ξ η).apply (F.pole t.star) (C.Θ η ξ) -
        (t.D ξ ξ).apply (F.pole t.star) (C.Θ η ξ)) * ψ η
  have htsharp := (C.criticalVariableFamily_inputChart_principalValue
    (t.toSplitFamily hF.G_eq hd) (F.pole t.star) (hF.pole_smooth t.star)
    (hF.pole_homogeneous t.star) hξ hν ψ).2
  have htsmooth := C.tendsto_radialCriticalVariableFamily_inputChart
    (t.toSplitFamily hF.G_eq hd) (F.pole t.star) (hF.pole_smooth t.star)
    (hF.pole_homogeneous t.star) hξ hν radialCutoffProfile
    radialCutoffProfile_contDiff.continuous
    (show (0 : ℝ) < 1 from zero_lt_one) (show (1 : ℝ) < 2 by norm_num)
    (fun r hr => radialCutoffProfile_one hr.le) (fun r hr => radialCutoffProfile_zero hr)
    (fun u => radialCutoffProfile_norm_le (ν u)) ψ
  have heSharp (ε : ℝ) : (∫ η in {η | ε < ν (C.Θ η ξ)}, t.kernel ξ η * φ η) =
      t.a ξ * ∫ η in {η | ε < ν (C.Θ η ξ)},
        (t.D ξ η).apply (F.pole t.star) (C.Θ η ξ) * ψ η := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall (fun η => by
      simp only [PrincipalTerm.kernel, hF.Θ_eq, ψ, TestFunction.coe_mk]
      ring)
  have heSmooth (ε : ℝ) : (∫ η, (1 - radialCutoffProfile (ν (C.G.dilate ε⁻¹ (C.Θ η ξ)))) *
      t.kernel ξ η * φ η) = t.a ξ * ∫ η,
      ((t.D ξ η).apply (F.pole t.star) (C.Θ η ξ) *
        (1 - radialCutoffProfile (ν (C.G.dilate ε⁻¹ (C.Θ η ξ))))) * ψ η := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall (fun η => by
      simp only [PrincipalTerm.kernel, hF.Θ_eq, ψ, TestFunction.coe_mk]
      ring)
  have hsharp : Tendsto (fun ε : ℝ => ∫ η in {η | ε < ν (C.Θ η ξ)}, t.kernel ξ η * φ η)
      (𝓝[>] (0 : ℝ)) (𝓝 (t.a ξ * A)) := by
    simpa only [heSharp] using htsharp.const_mul (t.a ξ)
  have hsmooth : Tendsto (fun ε : ℝ => ∫ η,
      (1 - radialCutoffProfile (ν (C.G.dilate ε⁻¹ (C.Θ η ξ)))) * t.kernel ξ η * φ η)
      (𝓝[>] (0 : ℝ)) (𝓝 (t.a ξ * A)) := by
    simpa only [heSmooth] using htsmooth.const_mul (t.a ξ)
  rw [hsharp.limUnder_eq]
  exact hsmooth

end RothschildStein.P1.LiftedChart
