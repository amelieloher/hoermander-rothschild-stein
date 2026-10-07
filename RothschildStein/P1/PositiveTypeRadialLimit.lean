-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PositiveTypeRowIntegrability
public import RothschildStein.P1.IntegrableChartRadialLimit
public import RothschildStein.P1.RadialGaugeCutoff
public import RothschildStein.P1.ContinuityPositive

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace RothschildStein.P1.LiftedChart
variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {F : KernelFrame (n + m)}

/-- Positive-type radial regularization converges
to the actual absolute integral on every test. Row integrability is
proved from the actual chart and poles, rather than assumed. -/
theorem tendsto_positiveType_radialIntegral {lam : ℕ} (hlam : 1 ≤ lam)
    (hF : C.IsLiftedFrame F) {κ : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ}
    (hκ : IsTypeKernel F lam κ) {ξ : Fin (n + m) → ℝ} (hξ : ξ ∈ C.U)
    {ν : (Fin (n + m) → ℝ) → ℝ} (hν : C.G.IsHomogeneousGauge ν)
    (φ : TestFunction F.V ℝ (⊤ : ℕ∞)) :
    Tendsto (fun ε : ℝ => ∫ η, (1 - radialCutoffProfile (ν (C.G.dilate ε⁻¹ (C.Θ η ξ)))) *
      (κ ξ η * φ η)) (𝓝[>] (0 : ℝ)) (𝓝 (∫ η, κ ξ η * φ η)) := by
  have hVU : (F.V : Set (Fin (n + m) → ℝ)) ⊆ C.U :=
    subset_closure.trans hF.closure_subset
  have hrow := (C.positiveType_rowIntegrable F hF.G_eq hF.Θ_eq hVU hF.pole_smooth
    (fun star => by simpa only [hF.G_eq] using hF.pole_homogeneous star) lam hlam κ hκ ξ).1
  obtain ⟨M, hM⟩ := φ.hasCompactSupport.exists_bound_of_continuous φ.contDiff.continuous
  have hint : Integrable (fun η => κ ξ η * φ η) :=
    hrow.mul_bdd φ.contDiff.continuous.aestronglyMeasurable (Eventually.of_forall hM)
  exact C.tendsto_integrableChart_radialCutoff hξ hν hint
    (fun η hη => by
      rw [image_eq_zero_of_notMem_tsupport (f := (φ : (Fin (n + m) → ℝ) → ℝ))
        (fun ht => hη (hVU (φ.tsupport_subset ht))), mul_zero])
    radialCutoffProfile radialCutoffProfile_contDiff.continuous (by norm_num : (0 : ℝ) < 2)
    (fun r hr => radialCutoffProfile_zero hr) (fun u => radialCutoffProfile_norm_le (ν u))

end RothschildStein.P1.LiftedChart
