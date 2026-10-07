-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.RegularAbsoluteSmallBall
public import RothschildStein.P1.InputFamilyUniformRadialError
public import RothschildStein.P1.UniformLinearErrorLimit
public import RothschildStein.P1.ContinuityPositive
public import RothschildStein.P1.RegularKernelIntegrability

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

/-- Regular rows have uniform O(ε) smooth
radial truncation convergence on compact subsets, with the true chart density. -/
theorem exists_regular_uniform_radialError_bound
    (hF : C.IsLiftedFrame F)
    {r : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ}
    (hr : IsRegularKernel F 1 r)
    {ν : (Fin (n + m) → ℝ) → ℝ} (hν : C.G.IsHomogeneousGauge ν)
    (φ : TestFunction F.V ℝ (⊤ : ℕ∞))
    {L : Set (Fin (n + m) → ℝ)} (hL : IsCompact L)
    (hLU : L ⊆ C.U) :
    ∃ ρ A : ℝ, 0 < ρ ∧ 0 ≤ A ∧ ∀ ξ ∈ L, ∀ ε : ℝ, 0 < ε → ε ≤ ρ →
      ‖(∫ η, (1 - radialCutoffProfile (ν (C.G.dilate ε⁻¹ (C.Θ η ξ)))) *
        (r ξ η * φ η)) - (∫ η, r ξ η * φ η)‖ ≤ A * ε := by
  have hVU : (F.V : Set (Fin (n + m) → ℝ)) ⊆ C.U :=
    subset_closure.trans hF.closure_subset
  let ψ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞) :=
    ⟨φ, φ.contDiff, φ.hasCompactSupport, φ.tsupport_subset.trans hVU⟩
  obtain ⟨ρ, A, hρ, hA, hb⟩ :=
    C.exists_regular_uniform_absoluteSmallBall_bound hr hν ψ hL hLU
  have hi : ∀ ξ ∈ L, Integrable (fun η => r ξ η * ψ η) := by
    intro ξ _
    have hM := Classical.choose_spec
      (φ.hasCompactSupport.exists_bound_of_continuous φ.contDiff.continuous)
    exact (hr.integrable_slices ξ).1.mul_bdd φ.contDiff.continuous.aestronglyMeasurable
      (Eventually.of_forall hM)
  refine ⟨ρ / 2, 2 * A, by positivity, by positivity, ?_⟩
  intro ξ hξ ε hε hερ
  exact C.inputFamily_uniform_radialError_of_absoluteSmallBall hν
    (fun ξ η _ => r ξ η) ψ hLU hi hb ξ hξ ε hε (by linarith)

/-- Actual smooth radial operator rows converge
uniformly on compact center sets. -/
theorem tendstoUniformlyOn_regular_radialIntegral
    (hF : C.IsLiftedFrame F)
    {r : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ}
    (hr : IsRegularKernel F 1 r)
    {ν : (Fin (n + m) → ℝ) → ℝ} (hν : C.G.IsHomogeneousGauge ν)
    (φ : TestFunction F.V ℝ (⊤ : ℕ∞))
    {L : Set (Fin (n + m) → ℝ)} (hL : IsCompact L)
    (hLU : L ⊆ C.U) :
    TendstoUniformlyOn (fun ε : ℝ => fun ξ => ∫ η,
      (1 - radialCutoffProfile (ν (C.G.dilate ε⁻¹ (C.Θ η ξ)))) *
        (r ξ η * φ η)) (fun ξ => ∫ η, r ξ η * φ η)
      (𝓝[>] (0 : ℝ)) L := by
  obtain ⟨radius, A, hRadius, _, hb⟩ :=
    C.exists_regular_uniform_radialError_bound hF hr hν φ hL hLU
  exact tendstoUniformlyOn_of_linearError hRadius hb

end RothschildStein.P1.LiftedChart
