-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.InjectiveChartContinuousInverse

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology

namespace RothschildStein.G4

/-- Local smooth inverses glue to the unique inverse on the
whole image of the actual injective nonsingular chart. Smoothness is
proved on the entire image (BB Theorems 9.11/9.42, pp. 404, 438). -/
theorem exists_smooth_inverse_of_actual_chart_injective {n : ℕ}
    {U : Set (Fin n → ℝ)} (hU : IsOpen U) (hne : U.Nonempty)
    (F : (Fin n → ℝ) → (Fin n → ℝ))
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F U)
    (hjac : ∀ u ∈ U, Matrix.det (coordinateDerivativeMatrix (fderiv ℝ F u)) ≠ 0)
    (hinj : InjOn F U) :
    IsOpen (F '' U) ∧
    ∃ Ψ : (Fin n → ℝ) → (Fin n → ℝ),
      ContDiffOn ℝ (⊤ : ℕ∞) Ψ (F '' U) ∧
      (∀ y ∈ F '' U, Ψ y ∈ U ∧ F (Ψ y) = y) ∧
      ∀ u ∈ U, Ψ (F u) = u := by
  have hlocal := isLocalHomeomorphOn_of_actual_jacobian hU F hF hjac
  have hopen : IsOpen (F '' U) := by
    apply isOpen_iff_mem_nhds.mpr
    rintro y ⟨u, hu, rfl⟩
    rw [← hlocal.map_nhds_eq hu]
    exact image_mem_map (hU.mem_nhds hu)
  obtain ⟨Ψ, hΨ, hright, hleft⟩ :=
    exists_continuous_inverse_of_actual_chart_injective hU hne F hF hjac hinj
  refine ⟨hopen, Ψ, ?_, hright, hleft⟩
  intro y hy
  have hu := (hright y hy).1
  have hFy := (hright y hy).2
  obtain ⟨ψ, hψ, _hψvalue, _hψright, hψleft⟩ :=
    exists_smooth_local_chart_inverse F (hF.contDiffAt (hU.mem_nhds hu)) (hjac _ hu)
  have hc : ContinuousAt Ψ y := hΨ.continuousAt (hopen.mem_nhds hy)
  have he := hc.tendsto.eventually hψleft
  have heq : Ψ =ᶠ[𝓝 y] ψ := by
    filter_upwards [he, hopen.mem_nhds hy] with z hz hzU
    simpa only [(hright z hzU).2] using hz.symm
  rw [hFy] at hψ
  exact (hψ.congr_of_eventuallyEq heq).contDiffWithinAt

end RothschildStein.G4
