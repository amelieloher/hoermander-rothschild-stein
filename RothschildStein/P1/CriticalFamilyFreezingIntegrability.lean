-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.CriticalFamilyChartFreezingBound
public import RothschildStein.P1.LocalChartPoleIntegrability

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
namespace RothschildStein.P1.LiftedChart
variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart w s Ω hΩ X x₀ m}
  {D : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → SmoothDifferentialOperator (n + m)}

/-- The actual endpoint-family freezing error
is absolutely integrable on compact input patches. -/
theorem integrableOn_criticalFamily_freezingError
    (F : SplitFamily C.G D) (Γ : (Fin (n + m) → ℝ) → ℝ)
    (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) Γ {(0 : Fin (n + m) → ℝ)}ᶜ)
    (hhom : ∀ r : ℝ, 0 < r → ∀ u : Fin (n + m) → ℝ, u ≠ 0 →
      Γ (C.G.dilate r u) = r ^ (2 - (C.G.homogeneousDimension : ℝ)) * Γ u)
    {ξ : Fin (n + m) → ℝ} (hξ : ξ ∈ C.U)
    {K : Set (Fin (n + m) → ℝ)} (hK : IsCompact K) (hKU : K ⊆ C.U) :
    IntegrableOn (fun η => (D ξ η).apply Γ (C.Θ η ξ) -
      (D ξ ξ).apply Γ (C.Θ η ξ)) K volume := by
  have hc : ContinuousOn (fun η => (D ξ η).apply Γ (C.Θ η ξ) -
      (D ξ ξ).apply Γ (C.Θ η ξ)) (K \ {ξ}) := by
    have hmap : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun η : Fin (n + m) → ℝ => (ξ, η, C.Θ η ξ)) (K \ {ξ}) :=
      contDiffOn_const.prodMk (contDiffOn_id.prodMk
        ((C.contDiffOn_Θ_fst hξ).mono (sdiff_subset.trans hKU)))
    exact (((F.contDiffOn_kernelUncurry hΓ).sub (F.contDiffOn_kernelUncurry_diag hΓ)).comp
      hmap (fun η hη => (C.theta_eq_zero_iff (hKU hη.1) hξ).not.mpr
        (fun he => hη.2 (mem_singleton_iff.mpr he.symm)))).continuousOn
  have hsingle : ({ξ} : Set (Fin (n + m) → ℝ)) ⊆ C.U := by
    intro η hη
    simpa only [mem_singleton_iff.mp hη] using hξ
  obtain ⟨ε, M, hε, hM, hb⟩ := exists_criticalFamily_chartFreezing_bound F Γ hΓ hhom
    isCompact_singleton hsingle
  apply integrableOn_of_local_gauge_power_bound hξ hK hKU _ hc
    (1 - (C.G.homogeneousDimension : ℤ)) (by omega) hε hM
  intro η hη hne hsmall
  exact hb ξ (mem_singleton ξ) η (hKU hη) hne.symm hsmall.le

/-- Compact interior testing makes the actual
freezing error integrable over the full ambient input space. -/
theorem integrable_criticalFamily_freezingError_test
    (F : SplitFamily C.G D) (Γ : (Fin (n + m) → ℝ) → ℝ)
    (hΓ : ContDiffOn ℝ (⊤ : ℕ∞) Γ {(0 : Fin (n + m) → ℝ)}ᶜ)
    (hhom : ∀ r : ℝ, 0 < r → ∀ u : Fin (n + m) → ℝ, u ≠ 0 →
      Γ (C.G.dilate r u) = r ^ (2 - (C.G.homogeneousDimension : ℝ)) * Γ u)
    {ξ : Fin (n + m) → ℝ} (hξ : ξ ∈ C.U)
    (ψ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞)) :
    Integrable (fun η => ((D ξ η).apply Γ (C.Θ η ξ) -
      (D ξ ξ).apply Γ (C.Θ η ξ)) * ψ η) volume := by
  have hi := integrableOn_criticalFamily_freezingError F Γ hΓ hhom hξ
    ψ.hasCompactSupport.isCompact ψ.tsupport_subset
  exact (hi.mul_continuousOn ψ.contDiff.continuous.continuousOn
    ψ.hasCompactSupport.isCompact).integrable_of_forall_notMem_eq_zero (fun η hη => by
      rw [image_eq_zero_of_notMem_tsupport hη, mul_zero])

end RothschildStein.P1.LiftedChart
