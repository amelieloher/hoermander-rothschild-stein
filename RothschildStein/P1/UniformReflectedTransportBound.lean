-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.ReflectedChartTransport

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped Topology
namespace RothschildStein.P1.LiftedChart
variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart w s Ω hΩ X x₀ m}

/-- Reflected transported test densities are
uniformly bounded for compact output sets, over the entire model space.
The bound includes the actual chart density (BB pp. 557–558). -/
theorem exists_uniform_reflectedTransport_bound
    {K : Set (Fin (n+m) → ℝ)} (hK : IsCompact K) (hKU : K ⊆ C.U)
    (ψ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞)) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ ξ ∈ K, ∀ u, ‖C.reflectedTransport ξ ψ u‖ ≤ B := by
  let A := K ×ˢ tsupport (ψ : (Fin (n+m) → ℝ) → ℝ)
  have hAU : A ⊆ C.U ×ˢ C.U := fun _ hp => ⟨hKU hp.1, ψ.tsupport_subset hp.2⟩
  have hθ : ContinuousOn (fun p : (Fin (n+m) → ℝ) × (Fin (n+m) → ℝ) => C.Θ p.1 p.2) A :=
    C.theta_smooth.continuousOn.mono hAU
  have hω : ContinuousOn (fun p : (Fin (n+m) → ℝ) × (Fin (n+m) → ℝ) =>
      C.ωp p.1 (C.Θ p.1 p.2)) A :=
    C.ωp_smooth.continuousOn.comp (continuousOn_fst.prodMk hθ)
      (fun _ hp => ⟨hKU hp.1, C.theta_mem_target (hKU hp.1) (ψ.tsupport_subset hp.2)⟩)
  have hd : ContinuousOn (fun p : (Fin (n+m) → ℝ) × (Fin (n+m) → ℝ) =>
      ψ p.2 * (C.c p.1 * (1 + C.ωp p.1 (C.Θ p.1 p.2)))) A :=
    (ψ.contDiff.continuous.comp continuous_snd).continuousOn.mul
      ((C.density_smooth.continuousOn.comp continuousOn_fst (fun _ hp => hKU hp.1)).mul
        (continuousOn_const.add hω))
  obtain ⟨B₀, hB₀⟩ := (hK.prod ψ.hasCompactSupport.isCompact).exists_bound_of_continuousOn hd
  refine ⟨max B₀ 0, le_max_right _ _, ?_⟩
  intro ξ hξ u
  by_cases hu : -u ∈ (C.e ξ).target
  · have hη : (C.e ξ).symm (-u) ∈ C.U := by
      rw [← C.e_source (hKU hξ)]
      exact (C.e ξ).mapsTo_symm hu
    have he : C.Θ ξ ((C.e ξ).symm (-u)) = -u := by
      rw [← C.e_apply (hKU hξ) hη]
      exact (C.e ξ).right_inv hu
    rw [reflectedTransport, modelTransport_of_mem hu]
    by_cases hs : (C.e ξ).symm (-u) ∈ tsupport (ψ : (Fin (n+m) → ℝ) → ℝ)
    · have hb := hB₀ (ξ, (C.e ξ).symm (-u)) ⟨hξ, hs⟩
      simpa only [he] using hb.trans (le_max_left _ _)
    · rw [image_eq_zero_of_notMem_tsupport hs, zero_mul, norm_zero]
      exact le_max_right _ _
  · simp only [reflectedTransport, modelTransport, indicator_of_notMem hu, norm_zero]
    exact le_max_right _ _

end RothschildStein.P1.LiftedChart
