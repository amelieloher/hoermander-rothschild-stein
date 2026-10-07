-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.QuantitativeTimeFlow
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric

namespace RothschildStein.G4

/-- Stationary parameters preserve the prescribed buffer and time
interval of the augmented flow. -/
theorem exists_smooth_fixed_time_parameter_flow {d N : ℕ}
    {Ω : Set (Fin N → ℝ)} (hΩ : IsOpen Ω)
    (Z : ((Fin d → ℝ) × (Fin N → ℝ)) → (Fin N → ℝ))
    (hZ : ContDiffOn ℝ (⊤ : ℕ∞) Z (univ ×ˢ Ω))
    (x₀ : Fin N → ℝ) {R : ℝ} (hR : 0 < R)
    (hRΩ : closedBall x₀ R ⊆ Ω)
    (hbound : ∀ p ∈ closedBall ((0 : Fin d → ℝ), x₀) R, ‖Z p‖ ≤ R / 16) :
    ∃ Φ : (((Fin d → ℝ) × (Fin N → ℝ)) × ℝ) → (Fin N → ℝ),
      ContDiffOn ℝ (⊤ : ℕ∞) Φ
        (ball ((0 : Fin d → ℝ), x₀) (R / 4) ×ˢ Ioo (-2) 2) ∧
      ∀ p ∈ ball ((0 : Fin d → ℝ), x₀) (R / 4), Φ (p, 0) = p.2 ∧
        ∀ t ∈ Ioo (-2) 2, Φ (p, t) ∈ closedBall x₀ R ∧
          HasDerivAt (fun v => Φ (p, v)) (Z (p.1, Φ (p, t))) t := by
  let F : ((Fin d → ℝ) × (Fin N → ℝ)) → ((Fin d → ℝ) × (Fin N → ℝ)) :=
    fun p => (0, Z p)
  have hF : ContDiffOn ℝ (⊤ : ℕ∞) F (univ ×ˢ Ω) := contDiffOn_const.prodMk hZ
  have hbuffer : closedBall ((0 : Fin d → ℝ), x₀) R ⊆ univ ×ˢ Ω := by
    intro p hp
    refine ⟨mem_univ _, hRΩ ?_⟩
    have hh := mem_closedBall.mp hp
    rw [Prod.dist_eq] at hh
    exact (le_max_right _ _).trans hh
  have hb : ∀ p ∈ closedBall ((0 : Fin d → ℝ), x₀) R, ‖F p‖ ≤ R / 16 := by
    intro p hp
    simpa [F] using hbound p hp
  obtain ⟨Ψ, hc, hΨ⟩ := exists_smooth_fixed_time_flow (isOpen_univ.prod hΩ)
    hF (0, x₀) hR hbuffer hb
  have hstationary : ∀ p ∈ ball ((0 : Fin d → ℝ), x₀) (R / 4),
      ∀ t ∈ Ioo (-2 : ℝ) 2, (Ψ (p, t)).1 = p.1 := by
    intro p hp t ht
    have hd : ∀ v ∈ Ioo (-2 : ℝ) 2, HasDerivAt (fun v => (Ψ (p, v)).1) 0 v := by
      intro v hv
      exact (ContinuousLinearMap.fst ℝ (Fin d → ℝ) (Fin N → ℝ)).hasFDerivAt.comp_hasDerivAt v
        ((hΨ p hp).2 v hv).2
    have ht₀ : (0 : ℝ) ∈ Ioo (-2 : ℝ) 2 := by constructor <;> norm_num
    have heq := isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
      (fun v hv => (hd v hv).differentiableAt.differentiableWithinAt)
      (fun v hv => (hd v hv).deriv) ht ht₀
    exact heq.trans (congrArg Prod.fst (hΨ p hp).1)
  refine ⟨(fun pt => (Ψ pt).2), hc.snd, ?_⟩
  intro p hp
  refine ⟨congrArg Prod.snd (hΨ p hp).1, ?_⟩
  intro t ht
  refine ⟨?_, ?_⟩
  · have hh := mem_closedBall.mp ((hΨ p hp).2 t ht).1
    rw [Prod.dist_eq] at hh
    exact (le_max_right _ _).trans hh
  · have hd := (ContinuousLinearMap.snd ℝ (Fin d → ℝ) (Fin N → ℝ)).hasFDerivAt.comp_hasDerivAt t
      ((hΨ p hp).2 t ht).2
    change HasDerivAt (fun v => (Ψ (p, v)).2) (Z ((Ψ (p, t)).1, (Ψ (p, t)).2)) t at hd
    rwa [hstationary p hp t ht] at hd

end RothschildStein.G4
