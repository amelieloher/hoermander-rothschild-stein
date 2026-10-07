-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.SmoothDependenceMain
public import Mathlib.Analysis.Calculus.MeanValue

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric

namespace RothschildStein.G1

/-- Joint smooth dependence on parameters and initial points
by adjoining stationary coordinates (BB Proposition 1.2, p. 3). -/
theorem exists_contDiff_parameter_flow {d N : ℕ} {n : ℕ∞} (hn : 1 ≤ n)
    {A : Set (Fin d → ℝ)} {Ω : Set (Fin N → ℝ)} (hA : IsOpen A) (hΩ : IsOpen Ω)
    (Z : ((Fin d → ℝ) × (Fin N → ℝ)) → (Fin N → ℝ))
    (hZ : ContDiffOn ℝ n Z (A ×ˢ Ω))
    {param₀ : Fin d → ℝ} {x₀ : Fin N → ℝ} (hparam₀ : param₀ ∈ A) (hx₀ : x₀ ∈ Ω) :
    ∃ r : ℝ, 0 < r ∧ ∃ τ : ℝ, 0 < τ ∧
      ∃ Φ : (((Fin d → ℝ) × (Fin N → ℝ)) × ℝ) → (Fin N → ℝ),
        ball (param₀, x₀) r ⊆ A ×ˢ Ω ∧
        ContDiffOn ℝ n Φ (ball (param₀, x₀) r ×ˢ Ioo (-τ) τ) ∧
        ∀ p ∈ ball (param₀, x₀) r, Φ (p, 0) = p.2 ∧ ∀ t ∈ Ioo (-τ) τ,
          Φ (p, t) ∈ Ω ∧ HasDerivAt (fun v => Φ (p, v)) (Z (p.1, Φ (p, t))) t := by
  let F : ((Fin d → ℝ) × (Fin N → ℝ)) → ((Fin d → ℝ) × (Fin N → ℝ)) :=
    fun p => (0, Z p)
  have hF : ContDiffOn ℝ n F (A ×ˢ Ω) := contDiffOn_const.prodMk hZ
  obtain ⟨r, hr, τ, hτ, Ψ, hball, hc, hΨ⟩ :=
    exists_contDiff_local_flow hn (x₀ := (param₀, x₀)) (hA.prod hΩ) F hF ⟨hparam₀, hx₀⟩
  have ht₀ : (0 : ℝ) ∈ Ioo (-τ) τ := ⟨by linarith, hτ⟩
  have hstationary : ∀ p ∈ ball (param₀, x₀) r, ∀ t ∈ Ioo (-τ) τ, (Ψ (p, t)).1 = p.1 := by
    intro p hp t ht
    have hderiv : ∀ v ∈ Ioo (-τ) τ, HasDerivAt (fun v => (Ψ (p, v)).1) 0 v := by
      intro v hv
      exact (ContinuousLinearMap.fst ℝ (Fin d → ℝ) (Fin N → ℝ)).hasFDerivAt.comp_hasDerivAt v
        ((hΨ p hp).2 v hv).2
    have heq := isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
      (fun v hv => (hderiv v hv).differentiableAt.differentiableWithinAt)
      (fun v hv => (hderiv v hv).deriv) ht ht₀
    exact heq.trans (congrArg Prod.fst (hΨ p hp).1)
  refine ⟨r, hr, τ, hτ, (fun pt => (Ψ pt).2), hball, hc.snd, ?_⟩
  intro p hp
  refine ⟨congrArg Prod.snd (hΨ p hp).1, ?_⟩
  intro t ht
  refine ⟨((hΨ p hp).2 t ht).1.2, ?_⟩
  have hd := (ContinuousLinearMap.snd ℝ (Fin d → ℝ) (Fin N → ℝ)).hasFDerivAt.comp_hasDerivAt t
    ((hΨ p hp).2 t ht).2
  change HasDerivAt (fun v => (Ψ (p, v)).2) (Z ((Ψ (p, t)).1, (Ψ (p, t)).2)) t at hd
  rwa [hstationary p hp t ht] at hd

end RothschildStein.G1
