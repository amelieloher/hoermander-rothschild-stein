-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.MeanValueWeakIntegrandScaling
public import HeatKernel.Moser.MeanValueParabolicIntegrals
public import HeatKernel.Form.ParabolicEnergyCurves
import Mathlib.Tactic

/-! # Transport of the weak spacetime equation under parabolic scaling -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace RothschildStein
namespace HeatKernel

/-- The actual spacetime weak identity transports to every cylinder contained in the
inverse coordinate image, with pulled-back coefficients and gradient factor r. -/
theorem SatisfiesParabolicTestIdentity.parabolic_pullback {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N)
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (t₀ : ℝ) (x₀ : Fin N → ℝ) (r : ℝ) (hr : 0 < r)
    {a : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ}
    {I : Opens ℝ} {U : Opens (Fin N → ℝ)}
    {u : ℝ → (Fin N → ℝ) → ℝ} {g : Fin q → ℝ → (Fin N → ℝ) → ℝ}
    (h : SatisfiesParabolicTestIdentity (G.horizontalFields hq) a I U u g)
    (J : Opens ℝ) (V : Opens (Fin N → ℝ))
    (hdom : (J : Set ℝ) ×ˢ (V : Set (Fin N → ℝ)) ⊆
      (parabolicGroupHomeomorph G t₀ x₀ r hr) ⁻¹'
        ((I : Set ℝ) ×ˢ (U : Set (Fin N → ℝ)))) :
    let T := parabolicGroupHomeomorph G t₀ x₀ r hr
    SatisfiesParabolicTestIdentity (G.horizontalFields hq)
      (fun t x i j => a (T (t, x)).1 (T (t, x)).2 i j) J V
      (fun t x => u (T (t, x)).1 (T (t, x)).2)
      (fun i t x => r * g i (T (t, x)).1 (T (t, x)).2) := by
  intro T φ hφ hc hs
  let ψ := parabolicTestTransport G t₀ x₀ r hr φ
  obtain ⟨hf, hz⟩ := h ψ (contDiff_parabolicTestTransport G t₀ x₀ r hr hφ)
    (hasCompactSupport_parabolicTestTransport G t₀ x₀ r hr hc)
    (tsupport_parabolicTestTransport_subset G t₀ x₀ r hr (hs.trans hdom))
  let f := fun z : ℝ × (Fin N → ℝ) =>
    -(u z.1 z.2 * fderiv ℝ ψ z (1, 0)) +
      ∑ i, ∑ j, a z.1 z.2 i j * g j z.1 z.2 *
        fderiv ℝ ψ z (0, G.horizontalFields hq i z.2)
  let F := fun z : ℝ × (Fin N → ℝ) =>
    -(u (T z).1 (T z).2 * fderiv ℝ φ z (1, 0)) +
      ∑ i, ∑ j, a (T z).1 (T z).2 i j * (r * g j (T z).1 (T z).2) *
        fderiv ℝ φ z (0, G.horizontalFields hq i z.2)
  change Integrable f at hf
  change (∫ z, f z) = 0 at hz
  have he : ∀ z, f (T z) = (r ^ 2)⁻¹ * F z :=
    parabolic_weak_integrand_scaling G hq hw t₀ x₀ r hr a u g hφ
  have he' : F = fun z => r ^ 2 * f (T z) := by
    funext z
    rw [he, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hr.ne'), one_mul]
  change Integrable F ∧ (∫ z, F z) = 0
  constructor
  · rw [he']
    exact (integrable_comp_parabolicGroupHomeomorph G t₀ x₀ r hr hf).const_mul (r ^ 2)
  · rw [he', integral_const_mul, integral_comp_parabolicGroupHomeomorph G t₀ x₀ r hr, hz]
    simp

end HeatKernel
