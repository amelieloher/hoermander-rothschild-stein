-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.ReflectedPrincipalKernel
public import RothschildStein.H1.KernelReflection
public import RothschildStein.H1.AssemblyInputs
public import Mathlib.MeasureTheory.Group.Measure

/-!
# Shell cancellation of the reflected kernel

H1's weighted shell cancellation `KernelShellCancellation` (BB Thm 11.5(d)) for the fundamental kernel
`Γ` implies the same property for its reflection `Γ*(u) = Γ(-u)` (`FundamentalKernel.reflection`,
BB Thm 11.5(e)) whenever the standing norm is symmetric: for `x ≠ 0`, `D Γ*(x) = (D^refl Γ)(-x)` by BB
(11.12), p. 546 (`differentialReflection_apply`), the reflection preserves the degree
(`differentialReflection_homogeneous`), and `x ↦ -x` preserves the shell and Lebesgue measure.
(In H1's assembly the reflected property is also a direct output,
`FundamentalKernelProperties (K.reflection hQ)`; this lemma shows it is not an extra input.)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory
namespace RothschildStein.P1

/-- The shell cancellation of the reflected kernel follows from that of the original
kernel when the standing norm is symmetric (BB (11.12), p. 546; BB Thm 11.5(d), (e)). -/
theorem kernelShellCancellation_reflection {N q : ℕ} {G : HomogeneousGroup N}
    {H : H1.StandingHypotheses G q} (K : H1.FundamentalKernel G H)
    (hQ : 2 < (G.homogeneousDimension : ℝ)) (hinv : ∀ x, G.inv x = -x)
    (hsym : ∀ x, H.norm (-x) = H.norm x) (hK : H1.KernelShellCancellation K) :
    H1.KernelShellCancellation (K.reflection hQ) := by
  intro D hD r R hr hrR Φ hΦ
  obtain ⟨hint, hzero⟩ := hK (differentialReflection D) (differentialReflection_homogeneous G D hD)
    r R hr hrR Φ hΦ
  have hν : Continuous H.norm := H.norm.gauge.1
  let S : Set (Fin N → ℝ) := {x | r < H.norm x ∧ H.norm x < R}
  have hSm : MeasurableSet S := by
    have : S = H.norm ⁻¹' Ioo r R := by ext x; simp [S]
    rw [this]
    exact (isOpen_Ioo.preimage hν).measurableSet
  have hS : (fun x : Fin N → ℝ => -x) ⁻¹' S = S := by
    ext x
    simp [S, hsym x]
  have hne : ∀ x ∈ S, x ≠ 0 := by
    intro x hx h0
    have h1 : H.norm x = 0 := (H.norm.gauge.2.2.1 x).mpr h0
    have := hx.1
    linarith
  have hfun : (⇑(K.reflection hQ) : (Fin N → ℝ) → ℝ) = fun y => K (-y) :=
    funext (K.reflection_neg hQ hinv)
  have hreg : ∀ a ∈ D.indices, ContDiffOn ℝ (∑ j, a j : ℕ) K {(0 : Fin N → ℝ)}ᶜ :=
    fun a _ => K.smooth_off_zero.of_le (by exact_mod_cast le_top)
  let F : (Fin N → ℝ) → ℝ := fun y => (differentialReflection D).apply K y * Φ (H.norm y)
  have hpt : ∀ x ∈ S, D.apply (K.reflection hQ) x * Φ (H.norm x) = (F ∘ fun x => -x) x := by
    intro x hx
    simp only [Function.comp_apply, F]
    rw [hsym x, hfun, differentialReflection_apply D hreg (hne x hx)]
  have hemb : MeasurableEmbedding (fun x : Fin N → ℝ => -x) :=
    (MeasurableEquiv.neg (Fin N → ℝ)).measurableEmbedding
  have hmp : MeasurePreserving (fun x : Fin N → ℝ => -x) volume volume :=
    Measure.measurePreserving_neg _
  constructor
  · have h1 : IntegrableOn (F ∘ fun x => -x) ((fun x : Fin N → ℝ => -x) ⁻¹' S) volume :=
      (hmp.integrableOn_comp_preimage hemb).mpr hint
    rw [hS] at h1
    exact h1.congr_fun (fun x hx => (hpt x hx).symm) hSm
  · change ∫ x in S, D.apply (K.reflection hQ) x * Φ (H.norm x) = 0
    rw [setIntegral_congr_fun hSm hpt]
    have h2 := hmp.setIntegral_preimage_emb hemb F S
    rw [hS] at h2
    exact h2.trans hzero

end RothschildStein.P1
