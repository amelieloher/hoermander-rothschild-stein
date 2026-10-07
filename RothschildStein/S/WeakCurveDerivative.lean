-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.FirstFieldUniformApproximation
public import RothschildStein.G1.LocalFlows
public import Mathlib.Analysis.Calculus.UniformLimitsDeriv

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter Metric TopologicalSpace
open scoped Topology
namespace RothschildStein.S
variable {n : ℕ}

/-- Along every local integral curve, a continuous weak
field derivative is the actual derivative of the composed function.
Uniform approximation and Mathlib's uniform derivative limit theorem
supply the fundamental-theorem-of-calculus passage to the limit
(BB Thm 2.20, p. 86; converse to Prop 2.22). -/
theorem hasDerivAt_comp_curve_of_continuous_weak_derivative
    (Ω : Opens (Fin n → ℝ)) (X : (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ContDiffOn ℝ (⊤ : ℕ∞) X (Ω : Set (Fin n → ℝ)))
    (f g : (Fin n → ℝ) → ℝ)
    (hf : ContinuousOn f (Ω : Set (Fin n → ℝ)))
    (hg : ContinuousOn g (Ω : Set (Fin n → ℝ)))
    (hw : hasWeakWordDeriv (fun _ : Fin 1 => X) Ω [0] f g)
    (γ : ℝ → (Fin n → ℝ)) {t : ℝ}
    (hγ : IsIntegralCurveAt γ (fun _ => X) t) (hx : γ t ∈ (Ω : Set (Fin n → ℝ))) :
    HasDerivAt (fun s => f (γ s)) (g (γ t)) t := by
  obtain ⟨V,hV,hxV,hVΩ,hcV⟩ := exists_open_between_and_isCompact_closure
    (isCompact_singleton (x := γ t)) Ω.isOpen (by simpa only [singleton_subset_iff] using hx)
  let U : Opens (Fin n → ℝ) := ⟨V,hV⟩
  have hxU : γ t ∈ (U : Set (Fin n → ℝ)) := hxV (mem_singleton (γ t))
  obtain ⟨F,hsm,htf,htg⟩ := exists_firstField_uniform_approximation Ω U X hX hcV hVΩ f g hf hg hw
  have hm : ∀ᶠ s in 𝓝 t,γ s ∈ (U : Set (Fin n → ℝ)) :=
    hγ.continuousAt.preimage_mem_nhds (U.isOpen.mem_nhds hxU)
  obtain ⟨r,hr,hball⟩ := Metric.mem_nhds_iff.mp (hm.and hγ)
  have hmap : ball t r ⊆ γ ⁻¹' (U : Set (Fin n → ℝ)) := fun s hs => (hball hs).1
  have hder : ∀ᶠ ε : ℝ in 𝓝[>] 0,∀ s ∈ ball t r,
      HasDerivAt (fun z => F ε (γ z)) (fieldDerivative X (F ε) (γ s)) s := by
    filter_upwards [self_mem_nhdsWithin] with ε hε
    intro s hs
    exact RothschildStein.G1.integralCurve_chain_rule (hball hs).2
      ((hsm ε hε).1.differentiable (by simp)).differentiableAt
  have ht := hasDerivAt_of_tendstoUniformlyOn isOpen_ball ((htg.comp γ).mono hmap) hder
    (fun s hs => htf.tendsto_at (hmap hs)) (mem_ball_self hr)
  simpa only [Function.comp_def] using ht

end RothschildStein.S
