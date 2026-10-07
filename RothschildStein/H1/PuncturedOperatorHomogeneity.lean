-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.DifferentialLocality
public import RothschildStein.H1.DifferentialScalar
public import RothschildStein.H1.SmoothGermExtension
public import RothschildStein.G2.DilationMeasure

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set TopologicalSpace Filter
open scoped Topology
namespace RothschildStein.H1
variable {N : ℕ} (G : HomogeneousGroup N)

/-- For punctured smooth kernels, the operator
homogeneity predicate extends from globally smooth tests to local
smooth germs, and subtracts its degree from the kernel degree. -/
theorem differentialOperator_punctured_homogeneity
    (P : SmoothDifferentialOperator N) {k β : ℝ} (hP : P.IsHomogeneous G k)
    {f : (Fin N → ℝ) → ℝ} (hc : ContDiffOn ℝ (⊤ : ℕ∞) f {(0 : Fin N → ℝ)}ᶜ)
    (hf : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 → f (G.dilate t x) = t ^ β * f x)
    {t : ℝ} (ht : 0 < t) {x : Fin N → ℝ} (hx : x ≠ 0) :
    P.apply f (G.dilate t x) = t ^ (β - k) * P.apply f x := by
  have hDt : G.dilate t x ≠ 0 := by
    intro he
    apply hx
    exact (G2.dilate_bijective G ht.ne').injective (he.trans (G2.dilate_zero G t).symm)
  let U : Opens (Fin N → ℝ) := ⟨{0}ᶜ, isOpen_compl_singleton⟩
  obtain ⟨g, hg, _, he⟩ := exists_smoothCompact_germ U hc (by change G.dilate t x ∈ ({(0 : Fin N → ℝ)}ᶜ : Set (Fin N → ℝ)); simpa using hDt)
  have hcomp : (g ∘ G.dilate t) =ᶠ[𝓝 x] (f ∘ G.dilate t) :=
    he.comp_tendsto (G2.continuous_dilate G t).continuousAt.tendsto
  have hscale : (f ∘ G.dilate t) =ᶠ[𝓝 x] fun y => t ^ β * f y := by
    filter_upwards [isOpen_compl_singleton.mem_nhds (show x ∈ {(0 : Fin N → ℝ)}ᶜ by simpa using hx)] with y hy
    exact hf t ht y (by simpa using hy)
  have hd := hP g hg t ht x
  rw [differentialOperator_germ_eq P hcomp, differentialOperator_germ_eq P he,
    differentialOperator_germ_eq P hscale, differentialOperator_const_mul] at hd
  apply mul_left_cancel₀ (ne_of_gt (Real.rpow_pos_of_pos ht k))
  rw [← mul_assoc, ← Real.rpow_add ht]
  have hdeg : k + (β - k) = β := by ring
  rw [hdeg]
  exact hd.symm

end RothschildStein.H1
