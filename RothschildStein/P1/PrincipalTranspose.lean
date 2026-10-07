-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.DifferentialReflection
public import RothschildStein.P1.TypeKernel

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Filter
open scoped Topology
namespace RothschildStein.P1

/-- Coordinate partials depend only on the germ of the function. -/
theorem euclideanPartial_congr_of_eventuallyEq {N : ℕ} (α : Fin N → ℕ)
    {f g : (Fin N → ℝ) → ℝ} {x : Fin N → ℝ} (h : f =ᶠ[𝓝 x] g) :
    euclideanPartial α f x = euclideanPartial α g x := by
  have he : ∀ l : List (Fin N), ∀ f g : (Fin N → ℝ) → ℝ,
      f =ᶠ[𝓝 x] g →
      l.foldr (fun j q y => fderiv ℝ q y (Hormander.Interface.basisVec j)) f =ᶠ[𝓝 x]
      l.foldr (fun j q y => fderiv ℝ q y (Hormander.Interface.basisVec j)) g := by
    intro l
    induction l with
    | nil => intro f g h; exact h
    | cons j l ih =>
      intro f g h
      exact ((ih f g h).fderiv (𝕜 := ℝ)).mono (fun y hy => congrArg (fun L => L (Hormander.Interface.basisVec j)) hy)
  exact (he _ f g h).eq_of_nhds

/-- The actual transposed principal term swaps endpoint cutoffs,
reflects the differential operator with its ordinary-order sign, and swaps
fundamental poles (BB (11.12), p. 546). -/
def PrincipalTerm.transpose {N : ℕ} {F : KernelFrame N} (t : PrincipalTerm F) :
    PrincipalTerm F where
  a := t.b
  b := t.a
  D ξ η := differentialReflection (t.D η ξ)
  indices := t.indices
  indices_eq ξ η := t.indices_eq η ξ
  coefficient_smooth := by
    intro α hα
    have h := (t.coefficient_smooth α hα).comp
      (contDiff_snd.fst.prodMk (contDiff_fst.prodMk contDiff_snd.snd.neg))
    exact contDiff_const.mul h
  degree := t.degree
  homogeneous ξ η := differentialReflection_homogeneous F.G (t.D η ξ) (t.homogeneous η ξ)
  star := !t.star

/-- Off the diagonal the constructed principal transpose is exactly
the swapped kernel, with no parity assumption on the fundamental pole. -/
theorem PrincipalTerm.transpose_kernel {N : ℕ} {F : KernelFrame N} (t : PrincipalTerm F)
    (hpole : ∀ b : Bool, ∀ u : Fin N → ℝ, u ≠ 0 → F.pole (!b) u = F.pole b (-u))
    (hsmooth : ∀ b : Bool, ContDiffOn ℝ (⊤ : ℕ∞) (F.pole b) {(0 : Fin N → ℝ)}ᶜ)
    (ξ η : Fin N → ℝ) (hu : F.Θ ξ η ≠ 0)
    (hanti : F.Θ η ξ = -F.Θ ξ η) :
    t.transpose.kernel ξ η = t.kernel η ξ := by
  have hf : ∀ α ∈ (t.D η ξ).indices,
      ContDiffOn ℝ (∑ j, α j : ℕ) (F.pole (!t.star)) {(0 : Fin N → ℝ)}ᶜ :=
    fun _ _ => (hsmooth _).of_le (by simp)
  have he := differentialReflection_apply (t.D η ξ) hf hu
  have hfun : Set.EqOn (fun u => F.pole (!t.star) (-u)) (F.pole t.star)
      {(0 : Fin N → ℝ)}ᶜ := by
    intro u hu
    change F.pole (!t.star) (-u) = F.pole t.star u
    rw [hpole t.star (-u) (neg_ne_zero.mpr hu), neg_neg]
  have heq : (t.D η ξ).apply (fun u => F.pole (!t.star) (-u)) (F.Θ ξ η) =
      (t.D η ξ).apply (F.pole t.star) (F.Θ ξ η) := by
    unfold SmoothDifferentialOperator.apply
    apply Finset.sum_congr rfl
    intro α hα
    congr 1
    exact euclideanPartial_congr_of_eventuallyEq α
      (hfun.eventuallyEq_of_mem (isOpen_compl_singleton.mem_nhds hu))
  change t.b ξ * t.a η * (differentialReflection (t.D η ξ)).apply
      (F.pole (!t.star)) (F.Θ η ξ) = _
  rw [hanti, he, heq]
  unfold PrincipalTerm.kernel
  ring

end RothschildStein.P1
