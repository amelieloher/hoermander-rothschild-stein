-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.ConvolutionSubstitution
public import Mathlib.Analysis.Calculus.ContDiff.Convolution
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open MeasureTheory Set Function Metric
namespace RothschildStein.G2
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Auxiliary kernel for the parameter integral (BB p. 122). -/
def groupKernel (ψ : (Fin N → ℝ) → ℝ) (x u : Fin N → ℝ) : ℝ :=
  ψ (G.mul x (G.inv (-u)))

/-- A common compact set for the integration variable when the
parameter varies in a unit ball (BB p. 122; compact support). -/
def groupKernelSupport (ψ : (Fin N → ℝ) → ℝ) (x₀ : Fin N → ℝ) : Set (Fin N → ℝ) :=
  (fun p : (Fin N → ℝ) × (Fin N → ℝ) => -(G.mul (G.inv p.1) p.2)) ''
    (tsupport ψ ×ˢ closedBall x₀ 1)

/-- The common integration-variable support is compact (BB p. 122). -/
theorem isCompact_groupKernelSupport {ψ : (Fin N → ℝ) → ℝ}
    (hcψ : HasCompactSupport ψ) (x₀ : Fin N → ℝ) : IsCompact (groupKernelSupport G ψ x₀) :=
  (hcψ.isCompact.prod (isCompact_closedBall x₀ 1)).image
    (((continuous_mul G).comp (((continuous_inv G).comp continuous_fst).prodMk continuous_snd)).neg)

/-- The auxiliary kernel vanishes outside the common compact set
(BB p. 122; compact support). -/
theorem groupKernel_vanish {ψ : (Fin N → ℝ) → ℝ} {x₀ x u : Fin N → ℝ}
    (hx : x ∈ ball x₀ 1) (hu : u ∉ groupKernelSupport G ψ x₀) : groupKernel G ψ x u = 0 := by
  by_contra hn
  apply hu
  refine ⟨(G.mul x (G.inv (-u)), x), ⟨subset_closure hn, ball_subset_closedBall hx⟩, ?_⟩
  change -(G.mul (G.inv (G.mul x (G.inv (-u)))) x) = u
  simp only [inv_product, inv_inv, mul_assoc, inv_mul, mul_zero, neg_neg]

/-- Joint smoothness of the auxiliary kernel (BB p. 122). -/
theorem contDiff_groupKernel {ψ : (Fin N → ℝ) → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    ContDiff ℝ (⊤ : ℕ∞) (uncurry (groupKernel G ψ)) := by
  have hn : ContDiff ℝ (⊤ : ℕ∞) (fun p : (Fin N → ℝ) × (Fin N → ℝ) => -p.2) :=
    contDiff_snd.neg
  have hi : ContDiff ℝ (⊤ : ℕ∞) (fun p : (Fin N → ℝ) × (Fin N → ℝ) => G.inv (-p.2)) :=
    (contDiff_inv G).comp hn
  have hm : ContDiff ℝ (⊤ : ℕ∞)
      (fun p : (Fin N → ℝ) × (Fin N → ℝ) => G.mul p.1 (G.inv (-p.2))) :=
    by
      apply contDiff_pi.mpr
      intro j
      apply (contDiff_eval (G.productPolynomial j)).comp
      apply contDiff_pi.mpr
      intro i
      cases i with
      | inl k => exact (contDiff_apply ℝ ℝ k).comp contDiff_fst
      | inr k => exact (contDiff_apply ℝ ℝ k).comp hi
  exact hψ.comp hm

/-- Convolving a compact smooth kernel on the left with a locally
integrable input is smooth (BB Prop 3.48 proof, p. 122; parametric integral). The coordinate convolution is only an auxiliary integral at zero. -/
theorem contDiff_groupConvolution_left {ψ h : (Fin N → ℝ) → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hcψ : HasCompactSupport ψ)
    (hh : LocallyIntegrable h volume) :
    ContDiff ℝ (⊤ : ℕ∞) (groupConvolution G ψ h) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x₀
  let g := groupKernel G ψ
  let K := groupKernelSupport G ψ x₀
  have hK := isCompact_groupKernelSupport G hcψ x₀
  have hgs : ∀ x u, x ∈ ball x₀ 1 → u ∉ K → g x u = 0 :=
    fun _ _ hx hu => groupKernel_vanish G hx hu
  have hg := contDiff_groupKernel G hψ
  have H := contDiffOn_convolution_right_with_param (ContinuousLinearMap.mul ℝ ℝ)
    isOpen_ball hK hgs hh hg.contDiffOn
  have H₀ : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun x => convolution h (g x) (ContinuousLinearMap.mul ℝ ℝ) volume 0) (ball x₀ 1) := by
    apply H.comp (contDiff_id.prodMk contDiff_const).contDiffOn
    intro x hx
    exact ⟨hx, mem_univ _⟩
  have he : (fun x => convolution h (g x) (ContinuousLinearMap.mul ℝ ℝ) volume 0) =
      groupConvolution G ψ h := by
    funext x
    change (∫ w, h w * ψ (G.mul x (G.inv (-(0 - w))))) = _
    simp only [zero_sub, neg_neg]
    rw [groupConvolution_def]
    simp only [mul_comm]
  rw [he] at H₀
  exact H₀.contDiffAt (ball_mem_nhds x₀ zero_lt_one)

end RothschildStein.G2
