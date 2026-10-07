-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.ConvolutionSubstitution
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Topology.UniformSpace.UniformConvergence
public import Mathlib.Analysis.Normed.Group.Bounded

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace RothschildStein.H3
attribute [local irreducible] HomogeneousGroup.mul HomogeneousGroup.inv
variable {N : ℕ}

/-- (b) Uniformly convergent continuous sources with a common
compact support give pointwise convergence of their actual group
convolutions with every locally integrable kernel (BB p. 379).
The compact integration region and domination are constructed here. -/
theorem tendsto_groupConvolution_of_uniform_compact_support
    {ι : Type*} (G : HomogeneousGroup N) (l : Filter ι) [l.IsCountablyGenerated]
    (F : ι → (Fin N → ℝ) → ℝ) (f K : (Fin N → ℝ) → ℝ)
    (hK : LocallyIntegrable K volume) (hf : Continuous f)
    (S : Set (Fin N → ℝ)) (hS : IsCompact S)
    (hsf : Function.support f ⊆ S)
    (hF : ∀ᶠ t in l, Continuous (F t) ∧ Function.support (F t) ⊆ S)
    (hu : TendstoUniformly F f l) (x : Fin N → ℝ) :
    Tendsto (fun t => G2.groupConvolution G (F t) K x) l
      (𝓝 (G2.groupConvolution G f K x)) := by
  have hc : HasCompactSupport f :=
    hS.of_isClosed_subset isClosed_closure (closure_minimal hsf hS.isClosed)
  obtain ⟨C, hC⟩ := hf.bounded_above_of_compact_support hc
  let E : Set (Fin N → ℝ) := (fun y => G.mul (G.inv y) x) '' S
  have hE : IsCompact E := hS.image
    ((G2.continuous_mul G).comp ((G2.continuous_inv G).prodMk continuous_const))
  have hki : IntegrableOn K E volume := hK.integrableOn_isCompact hE
  have hz (g : (Fin N → ℝ) → ℝ) (hg : Function.support g ⊆ S)
      (w : Fin N → ℝ) (hw : w ∉ E) : g (G.mul x (G.inv w)) = 0 := by
    by_contra hn
    apply hw
    refine ⟨G.mul x (G.inv w), hg hn, ?_⟩
    simp only [G2.inv_product, G2.inv_inv, G2.mul_assoc, G2.inv_mul, G2.mul_zero]
  have heq (g : (Fin N → ℝ) → ℝ) (hg : Function.support g ⊆ S) :
      (∫ w in E, g (G.mul x (G.inv w)) * K w) = G2.groupConvolution G g K x := by
    rw [G2.groupConvolution_def]
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro w hw
    rw [hz g hg w hw, zero_mul]
  have hm : ∀ᶠ t in l, AEStronglyMeasurable
      (fun w => F t (G.mul x (G.inv w)) * K w) (volume.restrict E) := by
    filter_upwards [hF] with t ht
    exact (((ht.1.comp ((G2.continuous_mul G).comp
      (continuous_const.prodMk (G2.continuous_inv G)))).aestronglyMeasurable).mono_measure
        Measure.restrict_le_self).mul hki.aestronglyMeasurable
  have hb : ∀ᶠ t in l, ∀ᵐ w ∂volume.restrict E,
      ‖F t (G.mul x (G.inv w)) * K w‖ ≤ (1 + C) * ‖K w‖ := by
    filter_upwards [Metric.tendstoUniformly_iff.mp hu 1 zero_lt_one] with t ht
    apply Eventually.of_forall
    intro w
    have hd : ‖F t (G.mul x (G.inv w)) - f (G.mul x (G.inv w))‖ < 1 := by
      simpa only [dist_eq_norm, norm_sub_rev] using ht (G.mul x (G.inv w))
    have hn := norm_add_le (F t (G.mul x (G.inv w)) - f (G.mul x (G.inv w)))
      (f (G.mul x (G.inv w)))
    have hs : ‖F t (G.mul x (G.inv w))‖ ≤ 1 + C := by
      simp only [sub_add_cancel] at hn
      linarith [hC (G.mul x (G.inv w))]
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right hs (norm_nonneg _)
  have hi := tendsto_integral_filter_of_dominated_convergence
    (fun w => (1 + C) * ‖K w‖) hm hb (hki.norm.const_mul (1 + C))
    (Eventually.of_forall fun w => (hu.tendsto_at (G.mul x (G.inv w))).mul_const (K w))
  rw [heq f hsf] at hi
  apply hi.congr'
  filter_upwards [hF] with t ht
  exact heq (F t) ht.2

end RothschildStein.H3
