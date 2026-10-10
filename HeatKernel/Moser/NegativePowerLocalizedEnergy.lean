-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.MeanValueLocalizedGraphEnergy

/-! # Exponent-independent localized reciprocal graph energies -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace
namespace HeatKernel

/-- Slice and dissipation budgets for reciprocal half powers control the full
localized graph energy with no loss in the reciprocal exponent. The comparisons
between the graph coordinates, primitive, diffusion, and outer value moment are
explicit hypotheses. -/
theorem reciprocal_localized_graph_energy_bounds {N q : ℕ}
    {V : Opens (Fin N → ℝ)} {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    {a b ell H L : ℝ} (hell : 0 < ell) (hH : 0 ≤ H) (hL : 0 ≤ L)
    {Y : ℝ → zeroBoundaryGraph V X} (hY : MemLp Y 2 (volume.restrict (Icc a b)))
    {θ : ℝ → ℝ} (hθ : Continuous θ)
    (hθunit : ∀ t ∈ Icc a b, θ t ∈ Icc (0 : ℝ) 1)
    {D m : ℝ → ℝ} (hD : IntegrableOn D (Icc a b)) (hm : IntegrableOn m (Icc a b))
    (hD0 : ∀ᵐ t ∂volume.restrict (Icc a b), 0 ≤ D t)
    (hm0 : ∀ᵐ t ∂volume.restrict (Icc a b), 0 ≤ m t)
    (hvalue : ∀ᵐ t ∂volume.restrict (Icc a b),
      ‖(Y t : GradientSpace (N := N) ⊤ q).fst‖ ^ 2 ≤ m t)
    (hgradient : ∀ᵐ t ∂volume.restrict (Icc a b),
      ‖(Y t : GradientSpace (N := N) ⊤ q).snd‖ ^ 2 ≤ D t / ell + 2 * L * m t)
    (hslice : ∀ᵐ t ∂volume.restrict (Icc a b),
      θ t ^ 2 * ‖(Y t : GradientSpace (N := N) ⊤ q).fst‖ ^ 2 ≤
        H * (∫ s in Icc a b, m s))
    (htotal : (∫ t in Icc a b, θ t ^ 2 * D t) ≤ H * (∫ t in Icc a b, m t)) :
    let w := fun t => θ t • Y t
    MemLp w 2 (volume.restrict (Icc a b)) ∧
      (∀ᵐ t ∂volume.restrict (Icc a b),
        ‖(w t : GradientSpace (N := N) ⊤ q).fst‖ ^ 2 ≤
          (H + H / ell + 2 * L + 1) * (∫ s in Icc a b, m s)) ∧
      (∫ t in Icc a b, ‖(w t : GradientSpace (N := N) ⊤ q).snd‖ ^ 2 +
        ‖(w t : GradientSpace (N := N) ⊤ q).fst‖ ^ 2) ≤
          (H + H / ell + 2 * L + 1) * (∫ t in Icc a b, m t) := by
  dsimp only
  let w := fun t => θ t • Y t
  have hw : MemLp w 2 (volume.restrict (Icc a b)) := by
    apply hY.mono (hθ.aestronglyMeasurable.smul hY.aestronglyMeasurable)
    filter_upwards [self_mem_ae_restrict measurableSet_Icc] with t ht
    change ‖θ t • Y t‖ ≤ ‖Y t‖
    rw [norm_smul, Real.norm_of_nonneg (hθunit t ht).1]
    exact (mul_le_mul_of_nonneg_right (hθunit t ht).2 (norm_nonneg _)).trans_eq (one_mul _)
  have hnorm (t : ℝ) :
      ‖(w t : GradientSpace (N := N) ⊤ q).snd‖ ^ 2 +
        ‖(w t : GradientSpace (N := N) ⊤ q).fst‖ ^ 2 =
      θ t ^ 2 * (‖(Y t : GradientSpace (N := N) ⊤ q).snd‖ ^ 2 +
        ‖(Y t : GradientSpace (N := N) ⊤ q).fst‖ ^ 2) := by
    simp only [w, Submodule.coe_smul, WithLp.smul_fst, WithLp.smul_snd,
      norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, mul_add]
  have hI0 : 0 ≤ ∫ t in Icc a b, m t := integral_nonneg_of_ae hm0
  have hwi := integrable_zeroBoundary_scaled_energy V X (volume.restrict (Icc a b)) hw 1
  simp only [one_pow, one_mul] at hwi
  have hθD : IntegrableOn (fun t => θ t ^ 2 * D t) (Icc a b) :=
    IntegrableOn.continuousOn_mul (hθ.pow 2).continuousOn hD isCompact_Icc
  have hupper : IntegrableOn (fun t => θ t ^ 2 * D t / ell + (2 * L + 1) * m t)
      (Icc a b) := (hθD.div_const ell).add (hm.const_mul _)
  have he := integral_mono_ae hwi hupper (by
    filter_upwards [hgradient, hvalue, hm0, hD0,
      self_mem_ae_restrict measurableSet_Icc] with t hg hv hmz hd ht
    rw [hnorm]
    have hθsq : θ t ^ 2 ≤ 1 := by
      obtain ⟨ht0, ht1⟩ := hθunit t ht
      nlinarith only [ht0, ht1]
    have h1 := mul_le_mul_of_nonneg_left (add_le_add hg hv) (sq_nonneg (θ t))
    have h2 := mul_le_mul_of_nonneg_right hθsq
      (show 0 ≤ (2 * L + 1) * m t by positivity)
    simp only [div_eq_mul_inv] at h1 ⊢
    nlinarith only [h1, h2])
  rw [integral_add (hθD.div_const ell) (hm.const_mul _), integral_div, integral_const_mul] at he
  have hdiv := div_le_div_of_nonneg_right htotal hell.le
  refine ⟨hw, ?_, ?_⟩
  · filter_upwards [hslice] with t ht
    have hvnorm : ‖(w t : GradientSpace (N := N) ⊤ q).fst‖ ^ 2 =
        θ t ^ 2 * ‖(Y t : GradientSpace (N := N) ⊤ q).fst‖ ^ 2 := by
      simp only [w, Submodule.coe_smul, WithLp.smul_fst, norm_smul, mul_pow,
        Real.norm_eq_abs, sq_abs]
    rw [hvnorm]
    have hcoef : H ≤ H + H / ell + 2 * L + 1 := by
      have := div_nonneg hH hell.le
      linarith
    exact ht.trans (mul_le_mul_of_nonneg_right hcoef hI0)
  · change (∫ t in Icc a b, ‖(w t : GradientSpace (N := N) ⊤ q).snd‖ ^ 2 +
        ‖(w t : GradientSpace (N := N) ⊤ q).fst‖ ^ 2) ≤ _
    have hscale : (H * (∫ t in Icc a b, m t)) / ell =
        (H / ell) * (∫ t in Icc a b, m t) := by ring
    rw [hscale] at hdiv
    nlinarith only [he, hdiv, mul_nonneg hH hI0]

end HeatKernel
