-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.StandingDistributionRegularity
public import RothschildStein.H1.AssemblyInputs
public import RothschildStein.G2.DifferentialTranspose

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped Topology
namespace RothschildStein.H1
variable {N q : ℕ} (G : HomogeneousGroup N)

/-- A smooth representative inherits scalar homogeneity from its
homogeneous distribution, including at zero (BB p. 264). -/
theorem smoothRepresentative_homogeneous
    (T : Distribution (⊤ : Opens (Fin N → ℝ)) ℝ (⊤ : ℕ∞))
    {f : (Fin N → ℝ) → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) {α : ℝ}
    (hT : G.HasHomogeneousDistribution α T)
    (hrep : ∀ φ : TestFunction (⊤ : Opens (Fin N → ℝ)) ℝ (⊤ : ℕ∞),
      T φ = ∫ x, φ x * f x) {t : ℝ} (ht : 0 < t) :
    (fun x => f (G.dilate t x)) = fun x => t ^ α * f x := by
  apply G2.continuous_eq_of_test_pairings
    (hf.continuous.comp (G2.continuous_dilate G t)) (continuous_const.mul hf.continuous)
  intro φ hφ hc
  let ψ : TestFunction (⊤ : Opens (Fin N → ℝ)) ℝ (⊤ : ℕ∞) := ⟨φ, hφ, hc, subset_univ _⟩
  have hs := (G2.hasHomogeneousDistribution_iff G α T).mp hT t⁻¹ (inv_pos.mpr ht) ψ
  rw [hrep, hrep] at hs
  simp only [G2.dilatedTest_apply] at hs
  change (∫ x, φ (G.dilate t⁻¹ x) * f x) =
    t⁻¹ ^ (-(G.homogeneousDimension : ℝ) - α) * ∫ x, φ x * f x at hs
  have he := G2.integral_dilate G ht (fun x => φ (G.dilate t⁻¹ x) * f x)
  simp only [G2.dilate_dilate, inv_mul_cancel₀ ht.ne', G2.dilate_one, smul_eq_mul] at he
  change (∫ x, φ x * f (G.dilate t x)) = ∫ x, φ x * (t ^ α * f x)
  rw [he, hs, ← mul_assoc]
  have hfactor : (t ^ G.homogeneousDimension)⁻¹ *
      t⁻¹ ^ (-(G.homogeneousDimension : ℝ) - α) = t ^ α := by
    rw [← Real.rpow_natCast, ← Real.rpow_neg ht.le, Real.inv_rpow ht.le,
      ← Real.rpow_neg ht.le, ← Real.rpow_add ht]
    congr 1
    ring
  rw [hfactor, ← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => by ring

/-- Applying the local weak regularity theorem to the difference of fundamental distributions gives
an actual global smooth null representative. -/
theorem StandingHypotheses.smooth_difference_fundamental
    (H : StandingHypotheses G q) (K : FundamentalKernel G H)
    (T : Distribution (⊤ : Opens (Fin N → ℝ)) ℝ (⊤ : ℕ∞))
    (hT : isFundamentalDistribution (sumSquaresWithDriftTranspose H.fields) T) :
    ∃ f : (Fin N → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) f ∧
      ∀ φ : TestFunction (⊤ : Opens (Fin N → ℝ)) ℝ (⊤ : ℕ∞),
        (T - K.toDistribution) φ = ∫ x, φ x * f x := by
  have ht := (H.isFundamentalDistribution_iff G T).mp hT
  have hk := (H.isFundamentalDistribution_iff G K.toDistribution).mp K.distribution_fundamental
  obtain ⟨f, hf, he⟩ := H.exists_smooth_distributionRepresentative G ⊤
    (T - K.toDistribution) 0 contDiffOn_const (fun φ => by
      change T _ - K.toDistribution _ = _
      rw [ht φ, hk φ]
      simp [Distribution.ofFun_zero])
  exact ⟨f, contDiffOn_univ.mp hf, he⟩

/-- Arbitrary-distribution homogeneous uniqueness follows from local weak
regularity and negative-degree rigidity. -/
theorem FundamentalKernel.distributionalKernelUniqueness
    {G : HomogeneousGroup N} {H : StandingHypotheses G q} (K : FundamentalKernel G H)
    (hQ : 2 < (G.homogeneousDimension : ℝ)) : DistributionalKernelUniqueness K := by
  intro T hhom hfund
  obtain ⟨f, hf, hrep⟩ := H.smooth_difference_fundamental G K T hfund
  have hdiff : G.HasHomogeneousDistribution (2 - (G.homogeneousDimension : ℝ))
      (T - K.toDistribution) := by
    rw [G2.hasHomogeneousDistribution_iff]
    intro t ht φ
    change T _ - K.toDistribution _ = _ * (T φ - K.toDistribution φ)
    rw [(G2.hasHomogeneousDistribution_iff G _ T).mp hhom t ht φ,
      (G2.hasHomogeneousDistribution_iff G _ K.toDistribution).mp K.distribution_homogeneous t ht φ]
    ring
  have hscale := smoothRepresentative_homogeneous G (T - K.toDistribution) hf hdiff hrep
    (by norm_num : (0 : ℝ) < 2)
  have hz := eq_zero_of_fundamental_dyadic_degree G hQ hf.continuous.continuousAt
    (fun x => congrFun hscale x)
  apply DFunLike.ext
  intro φ
  have he := hrep φ
  change T φ - K.toDistribution φ = _ at he
  simp only [hz, Pi.zero_apply, mul_zero, integral_zero] at he
  exact sub_eq_zero.mp he

end RothschildStein.H1
