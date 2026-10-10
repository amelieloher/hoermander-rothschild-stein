-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Gaussian.NormalizedEndpointWitness
public import HeatKernel.Gaussian.RepresentedGaussianUpperBound
public import HeatKernel.Kernel.JointKernelLocalWeakSolutions
public import HeatKernel.Gaussian.FullVolumeHeatConjugation
public import HeatKernel.Kernel.GlobalHorizontalHeatOperators

/-! # Gaussian upper bounds from local cylinder mean values

Smooth represented kernels provide both endpoint solutions. A parabolic
mean-value estimate for their literal weak class yields Gaussian decay.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric RothschildStein TopologicalSpace
namespace HeatKernel.Gaussian
set_option backward.isDefEq.respectTransparency false

/-- A smooth represented symmetric nonnegative kernel has the explicit Gaussian
upper bound whenever its weak solution class satisfies the local cylinder mean-value
estimate. The single-volume prefactor is the reciprocal of the volume of
`B(x, sqrt t)`. -/
theorem global_heat_kernel_upper_bound_of_local_mean_value {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (p : ℝ → (Fin N → ℝ) → (Fin N → ℝ) → ℝ)
    (hp : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun w : ℝ × (Fin N → ℝ) × (Fin N → ℝ) ↦ p w.1 w.2.1 w.2.2) (Ioi 0 ×ˢ univ))
    (hheat : ∀ t, 0 < t → ∀ x z, deriv (fun s ↦ p s x z) t =
      sumSquares (G.horizontalFields hq) (fun y ↦ p t y z) x)
    (hn : ∀ σ, 0 < σ → ∀ w z, 0 ≤ p σ w z)
    (hrepr : ∀ σ > 0, ∀ u : Lp ℝ 2 (CarnotPoint.volume G hq hqpos hspan),
      (fun w ↦ ∫ z, p σ w z * u z ∂(CarnotPoint.volume G hq hqpos hspan)) =ᵐ[
        CarnotPoint.volume G hq hqpos hspan] globalHorizontalHeatOperator G hq σ.toNNReal u)
    (hsym : ∀ σ, 0 < σ → ∀ w z, p σ w z = p σ z w)
    (C : ℝ)
    (hmean : ∀ (s r : ℝ) (w : CarnotPoint G hq hqpos hspan),
      0 < r → 0 < s - 7 * r ^ 2 / 2 → ∀ v : ℝ × (Fin N → ℝ) → ℝ,
      ContinuousOn v (Ioi 0 ×ˢ univ) →
      (∀ σ > 0, ∀ w, 0 ≤ v (σ, w)) →
      IsLocalWeakSolution G hq hqpos hw hspan (fun _ _ i j ↦ if i = j then 1 else 0)
        ⟨Ioo (s - 7 * r ^ 2 / 2) (s + r ^ 2 / 2), isOpen_Ioo⟩
        ⟨interior (horizontalBall (G.horizontalFields hq) w (2 * r)), isOpen_interior⟩
        (fun σ z ↦ v (σ, z)) →
        v (s, w) ^ 2 ≤ C ^ 2 /
          (r ^ 2 * (CarnotPoint.volume G hq hqpos hspan).real (ball w (2 * r))) *
          ∫ σ in Ioo (s - 7 * r ^ 2 / 2) (s + r ^ 2 / 2),
            ∫ z in ball w (2 * r), v (σ, z) ^ 2 ∂(CarnotPoint.volume G hq hqpos hspan))
    {t : ℝ} (ht : 0 < t) (x y : CarnotPoint G hq hqpos hspan) :
    p t x y ≤ (4 * (2 : ℝ) ^ G.homogeneousDimension * Real.exp (1 / 6) * C ^ 2 /
      (CarnotPoint.volume G hq hqpos hspan).real (ball x (Real.sqrt t))) *
        Real.exp (-(1 / 24 : ℝ) * (dist x y ^ 2 / t)) := by
  let T := fun σ : ℝ ↦ globalHorizontalHeatOperator G hq σ.toNNReal
  let μ := CarnotPoint.volume G hq hqpos hspan
  let r := Real.sqrt t / 4
  have hr : 0 < r := by dsimp [r]; positivity
  have hrow : ∀ z, ContinuousOn
      (fun w : ℝ × CarnotPoint G hq hqpos hspan ↦ p w.1 z w.2) (Ioi 0 ×ˢ univ) := by
    intro z
    exact hp.continuousOn.comp
      (continuous_fst.prodMk (continuous_const.prodMk continuous_snd)).continuousOn
      (fun w hw ↦ ⟨hw.1, mem_univ _⟩)
  apply carnot_gaussian_upper_bound_of_represented_endpoint_evolutions
    G hq hqpos hspan hw p hrow T ht x y C (fun σ hσ ↦
      norm_fullVolumeHorizontalHeat_distance_conjugation_le G hq hqpos hspan
        x y (dist x y / (6 * t)) hσ.le)
  · intro s hs
    dsimp only
    intro hpos
    have hspos : 0 < s := lt_of_lt_of_le (by linarith : 0 < t / 2) hs.1
    obtain ⟨u, hu, v, hv, hvrepr, hvcenter, hvnonneg, hvweak⟩ :=
      exists_represented_normalized_endpoint_evolution G hq hqpos hspan hw p hp hheat hn
        T hrepr x y (show 0 < 2 * r by positivity) hspos hpos
    refine ⟨u, hu, v, hv.continuousOn, hvrepr, ?_⟩
    rw [← hvcenter]
    have htime := (endpoint_cylinder_subset_positive ht hs).1
    exact hmean s r y hr htime v hv.continuousOn hvnonneg
      (hvweak ⟨Ioo (s - 7 * r ^ 2 / 2) (s + r ^ 2 / 2), isOpen_Ioo⟩
        ⟨interior (horizontalBall (G.horizontalFields hq) y (2 * r)), isOpen_interior⟩
        (fun σ hσ ↦ lt_trans htime hσ.1))
  · let v : ℝ × (Fin N → ℝ) → ℝ := fun w ↦ p w.1 w.2 y
    have hv : ContinuousOn v (Ioi 0 ×ˢ univ) := hp.continuousOn.comp
      (continuous_fst.prodMk (continuous_snd.prodMk continuous_const)).continuousOn
      (fun w hw ↦ ⟨hw.1, mem_univ _⟩)
    have htime := (endpoint_cylinder_subset_positive ht
      (show t ∈ Icc (t / 2) (2 * t) by constructor <;> linarith)).1
    have hw := isLocalWeakSolution_column_of_joint_smooth_kernel G hq hqpos hw hspan p hp hheat
      ⟨Ioo (t - 7 * r ^ 2 / 2) (t + r ^ 2 / 2), isOpen_Ioo⟩
      ⟨interior (horizontalBall (G.horizontalFields hq) x (2 * r)), isOpen_interior⟩
      (fun σ hσ ↦ lt_trans htime hσ.1) y
    have hb := hmean t r x hr htime v hv (fun σ hσ w ↦ hn σ hσ w y) hw
    have he : (∫ σ in Ioo (t - 7 * r ^ 2 / 2) (t + r ^ 2 / 2),
        ∫ z in ball x (2 * r), v (σ, z) ^ 2 ∂μ) =
        ∫ σ in Ioo (t - 7 * r ^ 2 / 2) (t + r ^ 2 / 2),
          ∫ z in ball x (2 * r), p σ y z ^ 2 ∂μ := by
      apply setIntegral_congr_fun measurableSet_Ioo
      intro σ hσ
      have hσpos := ((endpoint_cylinder_subset_positive ht
        (show t ∈ Icc (t / 2) (2 * t) by constructor <;> linarith)).2 hσ).1
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun z ↦ by dsimp [v]; rw [hsym σ hσpos z y])
    rw [he] at hb
    exact hb

end HeatKernel.Gaussian
