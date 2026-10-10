-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Gaussian.CarnotKernelConvolution
public import HeatKernel.Gaussian.ConservativeDiagonalPositivity
public import HeatKernel.Gaussian.ScaledKernelLowerBound
public import HeatKernel.Gaussian.LocalMeanValueKernelUpperBound
public import HeatKernel.Gaussian.KernelFacadeAssembly
public import HeatKernel.Kernel.ConservativeHorizontalHeatKernel
public import HeatKernel.Moser.MeanValueIdentityEssentialEndpoint
public import HeatKernel.Moser.MeanValueKernelEndpoint

/-! # Gaussian kernels from local cylinder estimates

One concrete conservative kernel, continuity and restricted convolution
combine with weak mean-value estimates to give the complete kernel conclusion.
The Gaussian upper estimate uses the single-volume prefactor V(x, sqrt t).
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric RothschildStein TopologicalSpace Filter
open scoped Topology
namespace HeatKernel.Gaussian
set_option backward.isDefEq.respectTransparency false

/-- A normalized essential mean-value estimate gives the complete
Gaussian kernel conclusion for the concrete horizontal heat semigroup. -/
theorem exists_gaussian_kernel_of_local_essential_mean_value {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (C : ℝ) (hC : 0 < C)
    (hmean : ∀ (s r : ℝ) (w : CarnotPoint G hq hqpos hspan),
      0 < r → 0 < s - 7 * r ^ 2 / 2 → ∀ v : ℝ × (Fin N → ℝ) → ℝ,
      ContinuousOn v (Ioi 0 ×ˢ univ) →
      (∀ σ > 0, ∀ w, 0 ≤ v (σ, w)) →
      IsLocalWeakSolution G hq hqpos hw hspan (fun _ _ i j ↦ if i = j then 1 else 0)
        ⟨Ioo (s - 7 * r ^ 2 / 2) (s + r ^ 2 / 2), isOpen_Ioo⟩
        ⟨interior (horizontalBall (G.horizontalFields hq) w (2 * r)), isOpen_interior⟩
        (fun σ z ↦ v (σ, z)) →
        eLpNormEssSup v (((volume : Measure ℝ).prod
          (CarnotPoint.volume G hq hqpos hspan)).restrict
            (Ioo (s - r ^ 2 / 2) (s + r ^ 2 / 2) ×ˢ ball w r)) ≤
          ENNReal.ofReal C * eLpNorm v 2
            (ENNReal.ofReal (r ^ 2 *
              (CarnotPoint.volume G hq hqpos hspan).real (ball w (2 * r)))⁻¹ •
                ((volume.restrict (Ioo (s - 7 * r ^ 2 / 2) (s + r ^ 2 / 2))).prod
                  ((CarnotPoint.volume G hq hqpos hspan).restrict (ball w (2 * r)))))) :
    let X := G.horizontalFields hq
    let L := sumSquares X
    let Q : ℝ := (G.homogeneousDimension : ℝ)
    let d : (Fin N → ℝ) → (Fin N → ℝ) → ℝ :=
      fun x y => (horizontalL2Distance X x y).toReal
    ∃ p : ℝ → (Fin N → ℝ) → (Fin N → ℝ) → ℝ,
      ContDiffOn ℝ (⊤ : ℕ∞)
        (fun z : ℝ × (Fin N → ℝ) × (Fin N → ℝ) => p z.1 z.2.1 z.2.2) (Ioi 0 ×ˢ univ) ∧
      (∀ t : ℝ, 0 < t → ∀ x y : Fin N → ℝ,
        deriv (fun s => p s x y) t = L (fun w => p t w y) x) ∧
      (∀ t : ℝ, 0 < t → ∀ x y : Fin N → ℝ, p t x y = p t y x) ∧
      (∀ s t : ℝ, 0 < s → 0 < t → ∀ x y : Fin N → ℝ,
        Integrable (fun z => p s x z * p t z y) ∧
        p (s + t) x y = ∫ z, p s x z * p t z y) ∧
      (∀ t : ℝ, 0 < t → ∀ x : Fin N → ℝ, ∫ y, p t x y = 1) ∧
      (∀ φ : (Fin N → ℝ) → ℝ, Continuous φ → (∃ M : ℝ, ∀ y, |φ y| ≤ M) →
        ∀ x : Fin N → ℝ,
          Tendsto (fun t => ∫ y, p t x y * φ y) (𝓝[>] 0) (𝓝 (φ x))) ∧
      (∀ t : ℝ, 0 < t → ∀ g x y : Fin N → ℝ, p t (G.mul g x) (G.mul g y) = p t x y) ∧
      (∀ t r : ℝ, 0 < t → 0 < r → ∀ x y : Fin N → ℝ,
        p (r ^ 2 * t) (G.dilate r x) (G.dilate r y) = (r ^ G.homogeneousDimension)⁻¹ * p t x y) ∧
      ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧
        ∀ t : ℝ, 0 < t → ∀ x y : Fin N → ℝ,
          c * t ^ (-Q / 2) * Real.exp (-(C * d x y ^ 2 / t)) ≤ p t x y ∧
          p t x y ≤ C * t ^ (-Q / 2) * Real.exp (-(c * d x y ^ 2 / t)) := by
  obtain ⟨p, hp, hn, hsym, hconv, hL2, _hintL2, hrepr, _hreg, _hrow, hcol,
    _hweak, _hweakcol, hleft, hscale, _hstrong, hinit, hnonneg, _hint, hmass, _hprob⟩ :=
    exists_conservative_horizontal_heat_kernel G hq hqpos hw hspan
  have hconvolution := carnot_kernel_convolution_eq G hq hqpos hspan p hconv
  let B := 4 * (2 : ℝ) ^ G.homogeneousDimension * Real.exp (1 / 6) * C ^ 2
  have hB : 0 < B := by dsimp [B]; positivity
  have hi : ∀ s t, 0 < s → 0 < t → ∀ x y : CarnotPoint G hq hqpos hspan,
      Integrable (fun z ↦ p s x z * p t z y) (CarnotPoint.volume G hq hqpos hspan) := by
    intro s t hs ht x y
    change Integrable (fun z : Fin N → ℝ ↦ p s x z * p t z y) volume
    exact integrable_kernel_convolution_of_symmetric_L2_rows p hsym hL2 hs ht x y
  have hcont : Continuous (fun z : CarnotPoint G hq hqpos hspan ↦ p 1 0 z) :=
    hp.continuousOn.comp_continuous
      (continuous_const.prodMk (continuous_const.prodMk
        (CarnotPoint.coordinateHomeomorph G hq hqpos hspan).continuous))
      (fun _ ↦ ⟨zero_lt_one, mem_univ _⟩)
  have hpos := kernel_diagonal_pos_of_conservation volume p hL2 hmass
    (fun t _ x y ↦ hsym t x y) hconv zero_lt_one (0 : Fin N → ℝ)
  obtain ⟨b, D, hb, _hD, hlower⟩ :=
    exists_gaussian_lower_bound_of_continuity_and_covariance G hq hqpos hspan hw p
      hcont hpos hleft (fun t r ht hr ↦ hscale r t hr ht) hnonneg hi hconvolution
  apply exists_heat_kernel_gaussian_of_upper_and_lower_estimates G hq hqpos hspan hw p hp hcol
    (a := (1 / 24 : ℝ)) (U := B) (b := b) (B := D) (by norm_num) hB hb hnonneg hmass
    (fun t _ x y ↦ hsym t x y) hconvolution
    ?_ hlower hinit hleft ?_
  · intro t ht x y
    exact global_heat_kernel_upper_bound_of_local_mean_value
      G hq hqpos hspan hw p hp hcol hnonneg hrepr (fun t _ x y ↦ hsym t x y)
      C (fun s r w hr hstart v hv hn hweak ↦
        kernel_endpoint_mean_value_of_essential_bound G hq hqpos hspan hw
          s r w hr hstart v hv hC.le (hmean s r w hr hstart v hv hn hweak)) ht x y
  · intro t r ht hr x y
    exact hscale r t hr ht x y

end HeatKernel.Gaussian
