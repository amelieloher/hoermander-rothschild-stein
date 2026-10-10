-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Gaussian.LocalCylinderGaussianKernel
public import HeatKernel.Moser.MeanValueIdentityEssentialEndpoint

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace Filter RothschildStein
open scoped BigOperators Topology ENNReal NNReal
namespace HeatKernel.Provider

/-- The conservative horizontal heat kernel satisfies Gaussian bounds in the
horizontal control distance, with constants depending only on the group. -/
theorem exists_heatKernel_gaussian
    {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (hspan : bracketSpansOn univ (G.horizontalFields hq)) :
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
          p t x y ≤ C * t ^ (-Q / 2) * Real.exp (-(c * d x y ^ 2 / t)) :=
by
  obtain ⟨C, hC, hmean⟩ :=
    exists_uniform_identity_kernel_endpoint_essential_mean_value G hq hqpos hspan hw
  exact Gaussian.exists_gaussian_kernel_of_local_essential_mean_value
    G hq hqpos hspan hw C hC hmean

end HeatKernel.Provider
