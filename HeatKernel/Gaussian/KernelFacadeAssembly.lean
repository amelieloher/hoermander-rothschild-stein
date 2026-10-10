-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Gaussian.TimeNormalization
public import RothschildStein.Definitions.sumSquares
public import HeatKernel.Gaussian.ConservativeMass
public import HeatKernel.Gaussian.RowIntegrability

/-! # Conservative kernels with Gaussian bounds

The assembly uses the single-volume prefactor V(x, sqrt t) for the upper
estimate. Exact Carnot volumes convert it to homogeneous-time bounds with
one ordered constant pair. All kernel properties refer to one common witness.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric RothschildStein Filter
open scoped Topology
namespace HeatKernel.Gaussian
set_option backward.isDefEq.respectTransparency false

/-- One conservative covariant smooth kernel with Gaussian upper and lower
estimates satisfies the complete kernel conclusion. The upper estimate
uses the single-volume prefactor V(x, sqrt t). -/
theorem exists_heat_kernel_gaussian_of_upper_and_lower_estimates {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (p : ℝ → (Fin N → ℝ) → (Fin N → ℝ) → ℝ)
    (hp : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : ℝ × (Fin N → ℝ) × (Fin N → ℝ) ↦ p z.1 z.2.1 z.2.2) (Ioi 0 ×ˢ univ))
    (hheat : ∀ t, 0 < t → ∀ x y, deriv (fun s ↦ p s x y) t =
      sumSquares (G.horizontalFields hq) (fun w ↦ p t w y) x)
    {a U b B : ℝ} (ha : 0 < a) (hU : 0 < U) (hb : 0 < b)
    (hn : ∀ t, 0 < t → ∀ x y, 0 ≤ p t x y)
    (hmass : ∀ t, 0 < t → ∀ x, ∫ z, p t x z
      ∂(CarnotPoint.volume G hq hqpos hspan) = 1)
    (hsym : ∀ t, 0 < t → ∀ x y, p t x y = p t y x)
    (hconv : ∀ s t, 0 < s → 0 < t → ∀ x y,
      p (s + t) x y = ∫ z, p s x z * p t z y ∂(CarnotPoint.volume G hq hqpos hspan))
    (hupper : ∀ t, 0 < t → ∀ x y : CarnotPoint G hq hqpos hspan, p t x y ≤
      U / (CarnotPoint.volume G hq hqpos hspan).real (ball x (Real.sqrt t)) *
        Real.exp (-a * (dist x y ^ 2 / t)))
    (hlower : ∀ t, 0 < t → ∀ x y : CarnotPoint G hq hqpos hspan,
      b * t ^ (-(G.homogeneousDimension : ℝ) / 2) *
        Real.exp (-B * (dist x y ^ 2 / t)) ≤ p t x y)
    (hinit : ∀ φ : (Fin N → ℝ) → ℝ, Continuous φ → (∃ M : ℝ, ∀ y, |φ y| ≤ M) →
      ∀ x, Tendsto (fun t ↦ ∫ y, p t x y * φ y) (𝓝[>] 0) (𝓝 (φ x)))
    (hleft : ∀ t, 0 < t → ∀ g x y, p t (G.mul g x) (G.mul g y) = p t x y)
    (hscale : ∀ t r, 0 < t → 0 < r → ∀ x y,
      p (r ^ 2 * t) (G.dilate r x) (G.dilate r y) =
        (r ^ G.homogeneousDimension)⁻¹ * p t x y) :
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
  have hc : ∀ x, ContinuousOn
      (fun z : ℝ × CarnotPoint G hq hqpos hspan ↦ p z.1 x z.2) (Ioi 0 ×ˢ univ) := by
    intro x
    exact hp.continuousOn.comp
      (continuous_fst.prodMk (continuous_const.prodMk continuous_snd)).continuousOn
      (fun z hz ↦ ⟨hz.1, mem_univ _⟩)
  let v := volume.real (horizontalBall (G.horizontalFields hq) 0 1)
  let I := {t : ℝ // 0 < t} × CarnotPoint G hq hqpos hspan × CarnotPoint G hq hqpos hspan
  let P : I → ℝ := fun i ↦ p i.1.1 i.2.1 i.2.2
  let S : I → ℝ := fun i ↦ i.1.1 ^ (-(G.homogeneousDimension : ℝ) / 2)
  let D : I → ℝ := fun i ↦ dist i.2.1 i.2.2 ^ 2 / i.1.1
  have hu : ∀ i, P i ≤ (U / v) * S i * Real.exp (-a * D i) := by
    intro i
    have H := hupper i.1.1 i.1.2 i.2.1 i.2.2
    simp only [div_eq_mul_inv] at H
    rw [inv_carnot_heat_volume_eq G hq hqpos hspan hw i.2.1 i.1.2] at H
    simpa only [P, S, D, v, div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using H
  obtain ⟨c, C, hcpos, hcC, hbounds⟩ := exists_common_gaussian_constants P S D ha hb
    (fun i ↦ (Real.rpow_pos_of_pos i.1.2 _).le)
    (fun i ↦ div_nonneg (sq_nonneg _) i.1.2.le)
    (fun i ↦ hlower i.1.1 i.1.2 i.2.1 i.2.2) hu
  refine ⟨p, hp, hheat, hsym, ?_, hmass, hinit, hleft, hscale, c, C, hcpos, hcC, ?_⟩
  · intro s t hs ht x y
    refine ⟨?_, hconv s t hs ht x y⟩
    apply integrable_kernel_convolution_of_gaussian_and_mass
      (CarnotPoint.volume G hq hqpos hspan) p
      (fun t x ↦ (CarnotPoint.volume G hq hqpos hspan).real (ball x (Real.sqrt t)))
      ha.le hU.le (fun _ _ _ ↦ measureReal_nonneg) ?_ hn ?_ hsym hupper hs ht x y
    · intro σ hσ w
      exact ((hc w).comp_continuous (continuous_const.prodMk continuous_id)
        (fun z ↦ ⟨hσ, mem_univ _⟩)).aestronglyMeasurable
    · intro σ hσ w
      exact lintegral_ofReal_eq_one_of_nonnegative_integral_eq_one
        (CarnotPoint.volume G hq hqpos hspan) (p σ w) (hn σ hσ w) (hmass σ hσ w)
  · intro t ht x y
    simpa only [P, S, D, carnot_dist_eq G hq hqpos hspan,
      neg_mul, neg_div, mul_div_assoc] using hbounds (⟨t, ht⟩, x, y)

end HeatKernel.Gaussian
