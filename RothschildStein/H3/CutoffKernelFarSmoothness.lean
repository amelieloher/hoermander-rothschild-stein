-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.CutoffFarDifference
public import RothschildStein.H3.KernelRightIncrement
public import RothschildStein.H3.CutoffKernelMeasurability
public import RothschildStein.H3.KernelDerivativeProperties

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set
variable {N q : ℕ} {G : HomogeneousGroup N}

/-- Case I of the cutoff-kernel difference estimate, with exact geometry,
cutoff, and first-seminorm dependence. -/
theorem cutoffGroupKernel_far_difference_of_controlNorm
    {Y : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ)}
    (H : G2.ControlNormConclusion G driftWeight Y)
    (hY : ∀ i, ContinuousOn (Y i) {0}ᶜ)
    (hhomY : ∀ i, G2.IsHomogeneousField G (Y i) (if i = 0 then 2 else 1))
    {T χ : (Fin N → ℝ) → ℝ} (hT : ContDiffOn ℝ (⊤ : ℕ∞) T {0}ᶜ)
    {γ : ℝ} (hγ : γ ≤ 0)
    (hhom : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 → T (G.dilate t x) = t ^ γ * T x)
    {R L : ℝ} (hR : 0 < R) (hL : 0 ≤ L)
    (hχ : ∀ z, 0 ≤ χ z ∧ χ z ≤ 1)
    (hχmod : ∀ a b, |χ a - χ b| ≤ L * G2.gaugeDistance G H.norm a b)
    (hsupp : ∀ z, R < H.norm z → χ z = 0)
    {x₀ x y : Fin N → ℝ} (hne : x₀ ≠ x)
    (hfar : 4 * G2.gaugeDistance G H.norm x₀ x ≤ G2.gaugeDistance G H.norm x₀ y) :
    |cutoffGroupKernel G χ T x₀ y - cutoffGroupKernel G χ T x y| ≤
      ((2 : ℝ) ^ (2 - γ) * max 0 (frameCoefficientSphereBound H.norm Y) +
        (2 : ℝ) ^ (-γ) * (2 * R * L)) * kernelDerivativeBound H.norm T 1 *
        G2.gaugeDistance G H.norm x₀ x *
          G2.gaugeDistance G H.norm x₀ y ^ (γ - 1) := by
  let X := G.mul (G.inv y) x₀
  let Z := G.mul (G.inv x₀) x
  let W := G.mul (G.inv y) x
  let ρ := G2.gaugeDistance G H.norm x₀ y
  let δ := G2.gaugeDistance G H.norm x₀ x
  let Λ := kernelDerivativeBound H.norm T 1
  let I := (2 : ℝ) ^ (2 - γ) * max 0 (frameCoefficientSphereBound H.norm Y)
  have hXρ : H.norm X = ρ := rfl
  have hZ : H.norm Z = δ := (G2.gaugeDistance_symmetric G H.norm H.symmetric x x₀).symm
  have hsep : 4 * δ ≤ ρ := hfar
  have hδ0 : δ ≠ 0 := fun hz => hne ((G2.gaugeDistance_eq_zero_iff G H.norm.gauge x₀ x).mp hz)
  have hδ : 0 < δ := lt_of_le_of_ne (H.norm.gauge.2.1 _) hδ0.symm
  have hρ : 0 < ρ := by linarith
  have hXZ : G.mul X Z = W := by
    dsimp only [X, Z, W]
    rw [G2.mul_assoc, ← G2.mul_assoc G x₀, G2.mul_inv, G2.zero_mul]
  have hZW : G2.gaugeDistance G H.norm X W = δ :=
    G2.gaugeDistance_leftInvariant G H.norm x₀ x (G.inv y)
  have htriangle : ρ ≤ δ + H.norm W := by
    have ht := G2.gaugeDistance_triangle G H.norm x₀ y x
    simpa only [H.constant_one, one_mul, G2.gaugeDistance, ρ, δ, W] using ht
  have hhalf : ρ / 2 ≤ H.norm W := by linarith
  have hW : W ≠ 0 := by
    intro hw
    rw [hw, (H.norm.gauge.2.2.1 0).mpr rfl] at hhalf
    linarith
  have hΛ : 0 ≤ Λ := (kernelDerivativeBound_properties H.norm.gauge hT 1).1
  have hSphere : kernelSphereBound H.norm T ≤ Λ := by
    rw [← kernelDerivativeBound_zero H.norm T]
    exact kernelDerivativeBound_mono H.norm T (by omega)
  have hsize : |T W| ≤ Λ * (2 : ℝ) ^ (-γ) * ρ ^ γ := by
    have hb := kernelSphereBound_homogeneous H.norm.gauge hT.continuousOn hhom W hW
    have hp := Real.rpow_le_rpow_of_nonpos (by linarith : 0 < ρ / 2) hhalf hγ
    have he : (ρ / 2) ^ γ = (2 : ℝ) ^ (-γ) * ρ ^ γ := by
      rw [Real.div_rpow hρ.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
      ring
    exact hb.trans ((mul_le_mul hSphere (hp.trans_eq he)
      (Real.rpow_nonneg (H.norm.gauge.2.1 W) _) hΛ).trans_eq (by ring))
  have hinc : |T X - T W| ≤ I * Λ * δ * ρ ^ (γ - 1) := by
    have hz : Z ≠ 0 := by intro hz; rw [hz, (H.norm.gauge.2.2.1 0).mpr rfl] at hZ; linarith
    have hi := kernel_right_increment_of_controlNorm H hY hhomY hT (by linarith) hhom (x := X) (y := Z) hz
      (by rw [hZ]; exact hsep)
    rw [hXZ, hZ, hXρ] at hi
    rw [abs_sub_comm]
    apply hi.trans
    dsimp only [I, Λ]
    gcongr
    exact le_max_right 0 _
  have hactive : χ X ≠ 0 ∨ χ W ≠ 0 → ρ ≤ 2 * R := by
    intro ha
    rcases ha with ha | ha
    · have hX : ρ ≤ R := le_of_not_gt (fun hr => ha (hsupp X hr))
      linarith
    · have hW' : H.norm W ≤ R := le_of_not_gt (fun hr => ha (hsupp W hr))
      linarith
  change |χ X * T X - χ W * T W| ≤
    (I + (2 : ℝ) ^ (-γ) * (2 * R * L)) * Λ * δ * ρ ^ (γ - 1)
  exact cutoff_far_difference_bound hρ hδ.le hR.le hL (by positivity)
    hΛ (hχ X) (hχ W) (by simpa only [hZW] using hχmod X W) hinc hsize hactive

end RothschildStein.H3
