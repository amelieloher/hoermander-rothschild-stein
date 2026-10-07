-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.FieldSphereDerivativeBound
public import RothschildStein.H3.HomogeneousIncrementLocal

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace RothschildStein.H3
open G2
variable {N q : ℕ} {G : HomogeneousGroup N}

/-- A frame constant defined by actual unit-sphere coefficient
maxima; it has no dependence on the scalar kernel. -/
def frameCoefficientSphereBound (ν : (Fin N → ℝ) → ℝ)
    (Y : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ)) : ℝ :=
  (∑ i : Fin q, kernelSphereBound ν (fun x => ∑ j : Fin N, |Y i.succ x j|)) +
    kernelSphereBound ν (fun x => ∑ j : Fin N, |Y 0 x j|)

/-- Case I precursor. The actual Λ₁ controls the right
kernel increment with a constant depending only on the frame and degree.
It includes the weight-two drift and the exact factor-four separation. -/
theorem kernel_right_increment_of_controlNorm
    {Y : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ)}
    (H : ControlNormConclusion G driftWeight Y)
    (hY : ∀ i, ContinuousOn (Y i) {0}ᶜ)
    (hhomY : ∀ i, IsHomogeneousField G (Y i) (if i = 0 then 2 else 1))
    {T : (Fin N → ℝ) → ℝ} (hT : ContDiffOn ℝ (⊤ : ℕ∞) T {0}ᶜ)
    {a : ℝ} (ha : a < 1)
    (hhom : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 → T (G.dilate t x) = t ^ a * T x)
    {x y : Fin N → ℝ} (hy : y ≠ 0) (hsep : 4 * H.norm y ≤ H.norm x) :
    |T (G.mul x y) - T x| ≤ (2 : ℝ) ^ (2 - a) *
      frameCoefficientSphereBound H.norm Y * kernelDerivativeBound H.norm T 1 *
        H.norm y * H.norm x ^ (a - 1) := by
  have hb := homogeneous_right_increment_sphere_bound_of_controlNorm H hY hhomY
    (hT.of_le (by simp)) ha hhom hy hsep
  have hs : (∑ i : Fin q, kernelSphereBound H.norm (fieldDerivative (Y i.succ) T)) +
      kernelSphereBound H.norm (fieldDerivative (Y 0) T) ≤
      frameCoefficientSphereBound H.norm Y * kernelDerivativeBound H.norm T 1 := by
    calc
      _ ≤ (∑ i : Fin q, kernelSphereBound H.norm
          (fun x => ∑ j : Fin N, |Y i.succ x j|) * kernelDerivativeBound H.norm T 1) +
          kernelSphereBound H.norm (fun x => ∑ j : Fin N, |Y 0 x j|) *
            kernelDerivativeBound H.norm T 1 :=
        add_le_add (Finset.sum_le_sum fun i _ =>
          fieldSphereBound_le_kernelDerivativeBound H.norm.gauge hT (Y i.succ) (hY i.succ))
          (fieldSphereBound_le_kernelDerivativeBound H.norm.gauge hT (Y 0) (hY 0))
      _ = _ := by rw [← Finset.sum_mul]; unfold frameCoefficientSphereBound; ring
  apply hb.trans
  have hy0 : 0 ≤ H.norm y := H.norm.gauge.2.1 y
  have hx0 : 0 ≤ H.norm x := H.norm.gauge.2.1 x
  have he := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hs
        (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (2 - a))) hy0)
    (Real.rpow_nonneg hx0 (a - 1))
  convert he using 1
  ring

end RothschildStein.H3
