-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.LocalMeanValue
public import RothschildStein.H3.C1FieldHomogeneity
public import RothschildStein.H3.HomogeneousIncrementAlgebra
public import RothschildStein.G2.ControlMeasure
public import RothschildStein.G2.GaugeConsequences

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace RothschildStein.H3
open G2
variable {N q : ℕ} {G : HomogeneousGroup N}

/-- The control ball of radius twice the smaller increment
stays away from the identity, with gauge at least half the base gauge.
This is the punctured buffer needed by the local mean value theorem. -/
theorem gauge_lower_on_increment_ball_of_controlNorm
    {Y : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ)}
    (H : ControlNormConclusion G driftWeight Y) {x y z : Fin N → ℝ}
    (hsep : 4 * H.norm y ≤ H.norm x)
    (hz : (controlDistance univ driftWeight Y x z).toReal ≤ 2 * H.norm y) :
    H.norm x / 2 ≤ H.norm z := by
  have ht := gaugeDistance_triangle G H.norm x 0 z
  have hinv : G.inv (0 : Fin N → ℝ) = 0 := G2.inv_zero G
  have hdist : gaugeDistance G H.norm z 0 = H.norm z := by
    simp only [gaugeDistance, hinv, G2.zero_mul]
  have hbase : gaugeDistance G H.norm x 0 = H.norm x := by
    simp only [gaugeDistance, hinv, G2.zero_mul]
  have hsym := gaugeDistance_symmetric G H.norm H.symmetric x z
  rw [H.constant_one, one_mul, hbase, hdist, ← hsym] at ht
  rw [controlDistance_toReal_of_controlNorm G H] at hz
  linarith

/-- The first homogeneous increment has the complete local
mean-value bound in terms of the actual directional sphere maxima.
The drift-square term is retained (BB Proposition 6.25, pp. 272–273). -/
theorem homogeneous_right_increment_local_of_controlNorm
    {Y : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ)}
    (H : ControlNormConclusion G driftWeight Y)
    (hY : ∀ i, ContinuousOn (Y i) {0}ᶜ)
    (hhomY : ∀ i, G2.IsHomogeneousField G (Y i) (if i = 0 then 2 else 1))
    {f : (Fin N → ℝ) → ℝ} (hf : ContDiffOn ℝ 1 f {0}ᶜ)
    {a : ℝ} (ha : a < 1)
    (hhom : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 → f (G.dilate t x) = t ^ a * f x)
    {x y : Fin N → ℝ} (hy : y ≠ 0) (hsep : 4 * H.norm y ≤ H.norm x) :
    |f (G.mul x y) - f x| ≤
      (2 * H.norm y) * (∑ i : Fin q,
        kernelSphereBound H.norm (fieldDerivative (Y i.succ) f) *
          (H.norm x / 2) ^ (a - 1)) +
      (2 * H.norm y) ^ 2 *
        (kernelSphereBound H.norm (fieldDerivative (Y 0) f) *
          (H.norm x / 2) ^ (a - 2)) := by
  have hry : 0 < H.norm y := gauge_pos H.norm.gauge hy
  have hrx : 0 < H.norm x := by linarith
  have hxy : (controlDistance univ driftWeight Y x (G.mul x y)).toReal = H.norm y := by
    rw [controlDistance_toReal_of_controlNorm G H,
      gaugeDistance_symmetric G H.norm H.symmetric]
    simp only [gaugeDistance, ← G2.mul_assoc, G2.inv_mul, G2.zero_mul]
  have hball (z : Fin N → ℝ)
      (hz : (controlDistance univ driftWeight Y x z).toReal ≤ 2 * H.norm y) :
      H.norm x / 2 ≤ H.norm z := gauge_lower_on_increment_ball_of_controlNorm H hsep hz
  have hz0 (z : Fin N → ℝ)
      (hz : (controlDistance univ driftWeight Y x z).toReal ≤ 2 * H.norm y) : z ≠ 0 := by
    intro he
    have hh := hball z hz
    rw [he, (H.norm.gauge.2.2.1 0).mpr rfl] at hh
    linarith
  apply local_meanValue_of_controlNorm H isOpen_compl_singleton hf
    (by rw [hxy]; linarith) (fun z hz => hz0 z hz)
  · intro z hz i
    have hdeg : G2.IsHomogeneousField G (Y i.succ) 1 := by
      simpa using hhomY i.succ
    have hp := fieldDerivative_sphere_power_bound_C1 G H.norm.gauge hf hhom
      (Y i.succ) (hY i.succ) hdeg z (hz0 z hz)
    exact hp.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos (by linarith) (hball z hz) (by linarith))
      (kernelSphereBound_continuous H.norm.gauge
        (fieldDerivative_continuousOn_C1 hf (hY i.succ))).1)
  · intro z hz
    have hdeg : G2.IsHomogeneousField G (Y 0) 2 := by simpa using hhomY 0
    have hp := fieldDerivative_sphere_power_bound_C1 G H.norm.gauge hf hhom
      (Y 0) (hY 0) hdeg z (hz0 z hz)
    exact hp.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos (by linarith) (hball z hz) (by linarith))
      (kernelSphereBound_continuous H.norm.gauge
        (fieldDerivative_continuousOn_C1 hf (hY 0))).1)

/-- The directional sphere maxima give a first-increment
bound at scale gauge(y) times gauge(x) to the degree a-1. -/
theorem homogeneous_right_increment_sphere_bound_of_controlNorm
    {Y : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ)}
    (H : ControlNormConclusion G driftWeight Y)
    (hY : ∀ i, ContinuousOn (Y i) {0}ᶜ)
    (hhomY : ∀ i, G2.IsHomogeneousField G (Y i) (if i = 0 then 2 else 1))
    {f : (Fin N → ℝ) → ℝ} (hf : ContDiffOn ℝ 1 f {0}ᶜ)
    {a : ℝ} (ha : a < 1)
    (hhom : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 → f (G.dilate t x) = t ^ a * f x)
    {x y : Fin N → ℝ} (hy : y ≠ 0) (hsep : 4 * H.norm y ≤ H.norm x) :
    |f (G.mul x y) - f x| ≤ (2 : ℝ) ^ (2 - a) *
      ((∑ i : Fin q, kernelSphereBound H.norm (fieldDerivative (Y i.succ) f)) +
        kernelSphereBound H.norm (fieldDerivative (Y 0) f)) *
      H.norm y * H.norm x ^ (a - 1) := by
  have hb := homogeneous_right_increment_local_of_controlNorm H hY hhomY hf ha hhom hy hsep
  have hr : 0 < H.norm y := gauge_pos H.norm.gauge hy
  have hR : 0 < H.norm x := by linarith
  have hD : 0 ≤ kernelSphereBound H.norm (fieldDerivative (Y 0) f) :=
    (kernelSphereBound_continuous H.norm.gauge
      (fieldDerivative_continuousOn_C1 hf (hY 0))).1
  have halg := homogeneous_increment_drift_algebra (a := a)
    (M := ∑ i : Fin q, kernelSphereBound H.norm (fieldDerivative (Y i.succ) f))
    hR hr.le hsep hD
  apply hb.trans
  convert halg using 1
  simp only [← Finset.sum_mul]
  ring

end RothschildStein.H3
