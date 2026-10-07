-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.TypeZero
public import RothschildStein.G2.DilationMeasure
public import Mathlib.MeasureTheory.Integral.Bochner.Set

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory
open RothschildStein.G2
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Every positive truncation transforms covariantly under dilation.
The degree minus Q cancels the volume Jacobian (BB pp. 356–357). -/
theorem principalValue_truncation_dilation_data
    {ν k : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    (hk : ∀ t : ℝ, 0 < t → ∀ w : Fin N → ℝ, w ≠ 0 →
      k (G.dilate t w) = t ^ (-(G.homogeneousDimension : ℝ)) * k w)
    (u : (Fin N → ℝ) → ℝ) (x : Fin N → ℝ)
    {t ε : ℝ} (ht : 0 < t) (hε : 0 < ε) :
    ((∫ y in {y | ε < ν (G.mul (G.inv y) x)},
      u (G.dilate t y) * k (G.mul (G.inv y) x)) =
    ∫ y in {y | t * ε < ν (G.mul (G.inv y) (G.dilate t x))},
      u y * k (G.mul (G.inv y) (G.dilate t x))) ∧
    (IntegrableOn (fun y => u (G.dilate t y) * k (G.mul (G.inv y) x))
      {y | ε < ν (G.mul (G.inv y) x)} volume ↔
     IntegrableOn (fun y => u y * k (G.mul (G.inv y) (G.dilate t x)))
      {y | t * ε < ν (G.mul (G.inv y) (G.dilate t x))} volume) := by
  let A : Set (Fin N → ℝ) := {y | ε < ν (G.mul (G.inv y) x)}
  let B : Set (Fin N → ℝ) :=
    {y | t * ε < ν (G.mul (G.inv y) (G.dilate t x))}
  let F : (Fin N → ℝ) → ℝ :=
    B.indicator (fun y => u y * k (G.mul (G.inv y) (G.dilate t x)))
  have hrel (y : Fin N → ℝ) :
      G.mul (G.inv (G.dilate t y)) (G.dilate t x) =
        G.dilate t (G.mul (G.inv y) x) := by
    rw [inv_dilate G ht, dilate_product G ht]
  have hB : MeasurableSet B :=
    isOpen_lt continuous_const
      (hν.1.comp ((continuous_mul G).comp ((continuous_inv G).prodMk continuous_const)))
      |>.measurableSet
  have hA : MeasurableSet A :=
    isOpen_lt continuous_const
      (hν.1.comp ((continuous_mul G).comp ((continuous_inv G).prodMk continuous_const)))
      |>.measurableSet
  have hf (y : Fin N → ℝ) :
      F (G.dilate t y) = (t ^ G.homogeneousDimension)⁻¹ *
        A.indicator (fun y => u (G.dilate t y) * k (G.mul (G.inv y) x)) y := by
    have hb : G.dilate t y ∈ B ↔ y ∈ A := by
      change t * ε < ν (G.mul (G.inv (G.dilate t y)) (G.dilate t x)) ↔
        ε < ν (G.mul (G.inv y) x)
      rw [hrel, hν.2.2.2 t ht, mul_lt_mul_iff_right₀ ht]
    by_cases hy : y ∈ A
    · have hn : G.mul (G.inv y) x ≠ 0 := by
        intro hz
        have hv := (hν.2.2.1 0).mpr rfl
        have hp : ε < ν (G.mul (G.inv y) x) := hy
        rw [hz, hv] at hp
        exact (not_lt_of_ge hε.le) hp
      simp only [F, indicator_of_mem (hb.mpr hy), indicator_of_mem hy]
      rw [hrel, hk t ht _ hn, Real.rpow_neg ht.le, Real.rpow_natCast]
      ring
    · simp only [F, indicator_of_notMem (fun h => hy (hb.mp h)),
        indicator_of_notMem hy]
      ring
  have hi := integral_dilate G ht F
  simp_rw [hf] at hi
  rw [integral_const_mul, integral_indicator hA, integral_indicator hB] at hi
  change (t ^ G.homogeneousDimension)⁻¹ * _ =
    (t ^ G.homogeneousDimension)⁻¹ * _ at hi
  refine ⟨mul_left_cancel₀ (inv_ne_zero (pow_ne_zero _ ht.ne')) hi, ?_⟩
  have hid := (measurableEmbedding_dilate G ht.ne').integrable_map_iff (g := F) (μ := volume)
  rw [map_dilate_volume G ht, integrable_smul_measure
    (ENNReal.ofReal_pos.mpr (inv_pos.mpr (pow_pos ht _))).ne'
    ENNReal.ofReal_ne_top] at hid
  have heF : (F ∘ G.dilate t) = fun y => (t ^ G.homogeneousDimension)⁻¹ *
      A.indicator (fun y => u (G.dilate t y) * k (G.mul (G.inv y) x)) y :=
    funext hf
  rw [heF, integrable_const_mul_iff
    (isUnit_iff_ne_zero.mpr (inv_ne_zero (pow_ne_zero _ ht.ne'))),
    integrable_indicator_iff hA] at hid
  have hFin : Integrable F volume ↔
      IntegrableOn (fun y => u y * k (G.mul (G.inv y) (G.dilate t x))) B volume :=
    integrable_indicator_iff hB
  exact hid.symm.trans hFin

end RothschildStein.H3
