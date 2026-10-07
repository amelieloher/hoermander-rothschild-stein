-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.Algebra
public import RothschildStein.Definitions.HomogeneousGroup.homogeneousDimension
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

@[expose] public section
noncomputable section
namespace RothschildStein.G2
open MeasureTheory Matrix
open scoped BigOperators
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Dilation as a diagonal linear map (BB (3.4), p. 95). -/
def dilationLinearMap (t : ℝ) : (Fin N → ℝ) →ₗ[ℝ] (Fin N → ℝ) :=
  Matrix.toLin' (Matrix.diagonal (fun j => t ^ G.weight j))

/-- The linear-map realization agrees with the dilation (BB p. 95). -/
theorem dilationLinearMap_apply (t : ℝ) (x : Fin N → ℝ) :
    dilationLinearMap G t x = G.dilate t x := by
  ext j
  simp [dilationLinearMap, Matrix.toLin'_apply, HomogeneousGroup.dilate, coordinateDilation,
    Matrix.mulVec_diagonal]

/-- The dilation determinant is t to the homogeneous dimension (BB (3.4), p. 95). -/
theorem det_dilationLinearMap (t : ℝ) :
    LinearMap.det (dilationLinearMap G t) = t ^ G.homogeneousDimension := by
  rw [dilationLinearMap, LinearMap.det_toLin', Matrix.det_diagonal,
    Finset.prod_pow_eq_pow_sum]
  rfl

/-- Pushforward of volume under a positive dilation (BB (3.4), p. 95). -/
theorem map_dilate_volume {t : ℝ} (ht : 0 < t) :
    Measure.map (G.dilate t) volume = ENNReal.ofReal ((t ^ G.homogeneousDimension)⁻¹) • volume := by
  have hd : LinearMap.det (dilationLinearMap G t) ≠ 0 := by
    rw [det_dilationLinearMap]
    exact pow_ne_zero _ ht.ne'
  have h := Real.map_linearMap_volume_pi_eq_smul_volume_pi hd
  have he : (dilationLinearMap G t : (Fin N → ℝ) → Fin N → ℝ) = G.dilate t := by
    funext x
    exact dilationLinearMap_apply G t x
  rw [he, det_dilationLinearMap, abs_of_pos (inv_pos.mpr (pow_pos ht _))] at h
  exact h

/-- The measure of any image under positive dilation scales by t^Q
(BB (3.4), p. 95). -/
theorem volume_dilate_image {t : ℝ} (ht : 0 < t) (s : Set (Fin N → ℝ)) :
    volume (G.dilate t '' s) = ENNReal.ofReal (t ^ G.homogeneousDimension) * volume s := by
  have h := Measure.addHaar_image_linearMap (volume : Measure (Fin N → ℝ))
    (dilationLinearMap G t) s
  have he : (dilationLinearMap G t : (Fin N → ℝ) → Fin N → ℝ) = G.dilate t := by
    funext x
    exact dilationLinearMap_apply G t x
  rw [he, det_dilationLinearMap, abs_of_pos (pow_pos ht _)] at h
  exact h

/-- The homogeneous dimension is positive (BB Definition 3.2, p. 95). -/
theorem homogeneousDimension_pos : 0 < G.homogeneousDimension := by
  let : Nonempty (Fin N) := ⟨⟨0, G.dimension_pos⟩⟩
  exact Finset.sum_pos (fun j _ => G.weight_pos j) Finset.univ_nonempty

/-- Every nonzero dilation is bijective (BB Proposition 3.7, p. 98). -/
theorem dilate_bijective {t : ℝ} (ht : t ≠ 0) : Function.Bijective (G.dilate t) := by
  constructor
  · exact Function.LeftInverse.injective (dilate_inv_dilate G ht)
  · intro x
    refine ⟨G.dilate t⁻¹ x, ?_⟩
    rw [dilate_dilate, mul_inv_cancel₀ ht, dilate_one]

/-- Dilation is continuous (BB p. 95). -/
theorem continuous_dilate (t : ℝ) : Continuous (G.dilate t) := by
  have he : (fun x => dilationLinearMap G t x) = G.dilate t := funext (dilationLinearMap_apply G t)
  rw [← he]
  exact (dilationLinearMap G t).continuous_of_finiteDimensional

/-- Dilation is a measurable embedding (BB p. 95). -/
theorem measurableEmbedding_dilate {t : ℝ} (ht : t ≠ 0) : MeasurableEmbedding (G.dilate t) :=
  (continuous_dilate G t).measurable.measurableEmbedding (dilate_bijective G ht).injective

/-- The Bochner integral scaling formula (BB (3.4), p. 95). -/
theorem integral_dilate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {t : ℝ} (ht : 0 < t) (f : (Fin N → ℝ) → E) :
    ∫ x, f (G.dilate t x) = (t ^ G.homogeneousDimension)⁻¹ • ∫ x, f x := by
  rw [← (measurableEmbedding_dilate G ht.ne').integral_map f, map_dilate_volume G ht,
    integral_smul_measure, ENNReal.toReal_ofReal (le_of_lt (inv_pos.mpr (pow_pos ht _)))]

end RothschildStein.G2
