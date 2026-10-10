-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.NegativePowerGraphEnergy
public import Mathlib.MeasureTheory.Integral.Prod

/-! # Finite reciprocal moments and spatial cutoff comparisons -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped ENNReal
namespace HeatKernel

/-- The real reciprocal moment on a finite measure space equals the extended
power moment used by the norm iteration. -/
theorem ofReal_integral_reciprocal_power_eq_lintegral {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {u : α → ℝ} {c p : ℝ}
    (hu : AEStronglyMeasurable u μ) (hu0 : ∀ᵐ x ∂μ, 0 ≤ u x)
    (hc : 0 < c) (hp : 0 < p) :
    ENNReal.ofReal (∫ x, (u x + c) ^ (-p) ∂μ) =
      ∫⁻ x, ‖(u x + c)⁻¹‖ₑ ^ p ∂μ := by
  have hm : AEStronglyMeasurable (fun x => (u x + c) ^ (-p)) μ :=
    ((hu.add aestronglyMeasurable_const).aemeasurable.pow_const (-p)).aestronglyMeasurable
  have hb : ∀ᵐ x ∂μ, ‖(u x + c) ^ (-p)‖ ≤ c ^ (-p) := by
    filter_upwards [hu0] with x hx
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (add_nonneg hx hc.le) _)]
    exact Real.rpow_le_rpow_of_nonpos hc (le_add_of_nonneg_left hx) (by linarith)
  have hi := (MemLp.of_bound (p := 2) hm (c ^ (-p)) hb).integrable (by norm_num)
  rw [ofReal_integral_eq_lintegral_ofReal hi
    (hu0.mono fun x hx => Real.rpow_nonneg (add_nonneg hx hc.le) _)]
  apply lintegral_congr_ae
  filter_upwards [hu0] with x hx
  calc
    ENNReal.ofReal ((u x + c) ^ (-p)) = ENNReal.ofReal (((u x + c)⁻¹) ^ p) := by
      rw [Real.rpow_neg_eq_inv_rpow]
    _ = (ENNReal.ofReal ((u x + c)⁻¹)) ^ p :=
      (ENNReal.ofReal_rpow_of_nonneg (inv_nonneg.mpr (add_nonneg hx hc.le)) hp.le).symm
    _ = ‖(u x + c)⁻¹‖ₑ ^ p := by
      rw [Real.enorm_of_nonneg (inv_nonneg.mpr (add_nonneg hx hc.le))]

/-- A positive perturbation gives an integrable reciprocal moment on every
finite product cylinder, for every positive exponent. -/
theorem integrableOn_reciprocal_spatial_moment {N : ℕ}
    {V : Set (Fin N → ℝ)} (hfinite : volume V ≠ ⊤)
    {u : ℝ × (Fin N → ℝ) → ℝ} (hu : Measurable u)
    (hu0 : ∀ z, 0 ≤ u z) {c p a b : ℝ} (hc : 0 < c) (hp : 0 < p) :
    IntegrableOn (fun t => ∫ x in V, (u (t, x) + c) ^ (-p)) (Icc a b) := by
  let : IsFiniteMeasure (volume.restrict V) := isFiniteMeasure_restrict.mpr hfinite
  have hm : AEStronglyMeasurable (fun z => (u z + c) ^ (-p))
      ((volume.restrict (Icc a b)).prod (volume.restrict V)) :=
    ((hu.add measurable_const).pow_const (-p)).aestronglyMeasurable
  have hb : ∀ᵐ z ∂(volume.restrict (Icc a b)).prod (volume.restrict V),
      ‖(u z + c) ^ (-p)‖ ≤ c ^ (-p) := Filter.Eventually.of_forall fun z => by
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (add_nonneg (hu0 z) hc.le) _)]
    exact Real.rpow_le_rpow_of_nonpos hc (le_add_of_nonneg_left (hu0 z)) (by linarith)
  have hi : Integrable (fun z => (u z + c) ^ (-p))
      ((volume.restrict (Icc a b)).prod (volume.restrict V)) :=
    (MemLp.of_bound (p := 2) hm (c ^ (-p)) hb).integrable (by norm_num)
  exact hi.integral_prod_left

/-- A unit spatial cutoff and its bounded gradient compare the localized graph
moments with the literal reciprocal moment on the outer region. The plateau
preserves the positive perturbation exactly. -/
theorem reciprocal_graph_cutoff_moment_comparisons {N q : ℕ}
    {V : Opens (Fin N → ℝ)}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    {u φ η : (Fin N → ℝ) → ℝ} {d : Fin q → (Fin N → ℝ) → ℝ}
    {c p L : ℝ} (hc : 0 < c) (hp : 0 < p) (hL : 0 ≤ L)
    (hfinite : volume (V : Set (Fin N → ℝ)) ≠ ⊤)
    (hu : AEStronglyMeasurable u volume) (hu0 : ∀ᵐ x ∂volume, 0 ≤ u x)
    (hη : MemLp η 2 volume) (hηunit : ∀ x, η x ∈ Icc (0 : ℝ) 1)
    (hd : ∀ i, MemLp (d i) 2 volume) (hdL : ∀ x, coordinateNormSq (fun i => d i x) ≤ L)
    (hactive : ∀ x, η x ≠ 0 ∨ (∃ i, d i x ≠ 0) → x ∈ (V : Set (Fin N → ℝ)))
    (hplateau : ∀ x, η x ≠ 0 ∨ (∃ i, d i x ≠ 0) → φ x = 1)
    (z : zeroBoundaryGraph V X)
    (hz : ∀ᵐ x ∂volume, 0 ≤ (z : GradientSpace (N := N) ⊤ q).fst x)
    (hval : (z : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume] fun x => u x * φ x) :
    (∫ x, η x ^ 2 * ((z : GradientSpace (N := N) ⊤ q).fst x + c) ^ (-p)) ≤
        ∫ x in (V : Set (Fin N → ℝ)), (u x + c) ^ (-p) ∧
      (∫ x, ((z : GradientSpace (N := N) ⊤ q).fst x + c) ^ (-p) *
        coordinateNormSq (fun i => d i x)) ≤
        L * (∫ x in (V : Set (Fin N → ℝ)), (u x + c) ^ (-p)) := by
  let f := fun x => (u x + c) ^ (-p)
  have hfi : IntegrableOn f (V : Set (Fin N → ℝ)) := by
    let : IsFiniteMeasure (volume.restrict (V : Set (Fin N → ℝ))) :=
      isFiniteMeasure_restrict.mpr hfinite
    apply (MemLp.of_bound (p := 2)
      ((((hu.add aestronglyMeasurable_const).aemeasurable.pow_const
        (-p)).aestronglyMeasurable).mono_measure Measure.restrict_le_self)
      (c ^ (-p)) ?_).integrable (by norm_num)
    filter_upwards [ae_restrict_of_ae hu0] with x hx
    change ‖(u x + c) ^ (-p)‖ ≤ c ^ (-p)
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (add_nonneg hx hc.le) _)]
    exact Real.rpow_le_rpow_of_nonpos hc (le_add_of_nonneg_left hx) (by linarith)
  have hfind := (integrable_indicator_iff V.isOpen.measurableSet).mpr hfi
  have hv : AEStronglyMeasurable ((z : GradientSpace (N := N) ⊤ q).fst) volume := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using
      (Lp.memLp (z : GradientSpace (N := N) ⊤ q).fst).aestronglyMeasurable
  have hEi := integrable_weighted_shifted_nonpositive_power hc (by linarith : -p ≤ 0)
    hη.integrable_sq hv hz
  have hdi : Integrable (fun x => coordinateNormSq (fun i => d i x)) volume :=
    integrable_finsetSum _ (fun i _ => (hd i).integrable_sq)
  have hRi : Integrable (fun x => ((z : GradientSpace (N := N) ⊤ q).fst x + c) ^ (-p) *
      coordinateNormSq (fun i => d i x)) volume := by
    simpa only [mul_comm] using
      integrable_weighted_shifted_nonpositive_power hc (by linarith : -p ≤ 0) hdi hv hz
  have hE := integral_mono_ae hEi hfind (by
    filter_upwards [hval, hu0] with x hx hn
    by_cases he : η x = 0
    · simp only [he, zero_pow (by decide : 2 ≠ 0), zero_mul]
      by_cases hxV : x ∈ (V : Set (Fin N → ℝ))
      · rw [indicator_of_mem hxV]
        exact Real.rpow_nonneg (add_nonneg hn hc.le) _
      · simp only [indicator_of_notMem hxV, le_refl]
    · rw [indicator_of_mem (hactive x (Or.inl he)), hx, hplateau x (Or.inl he), mul_one]
      have hs : η x ^ 2 ≤ 1 := by
        obtain ⟨h0, h1⟩ := hηunit x
        nlinarith
      exact (mul_le_mul_of_nonneg_right hs (Real.rpow_nonneg (add_nonneg hn hc.le) _)).trans_eq
        (one_mul _))
  have hR := integral_mono_ae hRi (hfind.const_mul L) (by
    filter_upwards [hval, hu0] with x hx hn
    by_cases he : ∃ i, d i x ≠ 0
    · rw [indicator_of_mem (hactive x (Or.inr he)), hx, hplateau x (Or.inr he), mul_one]
      exact (mul_le_mul_of_nonneg_left (hdL x)
        (Real.rpow_nonneg (add_nonneg hn hc.le) _)).trans_eq (mul_comm _ _)
    · have hz' : ∀ i, d i x = 0 := fun i => not_ne_iff.mp (fun h => he ⟨i, h⟩)
      simp only [coordinateNormSq, hz', zero_pow (by decide : 2 ≠ 0),
        Finset.sum_const_zero, mul_zero]
      apply mul_nonneg hL
      by_cases hxV : x ∈ (V : Set (Fin N → ℝ))
      · rw [indicator_of_mem hxV]
        exact Real.rpow_nonneg (add_nonneg hn hc.le) _
      · simp only [indicator_of_notMem hxV, le_refl])
  rw [integral_indicator V.isOpen.measurableSet] at hE
  rw [integral_const_mul, integral_indicator V.isOpen.measurableSet] at hR
  exact ⟨hE, hR⟩

end HeatKernel
