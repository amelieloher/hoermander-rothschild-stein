-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.ReverseHolderCutoffBudgetAssembly
public import HeatKernel.Moser.ReverseHolderRepresentativeLocalization
public import HeatKernel.Moser.MeanValueSmoothSpatialWeights
public import HeatKernel.Moser.MeanValueNonnegativeCylinder
public import HeatKernel.Form.MatrixCoefficientBounds
import Mathlib.Tactic
import all Mathlib.Basic.Real.Basic
import all Mathlib.Analysis.Normed.Group.Real
import all Mathlib.Analysis.Normed.Field.Basic

/-! Smooth spatial cutoffs supply backward budgets for the common weak solution. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory TopologicalSpace RothschildStein
namespace HeatKernel

/-- Smooth nested spatial cutoffs and compact-cylinder energy bounds supply
the complete backward budget, with the literal original solution as its outer
moment. The coefficient matrix and the common gradient are used throughout.
No global integrability of the original value or gradient is required. -/
theorem WeakSolutionEnergyInterface.exists_reverse_holder_smooth_cutoff_budgets {N q : ℕ}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    {coeff : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ}
    {I : Opens ℝ} {U V : Opens (Fin N → ℝ)}
    {u : ℝ → (Fin N → ℝ) → ℝ} {g : Fin q → ℝ → (Fin N → ℝ) → ℝ}
    (h : WeakSolutionEnergyInterface X coeff I U u g)
    (hum : AEStronglyMeasurable (Function.uncurry u)
      (volume.restrict ((I : Set ℝ) ×ˢ (U : Set (Fin N → ℝ)))))
    (hu0 : ∀ᵐ z : ℝ × (Fin N → ℝ)
      ∂volume.restrict ((I : Set ℝ) ×ˢ (U : Set (Fin N → ℝ))), 0 ≤ u z.1 z.2)
    (ha : ∀ i j, Measurable (fun z : ℝ × (Fin N → ℝ) => coeff z.1 z.2 i j))
    {ell upper c p A B a b H L : ℝ} (hell : 0 < ell) (hupper : 0 ≤ upper)
    (hc : 0 < c) (hp : 0 < p) (hp2 : p ≤ 1 / 2)
    (hbound : ∀ᵐ z : ℝ × (Fin N → ℝ) ∂volume,
      (∀ i j, coeff z.1 z.2 i j = coeff z.1 z.2 j i) ∧ ∀ ξ : Fin q → ℝ,
        ell * coordinateNormSq ξ ≤ matrixEnergy (coeff z.1 z.2) ξ ∧
        matrixEnergy (coeff z.1 z.2) ξ ≤ upper * coordinateNormSq ξ)
    (hJI : Icc A B ⊆ (I : Set ℝ)) (hab : a < b) (hAa : A < a) (hbB : b < B)
    {φ η : (Fin N → ℝ) → ℝ} {K : Set (Fin N → ℝ)}
    (hK : IsCompact K) (hKU : K ⊆ (U : Set (Fin N → ℝ)))
    (hφK : tsupport φ ⊆ K) (hφunit : ∀ x, φ x ∈ Icc (0 : ℝ) 1)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hcη : HasCompactSupport η)
    (hηV : tsupport η ⊆ (V : Set (Fin N → ℝ)))
    (hηunit : ∀ x, η x ∈ Icc (0 : ℝ) 1)
    (hplateau : ∀ x ∈ tsupport η, φ x = 1 ∧ ∀ i, fieldDerivative (X i) φ x = 0)
    (hL : 0 ≤ L) (hdL : ∀ x, coordinateNormSq (fun i => fieldDerivative (X i) η x) ≤ L)
    {v : ℝ → zeroBoundaryGraph V X} {F : ℝ → (zeroBoundaryGraph V X →L[ℝ] ℝ)}
    (hpair : IsZeroBoundaryWeakCutoffEnergyTimePair V X coeff (Icc A B) u g φ
      (fun i => fieldDerivative (X i) φ) v F)
    {θ : ℝ → ℝ} (hθ : ContDiff ℝ 1 θ) (hθb : θ b = 0)
    (hθunit : ∀ t ∈ Icc a b, θ t ∈ Icc (0 : ℝ) 1)
    (hH : 0 ≤ H) (hθd : ∀ t ∈ Icc a b, -(deriv (fun s => θ s ^ 2) t) ≤ H) :
    ∃ (Y : ℝ → zeroBoundaryGraph V X) (e D R : ℝ → ℝ),
      HasBackwardCutoffEnergyBudgets a b ell H (upper * L) L Y θ e D R
        (fun t => ∫ x in K, (u t x + c) ^ p) ∧
      ∀ᵐ t ∂volume.restrict (Icc a b), (Y t : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume]
        fun x => η x * (u t x + c) ^ (p / 2) := by
  classical
  have hsub : Icc a b ⊆ Icc A B := fun t ht => ⟨hAa.le.trans ht.1, ht.2.trans hbB.le⟩
  have hJab : Icc a b ⊆ (I : Set ℝ) := hsub.trans hJI
  let uK := fun t => K.indicator (u t)
  let gK := fun i t => K.indicator (g i t)
  have hφzero (x : Fin N → ℝ) (hx : x ∉ K) : φ x = 0 := by
    by_contra hne
    exact hx (hφK (subset_tsupport φ (Function.mem_support.mpr hne)))
  have hkzero (i : Fin q) (x : Fin N → ℝ) (hx : x ∉ K) : fieldDerivative (X i) φ x = 0 := by
    by_contra hne
    exact hx (hφK (S.tsupport_fieldDerivative_subset (X i) φ
      (subset_tsupport _ (Function.mem_support.mpr hne))))
  have hpairK := hpair.indicator_representatives hφzero hkzero
  obtain ⟨huK, hgK, _⟩ := h.memLp_indicator_representatives hum isCompact_Icc hJab hK hKU
  have hu0JK : ∀ᵐ z : ℝ × (Fin N → ℝ)
      ∂(volume.restrict (Icc a b)).prod (volume.restrict K), 0 ≤ u z.1 z.2 := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact hu0.filter_mono (ae_mono (Measure.restrict_mono (prod_mono hJab hKU) le_rfl))
  have huK0 : ∀ᵐ z : ℝ × (Fin N → ℝ)
      ∂(volume.restrict (Icc a b)).prod volume, 0 ≤ uK z.1 z.2 := by
    have hm : (volume.restrict (Icc a b)).prod (volume.restrict K) =
        ((volume.restrict (Icc a b)).prod volume).restrict (univ ×ˢ K) := by
      simpa only [Measure.restrict_univ] using Measure.prod_restrict
        (μ := volume.restrict (Icc a b)) (ν := volume) univ K
    rw [hm] at hu0JK
    have hn := (ae_restrict_iff' (MeasurableSet.univ.prod hK.measurableSet)).mp hu0JK
    filter_upwards [hn] with z hz
    by_cases hx : z.2 ∈ K
    · simpa only [uK, indicator_of_mem hx] using hz ⟨mem_univ _, hx⟩
    · simp only [uK, indicator_of_notMem hx, le_refl]
  have hz : ∀ᵐ t ∂volume.restrict (Icc a b), ∀ᵐ x ∂volume,
      0 ≤ (v t : GradientSpace (N := N) ⊤ q).fst x := by
    have hn := (ae_ae_nonneg_of_nonneg_on_product I.isOpen.measurableSet
      U.isOpen.measurableSet hu0).filter_mono
        (ae_mono (Measure.restrict_le_self : volume.restrict (Icc a b) ≤ volume))
    filter_upwards [hpair.2.2.1.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl)),
      self_mem_ae_restrict measurableSet_Icc, hn] with t ht htm hnt
    filter_upwards [ht, hnt] with x hx hnx
    rw [hx]
    by_cases hzero : φ x = 0
    · simp only [hzero, mul_zero, le_refl]
    · exact mul_nonneg (hnx (hJab htm)
        (hKU (hφK (subset_tsupport φ (Function.mem_support.mpr hzero))))) (hφunit x).1
  have hcoeff : ∀ᵐ t ∂volume.restrict (Icc a b),
      (∀ i j, AEStronglyMeasurable (fun x => coeff t x i j) volume) ∧
      (∀ i j, ∀ᵐ x ∂volume, ‖coeff t x i j‖ ≤ upper) ∧
      (∀ᵐ x ∂volume, (∀ i j, coeff t x i j = coeff t x j i) ∧ ∀ ξ : Fin q → ℝ,
        ell * coordinateNormSq ξ ≤ matrixEnergy (coeff t x) ξ ∧
        matrixEnergy (coeff t x) ξ ≤ upper * coordinateNormSq ξ) := by
    have hs := (Measure.ae_ae_of_ae_prod hbound).filter_mono
      (ae_mono (Measure.restrict_le_self : volume.restrict (Icc a b) ≤ volume))
    filter_upwards [hs] with t ht
    refine ⟨fun i j => ((ha i j).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable, ?_, ht⟩
    intro i j
    filter_upwards [ht] with x hx
    exact norm_matrix_entry_le_of_elliptic_bounds (coeff t x) hell.le hx.1 hx.2 i j
  let W := WeakSolutionSpatialWeight.ofSmoothUnitCutoff V X hX hη hcη hηV hηunit
  obtain ⟨S, hS, hSd⟩ := exists_smooth_square_spatial_weight V X hX hη hcη hηV hηunit
  have hcsq : HasCompactSupport (fun x => η x ^ 2) := by
    simpa only [pow_two, Pi.mul_def] using hcη.mul_left (f := η)
  have hssq : tsupport (fun x => η x ^ 2) ⊆ (V : Set (Fin N → ℝ)) := by
    simpa only [pow_two] using (tsupport_mul_subset_left (f := η) (g := η)).trans hηV
  obtain ⟨w, hw, hdw⟩ := exists_zeroBoundaryGraph_smooth_compact_constant V X hX hη hcη hηV 1
  obtain ⟨ws, hws, hdws⟩ := exists_zeroBoundaryGraph_smooth_compact_constant
    V X hX (hη.pow 2) hcsq hssq 1
  have hwW : (w : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume] W.toFun := by
    change (w : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume] η
    simpa only [mul_one] using hw
  have hdwW : ∀ i, (w : GradientSpace (N := N) ⊤ q).snd i =ᵐ[volume] W.gradient i := by
    intro i
    change (w : GradientSpace (N := N) ⊤ q).snd i =ᵐ[volume] fieldDerivative (X i) η
    simpa only [mul_one] using hdw i
  have hwsS : (ws : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume] S.toFun := by
    filter_upwards [hws] with x hx
    rw [hx, mul_one, hS]
  have hdwsS : ∀ i, (ws : GradientSpace (N := N) ⊤ q).snd i =ᵐ[volume] S.gradient i := by
    intro i
    filter_upwards [hdws i] with x hx
    rw [hx, mul_one, hSd, fieldDerivative_smooth_cutoff_sq X hη]
  have hSint : Integrable S.toFun volume := by
    apply ((hη.continuous.pow 2).integrable_of_hasCompactSupport hcsq).congr
    exact Filter.Eventually.of_forall fun x => (hS x).symm
  have hD (i : Fin q) : ContDiff ℝ (⊤ : ℕ∞) (fieldDerivative (X i) η) := by
    simpa only [Opens.coe_top, contDiffOn_univ] using
      RothschildStein.S.contDiffOn_fieldDerivative ⊤ (X i) η (hX i).contDiffOn hη.contDiffOn
  have hcD (i : Fin q) : HasCompactSupport (fieldDerivative (X i) η) :=
    hcη.of_isClosed_subset (isClosed_tsupport _) (RothschildStein.S.tsupport_fieldDerivative_subset (X i) η)
  choose Kd hKd using fun i => (hcD i).exists_bound_of_continuous (hD i).continuous
  have hKd0 (i : Fin q) : 0 ≤ Kd i := (norm_nonneg _).trans (hKd i 0)
  have hdBound (i : Fin q) : ∀ᵐ x ∂volume, ‖W.gradient i x‖ ≤ ∑ j, Kd j :=
    Filter.Eventually.of_forall fun x => (hKd i x).trans
      (Finset.single_le_sum (fun j _ => hKd0 j) (Finset.mem_univ i))
  have hηK : tsupport η ⊆ K := by
    intro x hx
    apply hφK
    apply subset_tsupport φ
    exact Function.mem_support.mpr (by rw [(hplateau x hx).1]; norm_num)
  have hWsupport (x : Fin N → ℝ) (hx : x ∉ K) : W.toFun x = 0 := by
    by_contra hne
    exact hx (hηK (subset_tsupport η (Function.mem_support.mpr hne)))
  have hdSupport (i : Fin q) (x : Fin N → ℝ) (hx : x ∉ K) : W.gradient i x = 0 := by
    by_contra hne
    exact hx (hηK (RothschildStein.S.tsupport_fieldDerivative_subset (X i) η
      (subset_tsupport _ (Function.mem_support.mpr hne))))
  have hWp : ∀ x, W.toFun x ≠ 0 ∨ (∃ i, W.gradient i x ≠ 0) →
      φ x = 1 ∧ ∀ i, fieldDerivative (X i) φ x = 0 := by
    intro x hx
    apply hplateau x
    rcases hx with hx | ⟨i, hi⟩
    · exact subset_tsupport η (Function.mem_support.mpr hx)
    · exact RothschildStein.S.tsupport_fieldDerivative_subset (X i) η
        (subset_tsupport _ (Function.mem_support.mpr hi))
  let data : HasReverseHolderCutoffAssemblyData coeff uK gK φ
      (fun i => fieldDerivative (X i) φ) v F W S w ws K θ
      A B a b c upper (∑ i, Kd i) ell upper p H L := {
    weak_pair := hpairK, shift_pos := hc, ellipticity_pos := hell, upper_nonneg := hupper
    power_pos := hp, power_le_half := hp2, interval_lt := hab, earlier_lt := hAa, later_lt := hbB
    value_rep := hwW, gradient_rep := hdwW, square_value_rep := hwsS, square_gradient_rep := hdwsS
    square_weight_value := hS, square_weight_gradient := hSd, square_weight_integrable := hSint
    plateau := hWp, region_measurable := hK.measurableSet, region_finite := hK.measure_lt_top.ne
    cutoff_unit := hηunit, value_support := hWsupport
    cutoff_gradient_memLp := fun i => (hD i).continuous.memLp_of_hasCompactSupport (hcD i)
    gradient_support := hdSupport, gradient_bound := hdBound, gradient_cost_nonneg := hL
    gradient_normSq_le := Filter.Eventually.of_forall hdL
    value_memLp := huK, gradient_memLp := hgK, value_nonneg := huK0, curve_nonneg := hz
    coefficient_slices := hcoeff, time_cutoff_contDiff := hθ, time_cutoff_top := hθb
    time_cutoff_unit := hθunit, time_cost_nonneg := hH, neg_deriv_sq_le := hθd }
  obtain ⟨e, hbudget⟩ := exists_backward_cutoff_energy_budgets_of_weak_pair hX W S w ws data
  have hm : (fun t => ∫ x in K, (uK t x + c) ^ p) =
      (fun t => ∫ x in K, (u t x + c) ^ p) := by
    funext t
    apply integral_congr_ae
    filter_upwards [self_mem_ae_restrict hK.measurableSet] with x hx
    simp only [uK, indicator_of_mem hx]
  let Y := fun t => W.affineEnergyMap hX
    (shiftedRpowWeakSolutionTest hc (p := p / 2) (by linarith)) w (c ^ (p / 2)) (v t)
  let D := fun t => ∫ x, 2 * ell * (p / 2) ^ 2 * coordinateNormSq
    (fun i => η x * ((uK t x + c) ^ (p / 2 - 1) * gK i t x))
  let R := fun t => ∫ x, 2 * upper * (uK t x + c) ^ p *
    coordinateNormSq (fun i => fieldDerivative (X i) η x)
  refine ⟨Y, e, D, R, ?_, ?_⟩
  · change HasBackwardCutoffEnergyBudgets a b ell H (upper * L) L Y θ e D R
      (fun t => ∫ x in K, (uK t x + c) ^ p) at hbudget
    rw [hm] at hbudget
    exact hbudget
  · have hv := hpairK.2.2.1.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
    have hg := (ae_all_iff.mpr hpairK.2.2.2.1).filter_mono
      (ae_mono (Measure.restrict_mono hsub le_rfl))
    filter_upwards [hv, hg, hz] with t hvt hgt hzt
    obtain ⟨hrep, _⟩ := W.shifted_rpow_affine_representatives_of_plateau hX hc
      (by linarith : p / 2 ≤ 1) (v t) w hzt hwW hdwW hvt hgt hWp
    filter_upwards [hrep] with x hx
    rw [hx]
    change η x * (uK t x + c) ^ (p / 2) = η x * (u t x + c) ^ (p / 2)
    by_cases hxK : x ∈ K
    · simp only [uK, indicator_of_mem hxK]
    · have hzero : η x = 0 := hWsupport x hxK
      simp only [hzero, zero_mul]

end HeatKernel
