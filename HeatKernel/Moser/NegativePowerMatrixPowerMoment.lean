-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.NegativePowerCutoffMoments
public import HeatKernel.Moser.NegativePowerMatrixMomentBudget
public import HeatKernel.Moser.NegativePowerLocalizedMoments
public import HeatKernel.Moser.MeanValueMatrixCutoffPair
public import HeatKernel.Moser.MeanValueSmoothSpatialWeights
public import HeatKernel.Form.SmoothCompactBoundaryMultipliers
public import Mathlib.Analysis.Calculus.Deriv.Pow

/-! # Localized reciprocal moments from the elliptic matrix weak equation -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace RothschildStein
open scoped ENNReal
namespace HeatKernel

/-- The matrix weak equation gives a localized reciprocal half-power moment
with a constant independent of the reciprocal exponent and perturbation.
Only smooth spatial cutoffs and a lower-time cutoff are supplied. -/
theorem exists_uniform_matrix_reciprocal_power_moment_constant {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hwG : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    {ν : ℝ} (hν : max 2 (G.homogeneousDimension : ℝ) < ν)
    (ell upper : ℝ) (hell : 0 < ell) (hupper : 0 ≤ upper) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (I : Opens ℝ) (U V : Opens (Fin N → ℝ)),
      volume (V : Set (Fin N → ℝ)) ≠ ⊤ →
      ∀ u : ℝ × (Fin N → ℝ) → ℝ, Measurable u → (∀ z, 0 ≤ u z) →
      ∀ coeff : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ,
      IsLocalWeakSolution G hq hqpos hwG hspan coeff I U (fun t x => u (t, x)) →
      (∀ i j, Measurable (fun z : ℝ × (Fin N → ℝ) => coeff z.1 z.2 i j)) →
      (∀ᵐ z : ℝ × (Fin N → ℝ) ∂volume,
        (∀ i j, coeff z.1 z.2 i j = coeff z.1 z.2 j i) ∧ ∀ ξ : Fin q → ℝ,
          ell * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, coeff z.1 z.2 i j * ξ i * ξ j ∧
          ∑ i, ∑ j, coeff z.1 z.2 i j * ξ i * ξ j ≤ upper * ∑ i, ξ i ^ 2) →
      ∀ A₀ B a b : ℝ, Icc A₀ B ⊆ (I : Set ℝ) → a < b → A₀ < a → b < B →
      ∀ φ η : (Fin N → ℝ) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → (∀ x, φ x ∈ Icc (0 : ℝ) 1) →
      HasCompactSupport φ → tsupport φ ⊆ (U : Set (Fin N → ℝ)) →
      tsupport φ ⊆ (V : Set (Fin N → ℝ)) →
      ContDiff ℝ (⊤ : ℕ∞) η → (∀ x, η x ∈ Icc (0 : ℝ) 1) →
      HasCompactSupport η → tsupport η ⊆ (V : Set (Fin N → ℝ)) →
      (∀ x ∈ tsupport η, φ x = 1 ∧
        ∀ i, fieldDerivative (G.horizontalFields hq i) φ x = 0) →
      ∀ L : ℝ, 0 ≤ L →
      (∀ x, (∑ i, fieldDerivative (G.horizontalFields hq i) η x ^ 2) ≤ L) →
      ∀ θ : ℝ → ℝ, ContDiff ℝ 1 θ → θ a = 0 →
      (∀ t ∈ Icc a b, θ t ∈ Icc (0 : ℝ) 1) →
      ∀ Ttime : ℝ, 0 ≤ Ttime → (∀ t ∈ Icc a b, deriv θ t ≤ Ttime) →
      ∀ c p : ℝ, 0 < c → 0 < p →
      (∫⁻ t in Icc a b, ∫⁻ x, ‖θ t * η x * (u (t, x) + c) ^ (-p / 2)‖ₑ ^
        (2 + 4 / ν) ∂volume) ≤
          ENNReal.ofReal A *
            (ENNReal.ofReal ((2 * Ttime + 2 * upper * L) +
              (2 * Ttime + 2 * upper * L) / ell + 2 * L + 1) *
              ENNReal.ofReal (∫ t in Icc a b,
                ∫ x in (V : Set (Fin N → ℝ)), (u (t, x) + c) ^ (-p))) ^ (1 + 2 / ν) := by
  obtain ⟨A, hA, hSob⟩ := exists_uniform_reciprocal_graph_moment_constant
    G hq hqpos hspan hwG hν
  refine ⟨A, hA, ?_⟩
  intro I U V hfinite u hum hu0 coeff hu ha hbound A₀ B a b hJI hab hAa hbB
    φ η hφ hφunit hcφ hφU hφV hη hηunit hcη hηV hplateau L hL hd
    θ hθ hθa hθunit Ttime hTtime hθd c p hc hp
  let X := G.horizontalFields hq
  have hX := G.horizontalFields_contDiff hq
  have hun : ∀ᵐ z ∂volume.restrict ((I : Set ℝ) ×ˢ (U : Set (Fin N → ℝ))),
      0 ≤ u z := Filter.Eventually.of_forall hu0
  obtain ⟨g, v, F, _, hpair, hzAB⟩ := hu.exists_smooth_cutoff_energy_pair
    G hq hqpos hwG hspan coeff I U V ha hell.le hbound hun hJI
    hφ hφunit hcφ hφU hφV
  have hsub : Icc a b ⊆ Icc A₀ B := fun t ht => ⟨hAa.le.trans ht.1, ht.2.trans hbB.le⟩
  have hz := hzAB.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
  have hv := hpair.1.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hval := hpair.2.2.1.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
  let d := fun i => fieldDerivative (X i) η
  have hdLp (i : Fin q) : MemLp (d i) 2 volume := by
    have hcd : ContDiff ℝ (⊤ : ℕ∞) (d i) := by
      simpa only [d, Opens.coe_top, contDiffOn_univ] using
        S.contDiffOn_fieldDerivative ⊤ (X i) η (hX i).contDiffOn hη.contDiffOn
    exact hcd.continuous.memLp_of_hasCompactSupport
      (hcη.of_isClosed_subset (isClosed_tsupport _) (S.tsupport_fieldDerivative_subset (X i) η))
  have hηLp : MemLp η 2 volume := hη.continuous.memLp_of_hasCompactSupport hcη
  have hηb : ∀ᵐ x ∂volume, ‖η x‖ ≤ 1 := Filter.Eventually.of_forall fun x => by
    simpa only [Real.norm_of_nonneg (hηunit x).1] using (hηunit x).2
  have hactive (x : Fin N → ℝ) (hx : η x ≠ 0 ∨ (∃ i, d i x ≠ 0)) : x ∈ tsupport η := by
    rcases hx with hx | ⟨i, hi⟩
    · exact subset_tsupport η (Function.mem_support.mpr hx)
    · exact S.tsupport_fieldDerivative_subset (X i) η
        (subset_tsupport (d i) (Function.mem_support.mpr hi))
  let W := WeakSolutionSpatialWeight.ofSmoothUnitCutoff V X hX hη hcη hηV hηunit
  obtain ⟨S, hS, hSd⟩ := exists_smooth_square_spatial_weight V X hX hη hcη hηV hηunit
  obtain ⟨w, hw, hdw⟩ := exists_zeroBoundaryGraph_smooth_compact_constant V X hX hη hcη hηV 1
  simp only [mul_one] at hw hdw
  have hcηsq : HasCompactSupport (fun x => η x ^ 2) := by
    simpa only [pow_two, Pi.mul_def] using hcη.mul_left (f := η)
  have hηsqV : tsupport (fun x => η x ^ 2) ⊆ (V : Set (Fin N → ℝ)) := by
    simpa only [pow_two] using (tsupport_mul_subset_left (f := η) (g := η)).trans hηV
  obtain ⟨wS, hwS, hdwS⟩ := exists_zeroBoundaryGraph_smooth_compact_constant
    V X hX (hη.pow 2) hcηsq hηsqV 1
  have hws : (wS : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume] S.toFun := by
    rw [funext hS]
    simpa only [mul_one] using hwS
  have hdws (i : Fin q) : (wS : GradientSpace (N := N) ⊤ q).snd i =ᵐ[volume] S.gradient i := by
    rw [funext (hSd i)]
    simpa only [mul_one, fieldDerivative_smooth_cutoff_sq X hη] using hdwS i
  have hSint : Integrable S.toFun volume := by
    rw [funext hS]
    exact hηLp.integrable_sq
  have hSp (x : Fin N → ℝ) (hx : S.toFun x ≠ 0 ∨ (∃ i, S.gradient i x ≠ 0)) :
      φ x = 1 ∧ ∀ i, fieldDerivative (X i) φ x = 0 := by
    apply hplateau x
    apply hactive x
    left
    intro he
    rcases hx with hx | ⟨i, hi⟩
    · exact hx (by rw [hS, he]; norm_num)
    · exact hi (by rw [hSd, he]; ring)
  let m := fun t => ∫ x in (V : Set (Fin N → ℝ)), (u (t, x) + c) ^ (-p)
  have hm : IntegrableOn m (Icc a b) := integrableOn_reciprocal_spatial_moment hfinite hum hu0 hc hp
  have hm0 : ∀ᵐ t ∂volume.restrict (Icc a b), 0 ≤ m t :=
    Filter.Eventually.of_forall fun t => integral_nonneg fun x =>
      Real.rpow_nonneg (add_nonneg (hu0 (t, x)) hc.le) _
  have hcmp : ∀ᵐ t ∂volume.restrict (Icc a b),
      (∫ x, η x ^ 2 * ((v t : GradientSpace (N := N) ⊤ q).fst x + c) ^ (-p)) ≤ m t ∧
      (∫ x, ((v t : GradientSpace (N := N) ⊤ q).fst x + c) ^ (-p) *
        coordinateNormSq (fun i => d i x)) ≤ L * m t := by
    filter_upwards [hz, hval] with t hzt hvt
    exact reciprocal_graph_cutoff_moment_comparisons hc hp hL hfinite
      ((hum.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun x => hu0 (t, x)) hηLp hηunit hdLp hd
      (fun x hx => hηV (hactive x hx)) (fun x hx => (hplateau x (hactive x hx)).1)
      (v t) hzt hvt
  have hcm : ∀ᵐ t ∂volume.restrict (Icc a b),
      ∀ i j, AEStronglyMeasurable (fun x => coeff t x i j) volume :=
    Filter.Eventually.of_forall fun t i j =>
      ((ha i j).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  have hcs := (Measure.ae_ae_of_ae_prod hbound).filter_mono
    (ae_mono (Measure.restrict_le_self : volume.restrict (Icc a b) ≤ volume))
  have hce : ∀ᵐ t ∂volume.restrict (Icc a b), ∀ᵐ x ∂volume,
      (∀ i j, coeff t x i j = coeff t x j i) ∧ ∀ ξ : Fin q → ℝ,
        ell * coordinateNormSq ξ ≤ matrixEnergy (coeff t x) ξ ∧
        matrixEnergy (coeff t x) ξ ≤ upper * coordinateNormSq ξ := by
    filter_upwards [hcs] with t ht
    filter_upwards [ht] with x hx
    simpa only [coordinateNormSq, matrixEnergy, mul_assoc, mul_left_comm, mul_comm] using hx
  let H := 2 * Ttime + 2 * upper * L
  obtain ⟨hDi, hb, htotal⟩ := hpair.matrix_reciprocal_budget_le_outer_moment hX
    hc hp hell hupper S wS hSint hws hdws hS hSd hSp hη.continuous.aestronglyMeasurable
    hηb hdLp hab hAa hbB hz hcm hce hm hm0 hL
    (hcmp.mono fun _ h => h.1) (hcmp.mono fun _ h => h.2)
    (hθ.pow 2) (by simp only [hθa, zero_pow (by decide : 2 ≠ 0)])
    (fun t ht => ⟨sq_nonneg _, by obtain ⟨h0, h1⟩ := hθunit t ht; nlinarith⟩)
    (show 0 ≤ 2 * Ttime by positivity)
    (fun t ht => deriv_sq_cutoff_le hθ (hθunit t ht) hTtime (hθd t ht))
  let D := fun t => ∫ x, 2 * ell * (p / 2) ^ 2 * coordinateNormSq
    (fun i => η x * (((v t : GradientSpace (N := N) ⊤ q).fst x + c) ^
      (-p / 2 - 1) * (v t : GradientSpace (N := N) ⊤ q).snd i x))
  let Y := fun t => W.affineEnergyMap hX (shiftedRpowWeakSolutionTest hc
    (p := -p / 2) (by linarith)) w (c ^ (-p / 2)) (v t)
  have hY : MemLp Y 2 (volume.restrict (Icc a b)) :=
    (W.multiplier.comp_memLp' ((shiftedRpowWeakSolutionTest hc
      (p := -p / 2) (by linarith)).memLp_energyMap V X hX hv)).add (memLp_const _)
  have hD0 (t : ℝ) : 0 ≤ D t := integral_nonneg fun x => by
    dsimp only [coordinateNormSq]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => sq_nonneg _)
  have hnorms : ∀ᵐ t ∂volume.restrict (Icc a b),
      ‖(Y t : GradientSpace (N := N) ⊤ q).fst‖ ^ 2 =
        (∫ x, η x ^ 2 * ((v t : GradientSpace (N := N) ⊤ q).fst x + c) ^ (-p)) ∧
      ‖(Y t : GradientSpace (N := N) ⊤ q).snd‖ ^ 2 ≤ D t / ell + 2 * L * m t := by
    filter_upwards [hz, hcmp] with t hzt hct
    obtain ⟨hyv, hyg⟩ := W.negative_half_power_graph_energy_bounds (η := η) (d := d) hX hc hp
      (v t) w hzt hw hdw (fun _ => rfl) (fun _ _ => rfl)
      hη.continuous.aestronglyMeasurable hηb hdLp
    refine ⟨hyv, hyg.trans ?_⟩
    dsimp only [D]
    simp only [integral_const_mul]
    have he : 2 * ell * (p / 2) ^ 2 * (∫ x, coordinateNormSq
        (fun i => η x * (((v t : GradientSpace (N := N) ⊤ q).fst x + c) ^
          (-p / 2 - 1) * (v t : GradientSpace (N := N) ⊤ q).snd i x))) / ell =
        2 * (p / 2) ^ 2 * (∫ x, coordinateNormSq
        (fun i => η x * (((v t : GradientSpace (N := N) ⊤ q).fst x + c) ^
          (-p / 2 - 1) * (v t : GradientSpace (N := N) ⊤ q).snd i x))) := by
      field_simp [hell.ne']
    rw [he]
    nlinarith only [hct.2]
  have hslice : ∀ᵐ t ∂volume.restrict (Icc a b),
      θ t ^ 2 * ‖(Y t : GradientSpace (N := N) ⊤ q).fst‖ ^ 2 ≤ H * (∫ s in Icc a b, m s) := by
    filter_upwards [hb, hnorms] with t ht hn
    rw [hn.1]
    have hi : 0 ≤ ∫ s in Icc a t, θ s ^ 2 * D s :=
      integral_nonneg fun s => mul_nonneg (sq_nonneg _) (hD0 s)
    dsimp only [H] at *
    linarith
  have hYvalue : ∀ᵐ t ∂volume.restrict (Icc a b),
      ‖(Y t : GradientSpace (N := N) ⊤ q).fst‖ ^ 2 ≤ m t := by
    filter_upwards [hnorms, hcmp] with t hn hc'
    exact hn.1.le.trans hc'.1
  have hmoment := hSob V hfinite a b ell H L Y θ D m
    ⟨hell, by dsimp only [H]; positivity, hL, hY, hθ.continuous, hθunit,
      hDi, hm, Filter.Eventually.of_forall hD0, hm0,
      hYvalue,
      hnorms.mono (fun _ ht => ht.2), hslice, htotal⟩
  have hrep : ∀ᵐ t ∂volume.restrict (Icc a b),
      ((θ t • Y t : zeroBoundaryGraph V X) : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume]
        fun x => θ t * η x * (u (t, x) + c) ^ (-p / 2) := by
    filter_upwards [hz, hval] with t hzt hvt
    have hvY := W.affineEnergyMap_value_ae hX (shiftedRpowWeakSolutionTest hc
      (p := -p / 2) (by linarith)) w (c ^ (-p / 2)) hw (v t)
    change (Y t : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume] _ at hvY
    have hs := Lp.coeFn_smul (θ t) (Y t : GradientSpace (N := N) ⊤ q).fst
    simp only [Opens.coe_top, Measure.restrict_univ] at hs
    filter_upwards [hs, hvY, hzt, hvt] with x hsx hvx hn hx
    change (θ t • (Y t : GradientSpace (N := N) ⊤ q).fst) x = _
    rw [hsx]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hvx]
    change θ t * (η x * ((shiftedRpowWeakSolutionTest hc
      (p := -p / 2) (by linarith)).toFun
      ((v t : GradientSpace (N := N) ⊤ q).fst x) + c ^ (-p / 2))) = _
    rw [show (shiftedRpowWeakSolutionTest hc (p := -p / 2) (by linarith)).toFun
      ((v t : GradientSpace (N := N) ⊤ q).fst x) =
        ((v t : GradientSpace (N := N) ⊤ q).fst x + c) ^ (-p / 2) - c ^ (-p / 2) from
          Sobolev.zeroPreservingShiftedRpow_eq (c := c) (p := -p / 2) hn, sub_add_cancel]
    by_cases he : η x = 0
    · simp only [he, zero_mul, mul_zero]
    · rw [hx, (hplateau x (hactive x (Or.inl he))).1, mul_one, mul_assoc]
  have heq : (∫⁻ t in Icc a b, ∫⁻ x,
      ‖((θ t • Y t : zeroBoundaryGraph V X) : GradientSpace (N := N) ⊤ q).fst x‖ₑ ^
        (2 + 4 / ν) ∂volume) =
      ∫⁻ t in Icc a b, ∫⁻ x, ‖θ t * η x * (u (t, x) + c) ^ (-p / 2)‖ₑ ^
        (2 + 4 / ν) ∂volume := by
    apply lintegral_congr_ae
    filter_upwards [hrep] with t ht
    exact lintegral_congr_ae (ht.mono fun x hx => by dsimp at hx ⊢; rw [hx])
  rw [heq] at hmoment
  exact hmoment

end HeatKernel
