-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.LogarithmicTimeSliceVariance
public import HeatKernel.Moser.LogarithmicHarnackGeometry
public import HeatKernel.Moser.LogarithmicHarnackConstants
public import HeatKernel.Moser.LogarithmicCylinderTail
public import HeatKernel.Moser.LogarithmicMeanShift
public import HeatKernel.Moser.LogarithmicCommonMeanFamily
public import HeatKernel.Moser.LogarithmicEnergyMeasurability
public import HeatKernel.Moser.LogarithmicCompactTimeTails
public import HeatKernel.Moser.LogarithmicInteriorWeight
public import HeatKernel.Moser.LogarithmicRegionExhaustion
public import HeatKernel.Bridge.ParabolicLocalEnergy
import Mathlib.Tactic
import all HeatKernel.Geometry.CarnotPoint
import all Mathlib.Basic.Real.Basic

/-! # Uniform logarithmic tails on inner regions of a weak-solution cylinder -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory Metric TopologicalSpace RothschildStein
open scoped ENNReal
namespace HeatKernel

/-- The literal normalized weighted logarithmic mean is a common shift for
both tails at almost every separating time, uniformly up to the open time
endpoints and for inner radii up to four thirds. -/
theorem exists_uniform_matrix_logarithmic_region_tails_with_mean_ae
    {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (ell upper : ℝ) (hell : 0 < ell) (hupper : 0 ≤ upper) :
    ∃ Aminus Aplus : ℝ, 0 ≤ Aminus ∧ 0 ≤ Aplus ∧
      ∀ (x : CarnotPoint G hq hqpos hspan) (t r : ℝ), 0 < r →
      ∀ start R : ℝ, t - 4 * r^2 ≤ start → start ≤ t - 3 * r^2 →
      5 / 4 * r ≤ R → R ≤ 4 / 3 * r →
      ∀ (coeff : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ)
      (u : ℝ × CarnotPoint G hq hqpos hspan → ℝ), Measurable u →
      (∀ᵐ y ∂(volume.prod (CarnotPoint.volume G hq hqpos hspan)).restrict
        (Ioo (t - 4 * r ^ 2) t ×ˢ Metric.ball x (2 * r)), 0 ≤ u y) →
      IsLocalWeakSolution G hq hqpos hw hspan coeff
        ⟨Ioo (t - 4 * r ^ 2) t, isOpen_Ioo⟩
        ⟨horizontalBall (G.horizontalFields hq) x (2 * r),
          isOpen_horizontalBall G hq hqpos hspan x (2 * r)⟩
        (fun s y => u (s, y)) →
      (∀ i j, Measurable (fun z : ℝ × (Fin N → ℝ) => coeff z.1 z.2 i j)) →
      (∀ᵐ z : ℝ × (Fin N → ℝ) ∂volume,
        (∀ i j, coeff z.1 z.2 i j = coeff z.1 z.2 j i) ∧ ∀ ξ : Fin q → ℝ,
          ell * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, coeff z.1 z.2 i j * ξ i * ξ j ∧
          ∑ i, ∑ j, coeff z.1 z.2 i j * ξ i * ξ j ≤ upper * ∑ i, ξ i ^ 2) →
      ∀ ε : ℝ, 0 < ε →
      ∀ᵐ τ ∂volume.restrict (Ioo (t - 113 / 64 * r^2) (t - 111 / 64 * r^2)),
      ∃ c : ℝ,
        c = (∫ y, max (1 - dist x y / (3 * r / 2)) 0 ^ 2 * Real.log (u (τ, y) + ε)
          ∂CarnotPoint.volume G hq hqpos hspan) /
          (∫ y, max (1 - dist x y / (3 * r / 2)) 0 ^ 2
            ∂CarnotPoint.volume G hq hqpos hspan) ∧
        (∀ ℓ : ℝ, 0 < ℓ →
          (volume.prod (CarnotPoint.volume G hq hqpos hspan))
            ((Ioo start τ ×ˢ Metric.ball x R) ∩
              {y | c + ℓ < Real.log (u y + ε)}) ≤ ENNReal.ofReal (Aminus / ℓ) *
                (volume.prod (CarnotPoint.volume G hq hqpos hspan))
                  (Ioo start τ ×ˢ Metric.ball x R)) ∧
        (∀ ℓ : ℝ, 0 < ℓ →
          (volume.prod (CarnotPoint.volume G hq hqpos hspan))
            ((Ioo τ t ×ˢ Metric.ball x R) ∩
              {y | Real.log (u y + ε) < c - ℓ}) ≤ ENNReal.ofReal (Aplus / ℓ) *
                (volume.prod (CarnotPoint.volume G hq hqpos hspan))
                  (Ioo τ t ×ˢ Metric.ball x R)) := by
  obtain ⟨K, hK, hspatial⟩ := exists_uniform_logarithmic_time_slice_variance G hq hqpos hspan hw
  let D₀ := upper * (((G.homogeneousDimension : ℝ) + 1) * ((G.homogeneousDimension : ℝ) + 2))
  let S := (2 : ℝ)^G.homogeneousDimension
  let A := 10000 * (K * S / ell + D₀)
  have hD₀ : 0 ≤ D₀ := by dsimp [D₀]; positivity
  have hS : 0 ≤ S := by positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  refine ⟨A, A, hA, hA, ?_⟩
  intro x t r hr start R hstartlow hstarthigh hRlow hRhigh coeff u hum hn hweak hcoeff hquad ε hε
  let I : Opens ℝ := ⟨Ioo (t - 4 * r^2) t, isOpen_Ioo⟩
  let U : Opens (Fin N → ℝ) := ⟨horizontalBall (G.horizontalFields hq) x (2 * r),
    isOpen_horizontalBall G hq hqpos hspan x (2 * r)⟩
  let a := fun n : ℕ => min (t - 3 * r^2) (start + 1 / (n + 1 : ℝ))
  let b := fun n => max (t - r^2) (interiorTopTime t n)
  let A₀ := fun n => (t - 4 * r^2 + a n) / 2
  let B := fun n => (b n + t) / 2
  have hr2 : 0 < r^2 := sq_pos_of_pos hr
  have ha (n : ℕ) : start ≤ a n ∧ t - 4 * r^2 < a n ∧ a n ≤ t - 3 * r^2 := by
    have hpos : 0 < (1 : ℝ) / (n + 1 : ℝ) := by positivity
    exact ⟨le_min hstarthigh (by linarith),
      lt_min (by linarith) (by linarith), min_le_left _ _⟩
  have hb (n : ℕ) : t - r^2 ≤ b n ∧ b n < t :=
    ⟨le_max_left _ _, max_lt (by linarith) (interiorTopTime_lt t n)⟩
  have hJ (n : ℕ) : Icc (A₀ n) (B n) ⊆ (I : Set ℝ) := by
    intro s hs
    exact ⟨by dsimp [I, A₀] at *; nlinarith [hs.1, (ha n).2.1],
      by dsimp [B] at *; nlinarith [(hb n).2, hs.2]⟩
  have hwindow (n : ℕ) : Ioo (t - 113 / 64 * r^2) (t - 111 / 64 * r^2) ⊆
      Icc (a n) (b n) := by
    intro s hs
    exact ⟨by nlinarith [hs.1, (ha n).2.2], by nlinarith [hs.2, (hb n).1]⟩
  have hncoord : ∀ᵐ z : ℝ × (Fin N → ℝ) ∂volume.restrict
      ((I : Set ℝ) ×ˢ (U : Set (Fin N → ℝ))), 0 ≤ u (z.1, z.2) := by
    rw [CarnotPoint.ball_eq_horizontalBall G hq hqpos hspan] at hn
    change ∀ᵐ z : ℝ × (Fin N → ℝ) ∂(volume.prod volume).restrict
      ((I : Set ℝ) ×ˢ (U : Set (Fin N → ℝ))), 0 ≤ u (z.1, z.2) at hn
    simpa only [← Measure.volume_eq_prod] using hn
  obtain ⟨g, m, hfamily, htimes⟩ :=
    hweak.exists_logarithmic_tent_mean_family G hq hqpos hspan hw x hr coeff I hcoeff
      hell.le hquad hncoord A₀ B a b hJ
      (fun n => by nlinarith [(ha n).2.2, (hb n).1])
      (fun n => by dsimp [A₀]; nlinarith [(ha n).2.1])
      (fun n => by dsimp [B]; nlinarith [(hb n).2]) hε hupper hwindow
  let ρ := 3 * r / 2
  let η := fun y => max (1 - (horizontalL2Distance (G.horizontalFields hq) x y).toReal / ρ) 0
  let mass := ∫ y, η y^2
  let D := D₀ / ρ^2
  let E := fun n s => mass⁻¹ * ∫ y, ∑ i, ∑ j, coeff s y i j *
    (η y * ((u (s, y) + ε)⁻¹ * g n j s y)) *
    (η y * ((u (s, y) + ε)⁻¹ * g n i s y))
  let f := fun s (y : CarnotPoint G hq hqpos hspan) => Real.log (u (s, y) + ε) - Real.log ε
  let w := fun y : CarnotPoint G hq hqpos hspan => η y^2
  let V := ball x R
  let _ : SFinite (CarnotPoint.volume G hq hqpos hspan) :=
    (inferInstance : SFinite (volume : Measure (Fin N → ℝ)))
  let ν := (CarnotPoint.volume G hq hqpos hspan).restrict V
  let μ : Measure (ℝ × CarnotPoint G hq hqpos hspan) := volume.prod (CarnotPoint.volume G hq hqpos hspan)
  let Vmass := (CarnotPoint.volume G hq hqpos hspan).real V
  let Kν := K * ρ^2 / ell * mass
  have hρ : 0 < ρ := by positivity
  have hη (y : CarnotPoint G hq hqpos hspan) :
      η y = max (1 - dist x y / ρ) 0 := by rw [dist_edist, CarnotPoint.edist_eq]
  have hmass : 0 < mass := Sobolev.integral_horizontal_tent_sq_pos G hq hqpos hspan hw x hρ
  have hwi : Integrable w (CarnotPoint.volume G hq hqpos hspan) := by
    change Integrable (fun y : Fin N → ℝ => η y^2) volume
    exact (Sobolev.integrable_horizontal_tent_and_sq G hq hqpos hspan hw x hρ).2
  have hRpos : 0 < R := lt_of_lt_of_le (by positivity : 0 < 5 / 4 * r) hRlow
  have hVfinite : (CarnotPoint.volume G hq hqpos hspan) V ≠ ⊤ := by
    dsimp only [V]
    rw [CarnotPoint.ball_eq_horizontalBall G hq hqpos hspan]
    exact (volume_horizontalBall_lt_top G hq hqpos hspan hw x hRpos.le).ne
  have hmassbound : mass ≤ S * Vmass := by
    apply (logarithmic_harnack_tent_mass_le G hq hqpos hspan hw x hr).trans
    apply mul_le_mul_of_nonneg_left _ hS
    exact ENNReal.toReal_mono hVfinite (measure_mono (ball_subset_ball hRlow))
  let _ : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr hVfinite
  have hwm : Measurable η := by
    change Measurable (fun y : CarnotPoint G hq hqpos hspan => η y)
    simp_rw [hη]
    fun_prop
  have hηzero : ∀ y ∉ (U : Set (Fin N → ℝ)), η y = 0 := by
    intro y hy
    have hd : 2 * r ≤ dist x (show CarnotPoint G hq hqpos hspan from y) := by
      have hy' : (show CarnotPoint G hq hqpos hspan from y) ∉ ball x (2 * r) := by
        rw [CarnotPoint.ball_eq_horizontalBall G hq hqpos hspan]
        exact hy
      change ¬dist (show CarnotPoint G hq hqpos hspan from y) x < 2 * r at hy'
      rw [dist_comm] at hy'
      exact le_of_not_gt hy'
    change η (show CarnotPoint G hq hqpos hspan from y) = 0
    rw [hη]
    have hdiv : 1 ≤ dist x (show CarnotPoint G hq hqpos hspan from y) / ρ :=
      (le_div_iff₀ hρ).mpr (by dsimp [ρ]; linarith)
    exact max_eq_right (by linarith)
  have hweight : ∀ s : ℝ, ∀ᵐ y ∂ν, (1 : ℝ) / 81 ≤ w y := by
    intro s
    filter_upwards [ae_restrict_mem isOpen_ball.measurableSet] with y hy
    change (1 : ℝ) / 81 ≤ η y^2
    rw [hη]
    exact logarithmic_tent_sq_lower_bound_on_inner_ball x hρ
      (ball_subset_ball (by dsimp [ρ]; linarith) hy)
  have hEn (n : ℕ) : ∀ᵐ s ∂volume, 0 ≤ E n s := by
    apply ae_nonneg_logarithmic_matrix_energy
      (hquad.mono fun z hz ξ => (mul_nonneg hell.le
        (Finset.sum_nonneg fun i _ => sq_nonneg (ξ i))).trans (hz.2 ξ).1)
  have hEm (n : ℕ) : AEStronglyMeasurable (E n) (volume.restrict (I : Set ℝ)) :=
    (hfamily n).1.aestronglyMeasurable_logarithmic_energy hcoeff hum hwm hηzero ε
  have hvariance (n : ℕ) : ∀ᵐ s ∂volume.restrict (Icc (a n) (b n)),
      Integrable (fun y => w y * (f s y - m n s)^2)
        (CarnotPoint.volume G hq hqpos hspan) ∧
      Integrable (fun y => w y * (f s y - m n s)^2) ν ∧
      (∫ y, w y * (f s y - m n s)^2 ∂ν) ≤ Kν * E n s := by
    have hsub : Icc (a n) (b n) ⊆ (I : Set ℝ) := by
      intro s hs
      exact ⟨(ha n).2.1.trans_le hs.1, hs.2.trans_lt (hb n).2⟩
    have H := hspatial x ρ (2 * r) hρ (by dsimp [ρ]; linarith) I
      (Icc (a n) (b n)) hsub coeff (fun s y => u (s, y)) (g n) (m n)
      ell upper ε hell hε hweak (hfamily n).1 hcoeff hquad hncoord (hfamily n).2.2.1
    filter_upwards [H] with s hs
    change Integrable (fun y => w y * (f s y - m n s)^2)
        (CarnotPoint.volume G hq hqpos hspan) ∧
      (∫ y, w y * (f s y - m n s)^2 ∂CarnotPoint.volume G hq hqpos hspan) ≤
        (K * ρ^2 / ell) * ∫ y : CarnotPoint G hq hqpos hspan, ∑ i, ∑ j, coeff s y i j *
          (η y * ((u (s, y) + ε)⁻¹ * g n j s y)) *
          (η y * ((u (s, y) + ε)⁻¹ * g n i s y))
            ∂CarnotPoint.volume G hq hqpos hspan at hs
    refine ⟨hs.1, hs.1.integrableOn, ?_⟩
    apply (integral_mono_measure Measure.restrict_le_self
      (Filter.Eventually.of_forall fun y => mul_nonneg (sq_nonneg _) (sq_nonneg _)) hs.1).trans
    apply hs.2.trans_eq
    dsimp only [Kν, E]
    field_simp
    rfl
  have hrelative (p q c d ℓ : ℝ) (hpq : p ≤ q) (hℓ : 0 < ℓ)
      (hδr : q - p ≤ 4 * r^2) (hδ₀ : r^2 ≤ d - c) (hδδ₀ : q - p ≤ d - c)
      (T : Set (ℝ × CarnotPoint G hq hqpos hspan))
      (htail : ((volume.restrict (Ioc p q)).prod ν).real T ≤
        max (324 * Kν) (2 * D * (q - p) *
          ((volume.restrict (Ioc p q)).prod ν).real univ) / ℓ) :
      μ ((Ioo p q ×ˢ V) ∩ T) ≤ ENNReal.ofReal (A / ℓ) * μ (Ioo c d ×ˢ V) := by
    exact logarithmic_cylinder_tail_of_energy_cost (CarnotPoint.volume G hq hqpos hspan)
      isOpen_ball.measurableSet hVfinite hpq (hr2.le.trans hδ₀ |> sub_nonneg.mp) hℓ
      (logarithmic_harnack_tail_cost_le hK.le hS hell hD₀ hr hmassbound
        measureReal_nonneg (sub_nonneg.mpr hpq) hδr hδ₀ hδδ₀) htail
  filter_upwards [ae_restrict_mem measurableSet_Ioo, htimes,
    ae_restrict_of_ae_restrict_of_subset (hwindow 0) (hvariance 0),
    ae_restrict_of_ae_restrict_of_subset (hwindow 0) (hfamily 0).2.2.1]
      with τ hτ hshared hvar hmean
  obtain ⟨shift, hshared⟩ := hshared
  have hτl := hτ.1
  have hτr := hτ.2
  have hraw : Integrable (fun y : CarnotPoint G hq hqpos hspan =>
      w y * Real.log (u (τ, y) + ε)) (CarnotPoint.volume G hq hqpos hspan) :=
    integrable_logarithmic_moment_of_variance hwi
      (((hum.comp (measurable_const.prodMk measurable_id)).add_const ε).log.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun y => sq_nonneg _) (m 0 τ) (Real.log ε) hvar.1
  have hmean' : shift = mass⁻¹ * (∫ y, w y *
      (Real.log (u (τ, y) + ε) - Real.log ε) ∂CarnotPoint.volume G hq hqpos hspan) := by
    rw [← hshared 0]
    change m 0 τ = (∫ y : Fin N → ℝ, η y^2)⁻¹ *
      (∫ y : Fin N → ℝ, η y^2 * (Real.log (u (τ, y) + ε) - Real.log ε))
    exact hmean
  have hshiftmean : shift + Real.log ε =
      (∫ y, max (1 - dist x y / (3 * r / 2)) 0 ^ 2 * Real.log (u (τ, y) + ε)
        ∂CarnotPoint.volume G hq hqpos hspan) /
      (∫ y, max (1 - dist x y / (3 * r / 2)) 0 ^ 2
        ∂CarnotPoint.volume G hq hqpos hspan) := by
    have H := normalized_logarithmic_mean_centering hwi hraw (ne_of_gt hmass) (Real.log ε)
    change mass⁻¹ * (∫ y, w y * (Real.log (u (τ, y) + ε) - Real.log ε)
      ∂CarnotPoint.volume G hq hqpos hspan) + Real.log ε = _ at H
    rw [← hmean'] at H
    simpa only [w, hη, ρ] using H
  have haτ (n : ℕ) : a n ≤ τ := by nlinarith [(ha n).2.2]
  have hτb (n : ℕ) : τ ≤ b n := by nlinarith [hτr, (hb n).1]
  have hC : 0 ≤ D := div_nonneg hD₀ (sq_nonneg _)
  have hKν : 0 ≤ Kν := by positivity
  have hdata (n : ℕ) : ∀ᵐ s ∂volume, s ∈ Icc (a n) (b n) →
      E n s ≤ 2 * deriv (fun z => m n z + D * z) s ∧
      (∀ᵐ y ∂ν, 0 ≤ w y) ∧
      Integrable (fun y => w y * (f s y - m n s)^2) ν ∧
      (∫ y, w y * (f s y - m n s)^2 ∂ν) ≤ Kν * E n s := by
    apply (ae_restrict_iff' measurableSet_Icc).mp
    filter_upwards [(hfamily n).2.2.2.2.2, hvariance n] with s hs hv
    exact ⟨hs, Filter.Eventually.of_forall fun y => sq_nonneg _, hv.2⟩
  have hfmeas : Measurable (fun z : ℝ × CarnotPoint G hq hqpos hspan => f z.1 z.2) :=
    (hum.add_const ε).log.sub_const (Real.log ε)
  have hcompacttails (n : ℕ) := measureReal_logarithmic_compact_time_tails_le
    ν (haτ n) (hτb n)
    (show Icc (a n) (b n) ⊆ (I : Set ℝ) from fun s hs =>
      ⟨(ha n).2.1.trans_le hs.1, hs.2.trans_lt (hb n).2⟩)
    hC hKν hfmeas hweight (hfamily n).2.2.2.1 (hEm n) (hEn n) (hdata n)
  have htminus : ∀ ℓ : ℝ, 0 < ℓ →
      μ ((Ioo start τ ×ˢ V) ∩ {z | shift + ℓ < f z.1 z.2}) ≤
        ENNReal.ofReal (A / ℓ) * μ (Ioo start τ ×ˢ V) := by
    intro ℓ hℓ
    have hcompact (n : ℕ) : μ ((Ioo (a n) τ ×ˢ V) ∩ {z | shift + ℓ < f z.1 z.2}) ≤
        ENNReal.ofReal (A / ℓ) * μ (Ioo start τ ×ˢ V) := by
      have htail := (hcompacttails n).1
      rw [hshared n] at htail
      exact hrelative (a n) τ start τ ℓ (haτ n) hℓ
        (by nlinarith [(ha n).2.1, hτr]) (by nlinarith [hτl])
        (by linarith [(ha n).1]) _ (htail ℓ hℓ)
    exact measure_inter_prod_Ioo_le_of_interior_bottom_bounds μ start τ (t - 3 * r^2)
      hstarthigh V {z | shift + ℓ < f z.1 z.2} _ hcompact
  have htplus : ∀ ℓ : ℝ, 0 < ℓ →
      μ ((Ioo τ t ×ˢ V) ∩ {z | f z.1 z.2 < shift - ℓ}) ≤
        ENNReal.ofReal (A / ℓ) * μ (Ioo τ t ×ˢ V) := by
    intro ℓ hℓ
    have hcompact (n : ℕ) : μ ((Ioo τ (b n) ×ˢ V) ∩ {z | f z.1 z.2 < shift - ℓ}) ≤
        ENNReal.ofReal (A / ℓ) * μ (Ioo τ t ×ˢ V) := by
      have htail := (hcompacttails n).2
      rw [hshared n] at htail
      exact hrelative τ (b n) τ t ℓ (hτb n) hℓ
        (by nlinarith [(hb n).2, hτl]) (by nlinarith [hτr])
        (by linarith [(hb n).2]) _ (htail ℓ hℓ)
    exact measure_inter_prod_Ioo_le_of_max_interior_top_bounds μ τ t (t - r^2)
      V {z | f z.1 z.2 < shift - ℓ} _ hcompact
  refine ⟨shift + Real.log ε, hshiftmean, ?_, ?_⟩
  · intro ℓ hℓ
    convert htminus ℓ hℓ using 1
    congr 1
    ext z
    simp only [mem_inter_iff, mem_ofPred_eq, f]
    constructor <;> rintro ⟨hz, hh⟩ <;> exact ⟨hz, by linarith⟩
  · intro ℓ hℓ
    convert htplus ℓ hℓ using 1
    congr 1
    ext z
    simp only [mem_inter_iff, mem_ofPred_eq, f]
    constructor <;> rintro ⟨hz, hh⟩ <;> exact ⟨hz, by linarith⟩

/-- Both logarithmic tails hold at almost every separating time, uniformly
for inner radii up to four thirds and for earlier intervals reaching the open
bottom of the solution cylinder. -/
theorem exists_uniform_matrix_logarithmic_region_tails_ae
    {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (ell upper : ℝ) (hell : 0 < ell) (hupper : 0 ≤ upper) :
    ∃ Aminus Aplus : ℝ, 0 ≤ Aminus ∧ 0 ≤ Aplus ∧
      ∀ (x : CarnotPoint G hq hqpos hspan) (t r : ℝ), 0 < r →
      ∀ start R : ℝ, t - 4 * r^2 ≤ start → start ≤ t - 3 * r^2 →
      5 / 4 * r ≤ R → R ≤ 4 / 3 * r →
      ∀ (coeff : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ)
      (u : ℝ × CarnotPoint G hq hqpos hspan → ℝ), Measurable u →
      (∀ᵐ y ∂(volume.prod (CarnotPoint.volume G hq hqpos hspan)).restrict
        (Ioo (t - 4 * r ^ 2) t ×ˢ Metric.ball x (2 * r)), 0 ≤ u y) →
      IsLocalWeakSolution G hq hqpos hw hspan coeff
        ⟨Ioo (t - 4 * r ^ 2) t, isOpen_Ioo⟩
        ⟨horizontalBall (G.horizontalFields hq) x (2 * r),
          isOpen_horizontalBall G hq hqpos hspan x (2 * r)⟩
        (fun s y => u (s, y)) →
      (∀ i j, Measurable (fun z : ℝ × (Fin N → ℝ) => coeff z.1 z.2 i j)) →
      (∀ᵐ z : ℝ × (Fin N → ℝ) ∂volume,
        (∀ i j, coeff z.1 z.2 i j = coeff z.1 z.2 j i) ∧ ∀ ξ : Fin q → ℝ,
          ell * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, coeff z.1 z.2 i j * ξ i * ξ j ∧
          ∑ i, ∑ j, coeff z.1 z.2 i j * ξ i * ξ j ≤ upper * ∑ i, ξ i ^ 2) →
      ∀ ε : ℝ, 0 < ε →
      ∀ᵐ τ ∂volume.restrict (Ioo (t - 113 / 64 * r^2) (t - 111 / 64 * r^2)),
      ∃ c : ℝ,
        (∀ ℓ : ℝ, 0 < ℓ →
          (volume.prod (CarnotPoint.volume G hq hqpos hspan))
            ((Ioo start τ ×ˢ Metric.ball x R) ∩
              {y | c + ℓ < Real.log (u y + ε)}) ≤ ENNReal.ofReal (Aminus / ℓ) *
                (volume.prod (CarnotPoint.volume G hq hqpos hspan))
                  (Ioo start τ ×ˢ Metric.ball x R)) ∧
        (∀ ℓ : ℝ, 0 < ℓ →
          (volume.prod (CarnotPoint.volume G hq hqpos hspan))
            ((Ioo τ t ×ˢ Metric.ball x R) ∩
              {y | Real.log (u y + ε) < c - ℓ}) ≤ ENNReal.ofReal (Aplus / ℓ) *
                (volume.prod (CarnotPoint.volume G hq hqpos hspan))
                  (Ioo τ t ×ˢ Metric.ball x R)) := by
  obtain ⟨Aminus, Aplus, hAminus, hAplus, htails⟩ :=
    exists_uniform_matrix_logarithmic_region_tails_with_mean_ae
      G hq hqpos hspan hw ell upper hell hupper
  refine ⟨Aminus, Aplus, hAminus, hAplus, ?_⟩
  intro x t r hr start R hstartlow hstarthigh hRlow hRhigh coeff u hum hn hweak ha hquad ε hε
  filter_upwards [htails x t r hr start R hstartlow hstarthigh hRlow hRhigh
    coeff u hum hn hweak ha hquad ε hε] with τ ht
  obtain ⟨c, _, hminus, hplus⟩ := ht
  exact ⟨c, hminus, hplus⟩

end HeatKernel
