-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.NegativePowerGraphFlux
public import HeatKernel.Moser.NegativePowerTerminalBudget
public import HeatKernel.Moser.NegativePowerMoment

/-! # Reciprocal matrix budgets controlled by an outer value moment -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace
namespace HeatKernel

/-- Matrix ellipticity and the weak cutoff time equation give both terminal
and total reciprocal diffusion budgets. The two spatial comparisons specify
the outer moment and the cutoff-gradient cost; no time-energy budget is assumed. -/
theorem IsZeroBoundaryWeakCutoffEnergyTimePair.matrix_reciprocal_budget_le_outer_moment
    {N q : ℕ} {V : Opens (Fin N → ℝ)}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    {u : ℝ → (Fin N → ℝ) → ℝ} {g : Fin q → ℝ → (Fin N → ℝ) → ℝ}
    {φ η : (Fin N → ℝ) → ℝ} {k d : Fin q → (Fin N → ℝ) → ℝ}
    {v : ℝ → zeroBoundaryGraph V X}
    {F : ℝ → (zeroBoundaryGraph V X →L[ℝ] ℝ)}
    {A B a b c p ell upper K L Htime : ℝ}
    {coeff : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ}
    (hp : IsZeroBoundaryWeakCutoffEnergyTimePair V X coeff (Icc A B) u g φ k v F)
    (hc : 0 < c) (hpower : 0 < p) (hell : 0 < ell) (hupper : 0 ≤ upper)
    (W : WeakSolutionSpatialWeight V X) (w : zeroBoundaryGraph V X)
    (hWint : Integrable W.toFun volume)
    (hw : (w : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume] W.toFun)
    (hdw : ∀ i, (w : GradientSpace (N := N) ⊤ q).snd i =ᵐ[volume] W.gradient i)
    (hW : ∀ x, W.toFun x = η x ^ 2)
    (hWd : ∀ i x, W.gradient i x = 2 * η x * d i x)
    (hplateau : ∀ x, W.toFun x ≠ 0 ∨ (∃ i, W.gradient i x ≠ 0) →
      φ x = 1 ∧ ∀ i, k i x = 0)
    (hη : AEStronglyMeasurable η volume) (hηb : ∀ᵐ x ∂volume, ‖η x‖ ≤ K)
    (hd : ∀ i, MemLp (d i) 2 volume)
    (hab : a < b) (hAa : A < a) (hbB : b < B)
    (hz : ∀ᵐ t ∂volume.restrict (Icc a b), ∀ᵐ x ∂volume,
      0 ≤ (v t : GradientSpace (N := N) ⊤ q).fst x)
    (hcoeff_meas : ∀ᵐ t ∂volume.restrict (Icc a b),
      ∀ i j, AEStronglyMeasurable (fun x => coeff t x i j) volume)
    (hcoeff : ∀ᵐ t ∂volume.restrict (Icc a b), ∀ᵐ x ∂volume,
      (∀ i j, coeff t x i j = coeff t x j i) ∧ ∀ ξ : Fin q → ℝ,
        ell * coordinateNormSq ξ ≤ matrixEnergy (coeff t x) ξ ∧
        matrixEnergy (coeff t x) ξ ≤ upper * coordinateNormSq ξ)
    {m : ℝ → ℝ} (hm : IntegrableOn m (Icc a b))
    (hm0 : ∀ᵐ t ∂volume.restrict (Icc a b), 0 ≤ m t)
    (hL : 0 ≤ L)
    (hvalue : ∀ᵐ t ∂volume.restrict (Icc a b),
      (∫ x, η x ^ 2 * ((v t : GradientSpace (N := N) ⊤ q).fst x + c) ^ (-p)) ≤ m t)
    (herror : ∀ᵐ t ∂volume.restrict (Icc a b),
      (∫ x, ((v t : GradientSpace (N := N) ⊤ q).fst x + c) ^ (-p) *
        coordinateNormSq (fun i => d i x)) ≤ L * m t)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ 1 χ) (hχa : χ a = 0)
    (hχunit : ∀ t ∈ Icc a b, χ t ∈ Icc (0 : ℝ) 1)
    (hHtime : 0 ≤ Htime) (hχderiv : ∀ t ∈ Icc a b, deriv χ t ≤ Htime) :
    let E := fun t => ∫ x, η x ^ 2 *
      ((v t : GradientSpace (N := N) ⊤ q).fst x + c) ^ (-p)
    let D := fun t => ∫ x, 2 * ell * (p / 2) ^ 2 * coordinateNormSq
      (fun i => η x * (((v t : GradientSpace (N := N) ⊤ q).fst x + c) ^
        (-p / 2 - 1) * (v t : GradientSpace (N := N) ⊤ q).snd i x))
    IntegrableOn D (Icc a b) ∧
      (∀ᵐ s ∂volume.restrict (Icc a b),
        χ s * E s + (∫ t in Icc a s, χ t * D t) ≤
          (Htime + 2 * upper * L) * (∫ t in Icc a b, m t)) ∧
      (∫ t in Icc a b, χ t * D t) ≤
        (Htime + 2 * upper * L) * (∫ t in Icc a b, m t) := by
  dsimp only
  let T := shiftedRpowWeakSolutionTest hc (p := -p - 1) (by linarith)
  let E := fun t => c ^ (-p) * (∫ x, W.toFun x) -
    p * W.affineEnergy T w (c ^ (-p - 1)) (v t)
  let D := fun t => ∫ x, 2 * ell * (p / 2) ^ 2 * coordinateNormSq
    (fun i => η x * (((v t : GradientSpace (N := N) ⊤ q).fst x + c) ^
      (-p / 2 - 1) * (v t : GradientSpace (N := N) ⊤ q).snd i x))
  have hsub : Icc a b ⊆ Icc A B := fun t ht =>
    ⟨hAa.le.trans ht.1, ht.2.trans hbB.le⟩
  have hv := hp.1.mono_measure (Measure.restrict_mono hsub le_rfl)
  have hDi : IntegrableOn D (Icc a b) :=
    integrable_negative_half_power_graph_diffusion hX hc hpower hη hηb hv hz
  have hgrad := (ae_all_iff.mpr hp.2.2.2.1).filter_mono
    (ae_mono (Measure.restrict_mono hsub le_rfl))
  have hflux := hp.2.2.2.2.2.1.filter_mono
    (ae_mono (Measure.restrict_mono hsub le_rfl))
  have habs : ∀ᵐ t ∂volume.restrict (Icc a b),
      D t ≤ -p * F t (W.affineEnergyMap hX T w (c ^ (-p - 1)) (v t)) +
        2 * (upper * L) * m t := by
    filter_upwards [hz, hgrad, hflux, hcoeff_meas, hcoeff, herror]
      with t hzt hgt hft hmt hct het
    have hb (i j : Fin q) : ∀ᵐ x ∂volume, ‖coeff t x i j‖ ≤ upper := by
      filter_upwards [hct] with x hx
      exact norm_matrix_entry_le_of_elliptic_bounds (coeff t x) hell.le hx.1 hx.2 i j
    have hsp := W.negative_power_graph_flux_bound (fun i j x => coeff t x i j)
      hX hc hell hpower (v t) w (F t) hzt hw hdw hgt hft hplateau
      hW hWd hη hηb hmt hb hd hct
    dsimp only at hsp
    have he := mul_le_mul_of_nonneg_left het (show 0 ≤ 2 * upper by positivity)
    have heq : (∫ x, 2 * upper *
        ((v t : GradientSpace (N := N) ⊤ q).fst x + c) ^ (-p) *
          coordinateNormSq (fun i => d i x)) =
        2 * upper * (∫ x, ((v t : GradientSpace (N := N) ⊤ q).fst x + c) ^ (-p) *
          coordinateNormSq (fun i => d i x)) := by
      simp only [mul_assoc, integral_const_mul]
    rw [heq] at hsp
    exact hsp.2.2.trans (by dsimp only [D, T]; nlinarith only [he])
  obtain ⟨hEi, hbudget⟩ := hp.ae_terminal_reciprocal_energy_budget hX W hc hpower w
    hab.le hAa hbB hχ hχa (fun t ht => (hχunit t ht).1) hDi
    (hm.const_mul (2 * (upper * L))) habs
  have hEq : E =ᵐ[volume.restrict (Icc a b)] fun t =>
      ∫ x, η x ^ 2 * ((v t : GradientSpace (N := N) ⊤ q).fst x + c) ^ (-p) := by
    filter_upwards [hz] with t ht
    dsimp only [E, T]
    rw [negative_power_corrected_energy_eq_moment W hc hpower hWint w hw (v t) ht]
    simp only [hW]
  have hE0 : ∀ᵐ t ∂volume.restrict (Icc a b), 0 ≤ E t := by
    filter_upwards [hEq, hz] with t ht hn
    rw [ht]
    apply integral_nonneg_of_ae
    filter_upwards [hn] with x hx
    positivity
  have hEm : ∀ᵐ t ∂volume.restrict (Icc a b), E t ≤ m t / 1 := by
    filter_upwards [hEq, hvalue] with t ht hm'
    simpa only [ht, div_one] using hm'
  obtain ⟨hs, htotal⟩ := terminal_energy_budget_le_full_value_moment hab
    (by norm_num : (0 : ℝ) < 1) hHtime (mul_nonneg hupper hL)
    hEi hDi hm hm0 hE0 hEm hχ hχunit hχderiv hbudget
  change (∀ᵐ s ∂volume.restrict (Icc a b),
    χ s * E s + (∫ t in Icc a s, χ t * D t) ≤
      (Htime / 1 + 2 * (upper * L)) * (∫ t in Icc a b, m t)) at hs
  simp only [div_one] at hs htotal
  refine ⟨hDi, ?_, ?_⟩
  · filter_upwards [hs, hEq] with s hs' he
    simpa only [he, D, mul_assoc] using hs'
  · simpa only [D, mul_assoc] using htotal

end HeatKernel
