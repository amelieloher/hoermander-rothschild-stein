-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.NegativePowerAffineEnergy
public import HeatKernel.Moser.WeakSolutionAffineTimeTesting
public import HeatKernel.Moser.WeakSolutionEnergyRepresentatives
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import HeatKernel.Moser.TopExhaustionAffineEnergyTrace
public import HeatKernel.Moser.MeanValueTerminalMomentBudget

/-! # Almost-everywhere terminal reciprocal energy budgets -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace
namespace HeatKernel

/-- A spatial bound for the corrected negative-power flux gives terminal
budgets for the literal corrected energy at almost every interior time.
The affine correction and the constant of integration are both retained. -/
theorem IsZeroBoundaryWeakCutoffEnergyTimePair.ae_terminal_reciprocal_energy_budget
    {N q : ℕ} {V : Opens (Fin N → ℝ)}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    {coeff : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ}
    {u : ℝ → (Fin N → ℝ) → ℝ} {g : Fin q → ℝ → (Fin N → ℝ) → ℝ}
    {φ : (Fin N → ℝ) → ℝ} {k : Fin q → (Fin N → ℝ) → ℝ}
    {v : ℝ → zeroBoundaryGraph V X}
    {F : ℝ → (zeroBoundaryGraph V X →L[ℝ] ℝ)} {A B a b c p offset : ℝ}
    (hp : IsZeroBoundaryWeakCutoffEnergyTimePair V X coeff (Icc A B) u g φ k v F)
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (W : WeakSolutionSpatialWeight V X) (hc : 0 < c) (hpower : 0 < p)
    (w : zeroBoundaryGraph V X)
    (hab : a ≤ b) (hAa : A < a) (hbB : b < B)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ 1 χ) (hχa : χ a = 0)
    (hχ0 : ∀ t ∈ Icc a b, 0 ≤ χ t)
    {D R : ℝ → ℝ} (hD : IntegrableOn D (Icc a b))
    (hR : IntegrableOn R (Icc a b))
    (habsorb : ∀ᵐ t ∂volume.restrict (Icc a b),
      D t ≤ -p * F t (W.affineEnergyMap hX
        (shiftedRpowWeakSolutionTest hc (p := -p - 1) (by linarith))
          w (c ^ (-p - 1)) (v t)) + R t) :
    let E := fun t => offset - p * W.affineEnergy
      (shiftedRpowWeakSolutionTest hc (p := -p - 1) (by linarith))
        w (c ^ (-p - 1)) (v t)
    IntegrableOn E (Icc a b) ∧
      ∀ᵐ s ∂volume.restrict (Icc a b),
        χ s * E s + (∫ t in Icc a s, χ t * D t) ≤
          ∫ t in Icc a s, deriv χ t * E t + χ t * R t := by
  dsimp only
  let T := shiftedRpowWeakSolutionTest hc (p := -p - 1) (by linarith)
  let E := fun t => offset - p * W.affineEnergy T w (c ^ (-p - 1)) (v t)
  let f := fun t => -p * F t (W.affineEnergyMap hX T w (c ^ (-p - 1)) (v t))
  have hsubAB : Icc a b ⊆ Icc A B := fun t ht =>
    ⟨hAa.le.trans ht.1, ht.2.trans hbB.le⟩
  have hf : IntegrableOn f (Icc a b) :=
    ((hp.integrable_affine_energy_flux hX W T w (c ^ (-p - 1))).mono_set hsubAB).const_mul (-p)
  obtain ⟨e, hac, heq, hder⟩ := hp.exists_affine_energy_representative
    hX W T w (c ^ (-p - 1)) hab hAa hbB
  have hEi : IntegrableOn E (Icc a b) :=
    (integrableOn_const (s := Icc a b) (C := offset)
      (hs := isCompact_Icc.measure_lt_top.ne)).sub
      ((hp.integrableOn_affine_energy hX W T w (c ^ (-p - 1)) hab hAa hbB).const_mul p)
  have hχE : IntegrableOn (fun t => deriv χ t * E t) (Icc a b) :=
    IntegrableOn.continuousOn_mul hχ.continuous_deriv_one.continuousOn hEi isCompact_Icc
  have hχf : IntegrableOn (fun t => χ t * f t) (Icc a b) :=
    IntegrableOn.continuousOn_mul hχ.continuous.continuousOn hf isCompact_Icc
  have hχD : IntegrableOn (fun t => χ t * D t) (Icc a b) :=
    IntegrableOn.continuousOn_mul hχ.continuous.continuousOn hD isCompact_Icc
  have hχR : IntegrableOn (fun t => χ t * R t) (Icc a b) :=
    IntegrableOn.continuousOn_mul hχ.continuous.continuousOn hR isCompact_Icc
  have hac' : AbsolutelyContinuousOnInterval (fun t => offset - p * e t) A B := by
    have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => offset) A B :=
      contDiff_const.contDiffOn.absolutelyContinuousOnInterval
    simpa only [Pi.sub_def] using hconst.sub (hac.const_mul p)
  refine ⟨hEi, ?_⟩
  filter_upwards [heq, self_mem_ae_restrict measurableSet_Icc] with s hes hs
  have has : a ≤ s := hs.1
  have hsub : Icc a s ⊆ Icc a b := Icc_subset_Icc_right hs.2
  have hsubu : uIcc a s ⊆ uIcc A B := by
    rw [uIcc_of_le has, uIcc_of_le (show A ≤ B by linarith)]
    exact hsub.trans hsubAB
  have hid := hχ.contDiffOn.absolutelyContinuousOnInterval.integral_deriv_mul_eq_sub
    (hac'.mono hsubu)
  rw [hχa, zero_mul, sub_zero, intervalIntegral.integral_of_le has,
    ← integral_Icc_eq_integral_Ioc, hes] at hid
  have heq' := heq.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
  have hder' := ae_restrict_of_ae hder (s := Icc a s)
  have he : χ s * E s = ∫ t in Icc a s, deriv χ t * E t - χ t * f t := by
    rw [← hid]
    apply integral_congr_ae
    filter_upwards [heq', hder', self_mem_ae_restrict measurableSet_Icc] with t ht hd htab
    have hd' := (hasDerivAt_const t offset).sub
      ((hd ((hsub.trans hsubAB) htab)).const_mul p)
    change HasDerivAt (fun t => offset - p * e t) _ t at hd'
    rw [hd'.deriv, ht]
    dsimp only [E, f]
    ring
  have hsplit := integral_add ((hχE.sub hχf).mono_set hsub) (hχD.mono_set hsub)
  simp only [Pi.sub_apply] at hsplit
  rw [he, ← hsplit]
  apply integral_mono_ae (((hχE.sub hχf).add hχD).mono_set hsub)
    ((hχE.add hχR).mono_set hsub)
  have ha := habsorb.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
  filter_upwards [ha, self_mem_ae_restrict measurableSet_Icc] with t ht htab
  have hm := mul_le_mul_of_nonneg_left ht (hχ0 t (hsub htab))
  simp only [Pi.add_apply, Pi.sub_apply]
  dsimp only [f] at *
  linarith

end HeatKernel
