-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.ReverseHolderAffineEnergy
public import HeatKernel.Moser.WeakSolutionAffineTimeTesting
public import HeatKernel.Moser.ReverseHolderTimeWeightedBudget
public import HeatKernel.Moser.TopExhaustionAffineEnergyTrace
import all Mathlib.Basic.Real.Basic
import all Mathlib.Analysis.Normed.Group.Real
import all Mathlib.Analysis.Normed.Field.Basic
import all Mathlib.Analysis.Normed.Ring.Basic
import all Mathlib.Analysis.Normed.Operator.Basic
import all Mathlib.Analysis.Normed.Operator.NormedSpace
import all Mathlib.Analysis.InnerProductSpace.Basic
import all Mathlib.Analysis.RCLike.Basic
import all Mathlib.Analysis.InnerProductSpace.Defs
import all Mathlib.Analysis.Normed.Module.Basic

/-! Backward concave-power budgets from the weak time equation. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
namespace HeatKernel

/-- A spatial absorption bound gives a backward small-positive-power budget
for an absolutely continuous representative. The upper time cutoff vanishes;
the absorption input is needed only on the tested compact interval. -/
theorem exists_reverse_holder_initial_energy_budgets_of_flux_bound
    {N q : ℕ} {V : Opens (Fin N → ℝ)}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    {coeff : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ}
    {u : ℝ → (Fin N → ℝ) → ℝ} {g : Fin q → ℝ → (Fin N → ℝ) → ℝ}
    {φ : (Fin N → ℝ) → ℝ} {k : Fin q → (Fin N → ℝ) → ℝ}
    {v : ℝ → zeroBoundaryGraph V X}
    {F : ℝ → (zeroBoundaryGraph V X →L[ℝ] ℝ)} {A B a b c p : ℝ}
    (hpair : IsZeroBoundaryWeakCutoffEnergyTimePair V X coeff (Icc A B) u g φ k v F)
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (W : WeakSolutionSpatialWeight V X) (hc : 0 < c) (hp1 : p ≤ 1)
    (w : zeroBoundaryGraph V X) (offset : ℝ)
    (hab : a ≤ b) (hAa : A < a) (hbB : b < B)
    (D R : ℝ → ℝ) (hD : IntegrableOn D (Icc a b)) (hR : IntegrableOn R (Icc a b))
    (habs : ∀ᵐ t ∂volume.restrict (Icc a b),
      D t ≤ -p * F t (W.affineEnergyMap hX
        (shiftedRpowWeakSolutionTest hc (p := p - 1) (by linarith))
          w (c ^ (p - 1)) (v t)) + R t)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ 1 χ) (hχb : χ b = 0)
    (hχpos : ∀ᵐ t ∂volume, 0 ≤ χ t) :
    let T := shiftedRpowWeakSolutionTest hc (p := p - 1) (by linarith)
    ∃ e : ℝ → ℝ, AbsolutelyContinuousOnInterval e a b ∧
      e =ᵐ[volume.restrict (Icc a b)]
        (fun t => offset + p * W.affineEnergy T w (c ^ (p - 1)) (v t)) ∧
      ∀ s ∈ Icc a b, χ s * e s + (∫ t in s..b, χ t * D t) ≤
        (∫ t in s..b, -(deriv χ t) * e t) + ∫ t in s..b, χ t * R t := by
  dsimp only
  let T := shiftedRpowWeakSolutionTest hc (p := p - 1) (by linarith)
  let f := fun t => F t (W.affineEnergyMap hX T w (c ^ (p - 1)) (v t))
  obtain ⟨e, he, heq, hder⟩ := hpair.exists_affine_energy_representative hX W T w
    (c ^ (p - 1)) hab hAa hbB
  have hsub : uIcc a b ⊆ uIcc A B := by
    rw [uIcc_of_le hab, uIcc_of_le (show A ≤ B by linarith)]
    exact fun t ht => ⟨hAa.le.trans ht.1, ht.2.trans hbB.le⟩
  have hac : AbsolutelyContinuousOnInterval (fun t => offset + p * e t) a b := by
    have hconst : AbsolutelyContinuousOnInterval (fun _ : ℝ => offset) a b :=
      contDiff_const.contDiffOn.absolutelyContinuousOnInterval
    simpa only [Pi.add_def] using hconst.add (AbsolutelyContinuousOnInterval.const_mul p (he.mono hsub))
  have hd : ∀ᵐ t ∂volume, t ∈ uIcc a b →
      HasDerivAt (fun t => offset + p * e t) (-p * f t) t := by
    filter_upwards [hder] with t ht
    intro htab
    have htAB : t ∈ Icc A B := by
      rw [← uIcc_of_le (show A ≤ B by linarith)]
      exact hsub htab
    convert (hasDerivAt_const t offset).add ((ht htAB).const_mul p) using 1; ring
  have hf : IntervalIntegrable (fun t => -p * f t) volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    exact ((hpair.integrable_affine_energy_flux hX W T w (c ^ (p - 1))).mono_set
      (fun t ht => ⟨hAa.le.trans ht.1, ht.2.trans hbB.le⟩)).const_mul (-p)
  have hDi : IntervalIntegrable D volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr hD
  have hRi : IntervalIntegrable R volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr hR
  refine ⟨fun t => offset + p * e t, hac, ?_, ?_⟩
  · filter_upwards [heq] with t ht
    rw [ht]
  · let R' := fun t => if t ∈ Icc a b then R t else D t + p * f t
    have hReq : R' =ᵐ[volume.restrict (Icc a b)] R := by
      filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
      simp only [R', ite_eq_left ht]
    have hRi' : IntervalIntegrable R' volume a b :=
      (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr (hR.congr hReq.symm)
    have habs' : ∀ᵐ t ∂volume, D t ≤ -p * f t + R' t := by
      filter_upwards [(ae_restrict_iff' measurableSet_Icc).mp habs] with t ht
      by_cases htab : t ∈ Icc a b
      · simpa only [R', ite_eq_left htab] using ht htab
      · simp only [R', ite_eq_right htab]
        linarith
    have hbudget := reverse_holder_time_weighted_initial_budgets hab hac hd hf hDi hRi'
      habs' hχ hχb hχpos
    intro s hs
    have hb := hbudget s hs
    have hi : (∫ t in s..b, χ t * R' t) = ∫ t in s..b, χ t * R t := by
      apply intervalIntegral.integral_congr_ae
      exact Filter.Eventually.of_forall fun t ht => by
        have htab : t ∈ Icc a b := by
          have hts : t ∈ Icc s b := by
            rw [← uIcc_of_le hs.2]
            exact uIoc_subset_uIcc ht
          exact ⟨hs.1.trans hts.1, hts.2⟩
        simp only [R', ite_eq_left htab]
    rw [hi] at hb
    exact hb

end HeatKernel
