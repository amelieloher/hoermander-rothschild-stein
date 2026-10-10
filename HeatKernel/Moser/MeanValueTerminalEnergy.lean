-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.WeakSolutionTimeTesting
import Mathlib.Tactic

/-! # Terminal energy budgets from the nonlinear weak time equation -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace
namespace HeatKernel

/-- Pointwise absorption of the actual nonlinear flux gives the terminal energy
budget after multiplication by a smooth nonnegative time cutoff. Dissipation
integrability follows from absorption; neither a terminal budget nor time
regularity of the original solution is assumed. The absorption and cutoff-error
integrability are explicit spatial inputs. -/
theorem IsZeroBoundaryWeakCutoffEnergyTimePair.ae_terminal_spatial_energy_budget
    {N q : ℕ} {V : Opens (Fin N → ℝ)}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    {coeff : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ}
    {u : ℝ → (Fin N → ℝ) → ℝ} {g : Fin q → ℝ → (Fin N → ℝ) → ℝ}
    {φ : (Fin N → ℝ) → ℝ} {k : Fin q → (Fin N → ℝ) → ℝ}
    {v : ℝ → zeroBoundaryGraph V X}
    {F : ℝ → (zeroBoundaryGraph V X →L[ℝ] ℝ)} {A B a b : ℝ}
    (hp : IsZeroBoundaryWeakCutoffEnergyTimePair V X coeff (Icc A B) u g φ k v F)
    (W : WeakSolutionSpatialWeight V X) (T : WeakSolutionScalarTest)
    (hab : a ≤ b) (hAa : A < a) (hbB : b < B)
    {χ : ℝ → ℝ} (hχ : ContDiff ℝ 1 χ) (hχa : χ a = 0)
    (hχ0 : ∀ t ∈ Icc a b, 0 ≤ χ t)
    {D R : ℝ → ℝ}
    (hD : AEStronglyMeasurable D (volume.restrict (Icc a b)))
    (hD0 : ∀ᵐ t ∂volume.restrict (Icc a b), 0 ≤ D t)
    (hR : IntegrableOn R (Icc a b))
    (habsorb : ∀ᵐ t ∂volume.restrict (Icc a b),
      D t ≤ F t (W.energyMap hX T (v t)) + R t) :
    IntegrableOn D (Icc a b) ∧
      ∀ᵐ s ∂volume.restrict (Icc a b),
        χ s * W.energy T (v s) + (∫ t in Icc a s, χ t * D t) ≤
          ∫ t in Icc a s, deriv χ t * W.energy T (v t) + χ t * R t := by
  let f : ℝ → ℝ := fun t => F t (W.energyMap hX T (v t))
  have hsubAB : Icc a b ⊆ Icc A B := fun t ht =>
    ⟨hAa.le.trans ht.1, ht.2.trans hbB.le⟩
  have hf : IntegrableOn f (Icc a b) :=
    (hp.integrable_spatial_energy_flux hX W T).mono_set hsubAB
  have hDi : IntegrableOn D (Icc a b) := (hf.add hR).mono' hD (by
    filter_upwards [hD0, habsorb] with t ht ha
    simpa only [Real.norm_eq_abs, abs_of_nonneg ht, Pi.add_apply] using ha)
  obtain ⟨e, hac, heq, hder⟩ := hp.exists_spatial_energy_representative hX W T hab hAa hbB
  have hEi := hp.integrableOn_spatial_energy hX W T hab hAa hbB
  have hχE : IntegrableOn (fun t => deriv χ t * W.energy T (v t)) (Icc a b) :=
    IntegrableOn.continuousOn_mul hχ.continuous_deriv_one.continuousOn hEi isCompact_Icc
  have hχf : IntegrableOn (fun t => χ t * f t) (Icc a b) :=
    IntegrableOn.continuousOn_mul hχ.continuous.continuousOn hf isCompact_Icc
  have hχD : IntegrableOn (fun t => χ t * D t) (Icc a b) :=
    IntegrableOn.continuousOn_mul hχ.continuous.continuousOn hDi isCompact_Icc
  have hχR : IntegrableOn (fun t => χ t * R t) (Icc a b) :=
    IntegrableOn.continuousOn_mul hχ.continuous.continuousOn hR isCompact_Icc
  refine ⟨hDi, ?_⟩
  filter_upwards [heq, self_mem_ae_restrict measurableSet_Icc] with s hes hs
  have has : a ≤ s := hs.1
  have hsub : Icc a s ⊆ Icc a b := Icc_subset_Icc_right hs.2
  have hsubu : uIcc a s ⊆ uIcc A B := by
    rw [uIcc_of_le has, uIcc_of_le (show A ≤ B by linarith)]
    exact hsub.trans hsubAB
  have hid := hχ.contDiffOn.absolutelyContinuousOnInterval.integral_deriv_mul_eq_sub
    (hac.mono hsubu)
  rw [hχa, zero_mul, sub_zero, intervalIntegral.integral_of_le has,
    ← integral_Icc_eq_integral_Ioc, hes] at hid
  have heq' := heq.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
  have hder' := ae_restrict_of_ae hder (s := Icc a s)
  have he : χ s * W.energy T (v s) =
      ∫ t in Icc a s, deriv χ t * W.energy T (v t) - χ t * f t := by
    rw [← hid]
    apply integral_congr_ae
    filter_upwards [heq', hder', self_mem_ae_restrict measurableSet_Icc] with t ht hd htab
    rw [ht, (hd ((hsub.trans hsubAB) htab)).deriv]
    dsimp [f]
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
  linarith

end HeatKernel
