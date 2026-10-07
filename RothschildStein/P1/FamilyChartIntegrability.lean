-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.GaugeChartIntegrability
public import RothschildStein.P1.KernelEstimatesChart

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory

namespace RothschildStein.P1

variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}

/-- A jointly smooth homogeneous family of positive type is absolutely
integrable in the actual input chart on a compact endpoint patch.
The diagonal value is unrestricted. -/
theorem LiftedChart.integrableOn_family_comp_theta
    (C : LiftedChart w s Ω hΩ X x₀ m)
    (Ψ : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ)
    (d : ℤ) (hd : -(C.G.homogeneousDimension : ℤ) < d)
    (hΨ : ContDiffOn ℝ (⊤ : ℕ∞) (kernelUncurry Ψ) {z | z.2.2 ≠ 0})
    (hbound : HasWeightedBounds C.G d Ψ)
    (L : Set (Fin (n + m) → ℝ)) (hL : IsCompact L) (hLU : L ⊆ C.U)
    (ξ : Fin (n + m) → ℝ) (hξ : ξ ∈ L)
    (K : Set (Fin (n + m) → ℝ)) (hK : IsCompact K) (hKL : K ⊆ L) :
    IntegrableOn (fun η => Ψ ξ η (C.Θ η ξ)) K := by
  let rsFamilyFinNonempty : Nonempty (Fin (n + m)) := ⟨⟨0, C.G.dimension_pos⟩⟩
  let E := K \ {ξ}
  have hE : MeasurableSet E := hK.measurableSet.diff (measurableSet_singleton ξ)
  have hKU : K ⊆ C.U := hKL.trans hLU
  have hξU : ξ ∈ C.U := hLU hξ
  obtain ⟨R, hR⟩ := C.exists_gauge_bound hL hLU
  obtain ⟨M, hM, hb⟩ := hbound L hL R
  have hreg : ContinuousOn (fun η => Ψ ξ η (C.Θ η ξ)) E := by
    have hmap : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun η : Fin (n + m) → ℝ => (ξ, η, C.Θ η ξ)) E :=
      contDiffOn_const.prodMk (contDiffOn_id.prodMk
        ((C.contDiffOn_Θ_fst hξU).mono (sdiff_subset.trans hKU)))
    exact (hΨ.comp hmap (fun η hη =>
      (C.theta_eq_zero_iff (hKU hη.1) hξU).not.mpr (fun he => hη.2 (mem_singleton_iff.mpr he.symm)))).continuousOn
  have hmajor : IntegrableOn (fun η => M * kgauge C.G (C.Θ η ξ) ^ d) E :=
    ((C.integrableOn_gauge_power_theta d hd ξ hξU K hK hKU).mono_set sdiff_subset).const_mul M
  have hint : IntegrableOn (fun η => Ψ ξ η (C.Θ η ξ)) E := by
    apply MeasureTheory.Integrable.mono hmajor (hreg.aestronglyMeasurable hE)
    apply ae_restrict_of_forall_mem hE
    intro η hη
    have hne : ξ ≠ η := fun he => hη.2 (mem_singleton_iff.mpr he.symm)
    have hu : C.Θ η ξ ≠ 0 := (C.theta_eq_zero_iff (hKU hη.1) hξU).not.mpr hne
    have hs := (hb ξ hξ η (hKL hη.1) (C.Θ η ξ) hu (hR η (hKL hη.1) ξ hξ)).1
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg hM (zpow_nonneg (kgauge_nonneg C.G _) _))]
    exact hs
  have he : E =ᵐ[volume] K := by
    filter_upwards [volume.ae_ne ξ] with η hη
    simp only [E, mem_sdiff, mem_singleton_iff, hη, not_false_eq_true, and_true]
  exact (integrableOn_congr_set_ae he).mp hint

end RothschildStein.P1
