-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.BoundedSquares
public import HeatKernel.Moser.WeakSolutionCompactSpatialTests
import Mathlib.Tactic
import all HeatKernel.Moser.WeakSolutionSpatialWeights
import all Mathlib.Basic.Real.Basic

/-! # Squared compact spatial weights with the exact logarithmic product gradient -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace RothschildStein
namespace HeatKernel

/-- A bounded compact energy cutoff supplies its squared spatial multiplier and
fixed zero-boundary test, both with the exact doubled cutoff gradient. -/
theorem exists_squared_logarithmic_spatial_weight {N q : ℕ}
    (V : Opens (Fin N → ℝ)) (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    {η : (Fin N → ℝ) → ℝ} (e : energyGraph (N := N) ⊤ X)
    (hη : Continuous η) (hc : HasCompactSupport η) (hs : tsupport η ⊆ (V : Set (Fin N → ℝ)))
    (hv : (e : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume] η)
    (hb : ∀ᵐ x ∂volume, ‖η x‖ ≤ 1) {L : ℝ} (hL : 0 ≤ L)
    (hg : ∀ i, ∀ᵐ x ∂volume, ‖(e : GradientSpace (N := N) ⊤ q).snd i x‖ ≤ L) :
    ∃ W : WeakSolutionSpatialWeight V X, ∃ w : zeroBoundaryGraph V X,
      W.toFun = (fun x => η x ^ 2) ∧
      W.gradient = (fun i x => 2 * η x * (e : GradientSpace (N := N) ⊤ q).snd i x) ∧
      (w : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume] W.toFun ∧
      ∀ i, (w : GradientSpace (N := N) ⊤ q).snd i =ᵐ[volume] W.gradient i := by
  have heb : ∀ᵐ x ∂volume, ‖(e : GradientSpace (N := N) ⊤ q).fst x‖ ≤ 1 := by
    filter_upwards [hv, hb] with x hx hbx
    simpa only [hx] using hbx
  obtain ⟨z, hz, hdz⟩ := exists_energyGraph_square_of_ae_bound X hX e (by norm_num) heb
  have hval : (z : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume] fun x => η x ^ 2 := by
    filter_upwards [hz, hv] with x hx hηx
    rw [hx, hηx]
  have hgrad (i : Fin q) : (z : GradientSpace (N := N) ⊤ q).snd i =ᵐ[volume]
      fun x => 2 * η x * (e : GradientSpace (N := N) ⊤ q).snd i x := by
    filter_upwards [hdz i, hv] with x hx hηx
    rw [hx, hηx]
  have hlocal : MemLocalEnergy ⊤ X (fun x => η x ^ 2) := by
    refine ⟨(hη.pow 2).aestronglyMeasurable, ?_⟩
    intro U _ _
    exact ⟨z, ae_restrict_of_ae hval⟩
  have hweak (i : Fin q) : hasWeakWordDeriv X ⊤ [i] (fun x => η x ^ 2)
      (fun x => 2 * η x * (e : GradientSpace (N := N) ⊤ q).snd i x) := by
    apply S.hasWeakWordDeriv_congr_ae X ⊤
      (energyGraph_le_weakGradientGraph ⊤ X (fun j => (hX j).contDiffOn) z.property i)
    · simpa only [Opens.coe_top, Measure.restrict_univ] using hval
    · simpa only [Opens.coe_top, Measure.restrict_univ] using hgrad i
  have hbound : ∀ᵐ x ∂volume, ‖η x ^ 2‖ ≤ (1 : ℝ) := by
    filter_upwards [hb] with x hx
    simpa only [norm_pow] using pow_le_one₀ (norm_nonneg _) hx
  have hdb (i : Fin q) : ∀ᵐ x ∂volume,
      ‖2 * η x * (e : GradientSpace (N := N) ⊤ q).snd i x‖ ≤ (Real.toNNReal (2 * L) : ℝ) := by
    filter_upwards [hb, hg i] with x hx hd
    rw [Real.coe_toNNReal _ (mul_nonneg (by norm_num) hL), norm_mul, norm_mul]
    norm_num only [Real.norm_ofNat]
    calc
      2 * ‖η x‖ * ‖(e : GradientSpace (N := N) ⊤ q).snd i x‖ ≤ 2 * 1 * L :=
        mul_le_mul (mul_le_mul_of_nonneg_left hx (by norm_num)) hd (norm_nonneg _) (by norm_num)
      _ = 2 * L := by ring
  have hsquare : tsupport (fun x => η x ^ 2) ⊆ tsupport η := by
    apply closure_mono
    intro x hx
    change η x ≠ 0
    intro hz
    exact hx (by simp only [hz, zero_pow (by norm_num : (2 : ℕ) ≠ 0)])
  have hcompact : HasCompactSupport (fun x => η x ^ 2) :=
    hc.of_isClosed_subset (isClosed_tsupport _) hsquare
  have hsupport : tsupport (fun x => η x ^ 2) ⊆ (V : Set (Fin N → ℝ)) := hsquare.trans hs
  let W := WeakSolutionSpatialWeight.ofBoundedWeakGradient V X hX hlocal hweak
    1 (Real.toNNReal (2 * L)) hbound hdb hcompact hsupport
  obtain ⟨w, hw, hdw⟩ := exists_compact_spatial_energy_test V X hX hlocal hweak hcompact hsupport
  exact ⟨W, w, rfl, rfl, hw, hdw⟩

end HeatKernel
