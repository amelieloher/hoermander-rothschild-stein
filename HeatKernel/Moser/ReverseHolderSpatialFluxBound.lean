-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.ReverseHolderPhysicalFlux
public import HeatKernel.Moser.ReverseHolderAffineFlux
import all Mathlib.Basic.Real.Basic
import all Mathlib.Analysis.Normed.Group.Defs
import all Mathlib.Analysis.Normed.Group.Basic
import all Mathlib.Analysis.Normed.Group.Continuity
import all Mathlib.Analysis.Normed.Group.Real
import all Mathlib.Analysis.Normed.Field.Basic

/-! Spatial concave-power absorption for the actual localized weak flux. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
namespace HeatKernel

/-- Each coordinate of the physical concave-power flux is integrable from
bounded coefficients and cutoffs and the original square-integrable gradients. -/
theorem integrable_reverse_holder_coordinate_flux {α ι : Type*}
    [MeasurableSpace α] [Fintype ι] {μ : Measure α}
    {a : ι → ι → α → ℝ} {u η : α → ℝ} {g d : ι → α → ℝ}
    {c C K p : ℝ} (hc : 0 < c) (hp2 : p ≤ 1 / 2)
    (hu : AEStronglyMeasurable u μ) (hupos : ∀ᵐ x ∂μ, 0 ≤ u x)
    (hη : AEStronglyMeasurable η μ) (hηbound : ∀ᵐ x ∂μ, ‖η x‖ ≤ K)
    (ha : ∀ i j, AEStronglyMeasurable (a i j) μ)
    (hb : ∀ i j, ∀ᵐ x ∂μ, ‖a i j x‖ ≤ C)
    (hg : ∀ i, MemLp (g i) 2 μ) (hd : ∀ i, MemLp (d i) 2 μ) (i : ι) :
    Integrable (fun x => (∑ j, a i j x * g j x) *
      (η x ^ 2 * (p - 1) * (u x + c) ^ (p - 2) * g i x +
        (2 * η x * d i x) * (u x + c) ^ (p - 1))) μ := by
  have hprincipal := memLp_two_mul_of_ae_bound hη
    (memLp_two_mul_of_ae_bound hη
      (memLp_shifted_nonpositive_power_mul hc (by linarith : p - 2 ≤ 0)
        hu hupos (hg i)) hηbound) hηbound
  have hmixed := memLp_two_mul_of_ae_bound hη
    (memLp_shifted_nonpositive_power_mul hc (by linarith : p - 1 ≤ 0)
      hu hupos (hd i)) hηbound
  have hrow : MemLp (fun x => ∑ j, a i j x * g j x) 2 μ :=
    memLp_finsetSum _ fun j _ => memLp_two_mul_of_ae_bound (ha i j) (hg j) (hb i j)
  have htest := (hprincipal.const_mul (p - 1)).add (hmixed.const_mul 2)
  have hprod := hrow.integrable_mul htest
  apply hprod.congr
  exact Filter.Eventually.of_forall fun x => by simp only [Pi.mul_def, Pi.add_def]; ring

/-- On a localization plateau, the affine-corrected weak test supplies the
spatial concave-power absorption bound. The weighted cutoff gradient is
assumed square integrable; the remaining density integrability is derived. -/
theorem WeakSolutionSpatialWeight.reverse_holder_flux_bound_of_plateau {N q : ℕ}
    {V : Opens (Fin N → ℝ)}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    (W : WeakSolutionSpatialWeight V X) (a : Fin q → Fin q → (Fin N → ℝ) → ℝ)
    {u φ η : (Fin N → ℝ) → ℝ} {g k d : Fin q → (Fin N → ℝ) → ℝ}
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    {c C K ell upper p : ℝ} (hc : 0 < c) (hell : 0 < ell) (hp : 0 < p) (hp2 : p ≤ 1 / 2)
    (z w : zeroBoundaryGraph V X) (F : zeroBoundaryGraph V X →L[ℝ] ℝ)
    (hz : ∀ᵐ x ∂volume, 0 ≤ (z : GradientSpace (N := N) ⊤ q).fst x)
    (hw : (w : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume] W.toFun)
    (hdw : ∀ i, (w : GradientSpace (N := N) ⊤ q).snd i =ᵐ[volume] W.gradient i)
    (hval : (z : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume] fun x => u x * φ x)
    (hgrad : ∀ i, (z : GradientSpace (N := N) ⊤ q).snd i =ᵐ[volume]
      fun x => g i x * φ x + u x * k i x)
    (hflux : ∀ v, F v = ∑ i, ∫ x, (∑ j, a i j x * g j x) *
      (φ x * (v : GradientSpace (N := N) ⊤ q).snd i x +
        k i x * (v : GradientSpace (N := N) ⊤ q).fst x))
    (hplateau : ∀ x, W.toFun x ≠ 0 ∨ (∃ i, W.gradient i x ≠ 0) →
      φ x = 1 ∧ ∀ i, k i x = 0)
    (hW : ∀ x, W.toFun x = η x ^ 2) (hWd : ∀ i x, W.gradient i x = 2 * η x * d i x)
    (hu : AEStronglyMeasurable u volume) (hupos : ∀ᵐ x ∂volume, 0 ≤ u x)
    (hη : AEStronglyMeasurable η volume) (hηbound : ∀ᵐ x ∂volume, ‖η x‖ ≤ K)
    (ha : ∀ i j, AEStronglyMeasurable (a i j) volume)
    (hb : ∀ i j, ∀ᵐ x ∂volume, ‖a i j x‖ ≤ C)
    (hg : ∀ i, MemLp (g i) 2 volume) (hd : ∀ i, MemLp (d i) 2 volume)
    (hcut : ∀ i, MemLp (fun x => (u x + c) ^ (p / 2) * d i x) 2 volume)
    (hcoeff : ∀ᵐ x ∂volume, (∀ i j, a i j x = a j i x) ∧ ∀ ξ : Fin q → ℝ,
      ell * coordinateNormSq ξ ≤ matrixEnergy (fun i j => a i j x) ξ ∧
      matrixEnergy (fun i j => a i j x) ξ ≤ upper * coordinateNormSq ξ) :
    let D := fun x => 2 * ell * (p / 2) ^ 2 * coordinateNormSq
      (fun i => η x * ((u x + c) ^ (p / 2 - 1) * g i x))
    let R := fun x => 2 * upper * (u x + c) ^ p * coordinateNormSq (fun i => d i x)
    Integrable D volume ∧ Integrable R volume ∧
      (∫ x, D x) ≤ -p * F (W.affineEnergyMap hX
        (shiftedRpowWeakSolutionTest hc (p := p - 1) (by linarith))
          w (c ^ (p - 1)) z) + ∫ x, R x := by
  dsimp only
  obtain ⟨hD, _, hR, hbound⟩ := integrable_reverse_holder_physical_flux_and_bound
    hc hell hp hp2 hu hupos hη hηbound ha hb hg hcut hcoeff
  have hFeq := W.reverse_holder_test_flux_eq_of_plateau a hX hc (by linarith : p ≤ 1) z w F
    hz hw hdw hval hgrad hflux hplateau
  have hi := integrable_reverse_holder_coordinate_flux hc hp2 hu hupos hη hηbound ha hb hg hd
  have heq : F (W.affineEnergyMap hX
      (shiftedRpowWeakSolutionTest hc (p := p - 1) (by linarith))
        w (c ^ (p - 1)) z) = ∫ x, ∑ i, (∑ j, a i j x * g j x) *
      (η x ^ 2 * (p - 1) * (u x + c) ^ (p - 2) * g i x +
        (2 * η x * d i x) * (u x + c) ^ (p - 1)) := by
    rw [hFeq, integral_finsetSum _ (fun i _ => hi i)]
    apply Finset.sum_congr rfl
    intro i _
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => by dsimp only; rw [hW, hWd]; ring
  exact ⟨hD, hR, by rw [heq]; exact hbound⟩

end HeatKernel
