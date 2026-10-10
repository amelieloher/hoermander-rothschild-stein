-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.NegativePowerEnergyEndpoints
public import HeatKernel.Moser.CaccioppoliSpatialPowerTest
public import HeatKernel.Moser.WeakSolutionAffineEnergyIdentity

/-! Shifted real-power chain rules on nonnegative energy-space values. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory Filter
open scoped Topology
namespace HeatKernel

/-- The centered shifted power has the ordinary power derivative on positive inputs. -/
theorem hasDerivAt_shifted_rpow_test {c r s : ℝ}
    (hc : 0 < c) (hr : r ≤ 1) (hs : 0 < s) :
    HasDerivAt (shiftedRpowWeakSolutionTest hc hr).toFun (r * (s + c) ^ (r - 1)) s := by
  have hd := ((Real.hasDerivAt_rpow_const (p := r)
    (Or.inl (add_pos hs hc).ne')).comp s
      ((hasDerivAt_id s).add_const c)).sub_const (c ^ r)
  have hd' : HasDerivAt (fun t : ℝ => (t + c) ^ r - c ^ r)
      (r * (s + c) ^ (r - 1)) s := by
    simpa only [Function.comp_def, id_eq, mul_one] using hd
  apply hd'.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds hs] with t ht
  exact Sobolev.zeroPreservingShiftedRpow_eq (c := c) (p := r) ht.le

/-- The centered shifted-power gradient formula holds at zero levels as well,
since an energy-space weak gradient vanishes on a constant level set. -/
theorem WeakSolutionSpatialWeight.shifted_rpow_energyMap_gradient_ae {N q : ℕ}
    {V : TopologicalSpace.Opens (Fin N → ℝ)}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    (W : WeakSolutionSpatialWeight V X) (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    {c r : ℝ} (hc : 0 < c) (hr : r ≤ 1) (z : zeroBoundaryGraph V X) (i : Fin q)
    (hz : ∀ᵐ x ∂volume, 0 ≤ (z : GradientSpace (N := N) ⊤ q).fst x) :
    (W.energyMap hX (shiftedRpowWeakSolutionTest hc hr) z :
      GradientSpace (N := N) ⊤ q).snd i =ᵐ[volume] fun x =>
      W.toFun x * ((r * ((z : GradientSpace (N := N) ⊤ q).fst x + c) ^ (r - 1)) *
        (z : GradientSpace (N := N) ⊤ q).snd i x) +
      W.gradient i x * (((z : GradientSpace (N := N) ⊤ q).fst x + c) ^ r - c ^ r) := by
  filter_upwards [W.energyMap_gradient_ae hX (shiftedRpowWeakSolutionTest hc hr) z i, hz,
    energyGraph_gradient_zero_on_level X hX (zeroBoundaryEnergyInclusion V X z) 0 i]
    with x hx hnonneg hzero
  by_cases hs : 0 < (z : GradientSpace (N := N) ⊤ q).fst x
  · rw [hx, (hasDerivAt_shifted_rpow_test hc hr hs).deriv]
    rw [show (shiftedRpowWeakSolutionTest hc hr).toFun
      ((z : GradientSpace (N := N) ⊤ q).fst x) = _ from
        Sobolev.zeroPreservingShiftedRpow_eq (c := c) (p := r) hs.le]
  · have heq : (z : GradientSpace (N := N) ⊤ q).fst x = 0 :=
      le_antisymm (le_of_not_gt hs) hnonneg
    have hg : (z : GradientSpace (N := N) ⊤ q).snd i x = 0 := hzero heq
    rw [hx, hg, heq]
    simp [WeakSolutionScalarTest.map_zero]

/-- The affine correction restores the uncentered power in the cutoff-gradient
term while preserving the principal shifted-power chain rule. -/
theorem WeakSolutionSpatialWeight.shifted_rpow_affine_gradient_ae {N q : ℕ}
    {V : TopologicalSpace.Opens (Fin N → ℝ)}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    (W : WeakSolutionSpatialWeight V X) (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    {c r : ℝ} (hc : 0 < c) (hr : r ≤ 1) (z w : zeroBoundaryGraph V X)
    (hz : ∀ᵐ x ∂volume, 0 ≤ (z : GradientSpace (N := N) ⊤ q).fst x)
    (hdw : ∀ i, (w : GradientSpace (N := N) ⊤ q).snd i =ᵐ[volume] W.gradient i)
    (i : Fin q) :
    (W.affineEnergyMap hX (shiftedRpowWeakSolutionTest hc hr)
      w (c ^ r) z : GradientSpace (N := N) ⊤ q).snd i =ᵐ[volume]
      fun x => W.toFun x * ((r *
        ((z : GradientSpace (N := N) ⊤ q).fst x + c) ^ (r - 1)) *
        (z : GradientSpace (N := N) ⊤ q).snd i x) +
        W.gradient i x * ((z : GradientSpace (N := N) ⊤ q).fst x + c) ^ r := by
  let P := W.energyMap hX (shiftedRpowWeakSolutionTest hc hr) z
  have ha := Lp.coeFn_add ((P : GradientSpace (N := N) ⊤ q).snd i)
    (c ^ r • (w : GradientSpace (N := N) ⊤ q).snd i)
  have hs := Lp.coeFn_smul (c ^ r) ((w : GradientSpace (N := N) ⊤ q).snd i)
  simp only [TopologicalSpace.Opens.coe_top, Measure.restrict_univ] at ha hs
  filter_upwards [ha, hs, W.shifted_rpow_energyMap_gradient_ae hX hc hr z i hz, hdw i]
    with x hax hsx hpx hwx
  change ((P : GradientSpace (N := N) ⊤ q).snd i +
    c ^ r • (w : GradientSpace (N := N) ⊤ q).snd i) x = _
  rw [hax]
  simp only [Pi.add_apply]
  rw [hsx]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hpx, hwx]
  ring

end HeatKernel
