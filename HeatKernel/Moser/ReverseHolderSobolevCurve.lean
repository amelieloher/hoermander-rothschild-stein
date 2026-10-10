-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.ReverseHolderSobolevEnergy
public import HeatKernel.Moser.WeakSolutionConvexEnergy
import all Mathlib.Basic.Real.Basic
import all Mathlib.Analysis.Normed.Group.Submodule
import all Mathlib.Analysis.Normed.Group.Defs
import all Mathlib.Analysis.Normed.Group.Basic
import all Mathlib.Analysis.Normed.Group.Continuity
import all Mathlib.Analysis.Normed.Group.Real
import all Mathlib.Analysis.Normed.Field.Basic
import all Mathlib.Analysis.Normed.Ring.Basic
import all Mathlib.Analysis.Normed.Operator.Basic
import all Mathlib.Analysis.Normed.Operator.NormedSpace
import all Mathlib.Analysis.InnerProductSpace.Basic
import all Mathlib.Analysis.RCLike.Basic
import all Mathlib.Analysis.InnerProductSpace.Defs
import all Mathlib.Analysis.Normed.Module.Basic

/-! Small-positive-power graph curves and their literal quadratic energies. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
namespace HeatKernel

/-- Adding a fixed spatial correction preserves square integrability of the
nonlinear test curve on a finite time measure. -/
theorem WeakSolutionSpatialWeight.memLp_affineEnergyMap {N q : ℕ}
    {V : Opens (Fin N → ℝ)} {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    (W : WeakSolutionSpatialWeight V X) (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (T : WeakSolutionScalarTest) (w : zeroBoundaryGraph V X) (c : ℝ)
    {μ : Measure ℝ} [IsFiniteMeasure μ] {v : ℝ → zeroBoundaryGraph V X}
    (hv : MemLp v 2 μ) :
    MemLp (fun t => W.affineEnergyMap hX T w c (v t)) 2 μ := by
  have hP := W.multiplier.comp_memLp' (T.memLp_energyMap V X hX hv)
  set_option backward.isDefEq.respectTransparency false in
    simpa only [WeakSolutionSpatialWeight.affineEnergyMap,
      WeakSolutionSpatialWeight.energyMap, Function.comp_apply, Pi.add_def] using
      hP.add (memLp_const (c • w))

/-- The affine half-power curve has the literal small-power value moment and
the full horizontal product gradient. Diffusion and the cutoff-gradient moment
control its gradient norm independently of the small exponent. The comparison
of the cutoff-gradient moment with the outer moment is an explicit geometric input. -/
theorem WeakSolutionSpatialWeight.reverse_holder_affine_graph_energy_bounds {N q : ℕ}
    {V : Opens (Fin N → ℝ)} {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    (W : WeakSolutionSpatialWeight V X) (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    {u φ : (Fin N → ℝ) → ℝ} {g k : Fin q → (Fin N → ℝ) → ℝ}
    {c p K ell L m : ℝ} (hc : 0 < c) (hp2 : p ≤ 1 / 2) (hell : 0 < ell)
    (z w : zeroBoundaryGraph V X)
    (hz : ∀ᵐ x ∂volume, 0 ≤ (z : GradientSpace (N := N) ⊤ q).fst x)
    (hw : (w : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume] W.toFun)
    (hdw : ∀ i, (w : GradientSpace (N := N) ⊤ q).snd i =ᵐ[volume] W.gradient i)
    (hval : (z : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume] fun x => u x * φ x)
    (hgrad : ∀ i, (z : GradientSpace (N := N) ⊤ q).snd i =ᵐ[volume]
      fun x => g i x * φ x + u x * k i x)
    (hplateau : ∀ x, W.toFun x ≠ 0 ∨ (∃ i, W.gradient i x ≠ 0) →
      φ x = 1 ∧ ∀ i, k i x = 0)
    (hu : AEStronglyMeasurable u volume) (hupos : ∀ᵐ x ∂volume, 0 ≤ u x)
    (hWbound : ∀ᵐ x ∂volume, ‖W.toFun x‖ ≤ K)
    (hg : ∀ i, MemLp (g i) 2 volume)
    (hcut : ∀ i, MemLp (fun x => (u x + c) ^ (p / 2) * W.gradient i x) 2 volume)
    (hcutMoment : (∫ x, (u x + c) ^ p * coordinateNormSq (fun i => W.gradient i x)) ≤ L * m) :
    let Z := W.affineEnergyMap hX
      (shiftedRpowWeakSolutionTest hc (p := p / 2) (by linarith)) w (c ^ (p / 2)) z
    ‖(Z : GradientSpace (N := N) ⊤ q).fst‖ ^ 2 =
        (∫ x, W.toFun x ^ 2 * (u x + c) ^ p) ∧
      ‖(Z : GradientSpace (N := N) ⊤ q).snd‖ ^ 2 ≤
        (∫ x, 2 * ell * (p / 2) ^ 2 * coordinateNormSq
          (fun i => W.toFun x * ((u x + c) ^ (p / 2 - 1) * g i x))) / ell + 2 * L * m := by
  dsimp only
  let Z := W.affineEnergyMap hX
    (shiftedRpowWeakSolutionTest hc (p := p / 2) (by linarith)) w (c ^ (p / 2)) z
  obtain ⟨hv, hd⟩ := W.shifted_rpow_affine_representatives_of_plateau hX
    hc (by linarith : p / 2 ≤ 1) z w hz hw hdw hval hgrad hplateau
  obtain ⟨hnv, hnd⟩ := Sobolev.gradientSpace_norms_sq_eq_integrals_of_ae_eq
    (Z : GradientSpace (N := N) ⊤ q) hv hd
  obtain ⟨_, _, _, henergy⟩ := integrable_reverse_holder_product_gradient_energy_and_bound
    hc hp2 hu hupos W.aestronglyMeasurable hWbound hg hcut
  constructor
  · rw [hnv]
    apply integral_congr_ae
    filter_upwards [hupos] with x hx
    have hs : 0 < u x + c := add_pos_of_nonneg_of_pos hx hc
    have hp : ((u x + c) ^ (p / 2)) ^ 2 = (u x + c) ^ p := by
      rw [pow_two, ← Real.rpow_add hs]
      congr 1
      ring
    simp only [mul_pow, hp]
  · rw [hnd]
    have hscale : 2 * (∫ x, (p / 2) ^ 2 * coordinateNormSq
        (fun i => W.toFun x * ((u x + c) ^ (p / 2 - 1) * g i x))) =
        (∫ x, 2 * ell * (p / 2) ^ 2 * coordinateNormSq
          (fun i => W.toFun x * ((u x + c) ^ (p / 2 - 1) * g i x))) / ell := by
      simp only [integral_const_mul]
      field_simp
    rw [hscale] at henergy
    have hcutle : 2 * (∫ x, (u x + c) ^ p *
        coordinateNormSq (fun i => W.gradient i x)) ≤ 2 * L * m := by
      nlinarith only [hcutMoment]
    exact henergy.trans (add_le_add le_rfl hcutle)

end HeatKernel
