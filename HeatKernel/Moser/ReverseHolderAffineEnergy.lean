-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.WeakSolutionScalarTests
public import HeatKernel.Moser.WeakSolutionAffineIntegrals
import Mathlib.Tactic

/-! Concave-power affine energies for backward time estimates. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
namespace HeatKernel

/-- The normalized small-positive-power primitive retains the linear centering term. -/
theorem reverse_holder_test_primitive {c p s : ℝ}
    (hc : 0 < c) (hp : 0 < p) (hp1 : p ≤ 1) (hs : 0 ≤ s) :
    (shiftedRpowWeakSolutionTest hc (p := p - 1) (by linarith)).primitive s =
      ((s + c) ^ p - c ^ p) / p - s * c ^ (p - 1) := by
  let T := shiftedRpowWeakSolutionTest hc (p := p - 1) (by linarith)
  have hd : ∀ x ∈ uIcc (0 : ℝ) s,
      HasDerivAt (fun y : ℝ => (y + c) ^ p / p - y * c ^ (p - 1))
        (T.toFun x) x := by
    intro x hx
    have hx0 : 0 ≤ x := (uIcc_of_le hs ▸ hx).1
    have hpos : 0 < x + c := add_pos_of_nonneg_of_pos hx0 hc
    have he : T.toFun x = (x + c) ^ (p - 1) - c ^ (p - 1) :=
      Sobolev.zeroPreservingShiftedRpow_eq (c := c) (p := p - 1) hx0
    rw [he]
    convert (((Real.hasDerivAt_rpow_const (p := p) (Or.inl hpos.ne')).comp x
      ((hasDerivAt_id x).add_const c)).div_const p).sub
      ((hasDerivAt_id x).mul_const (c ^ (p - 1))) using 1 <;>
      simp only [Function.comp_def, mul_one, one_mul] <;>
      first | (ext y <;> dsimp) | field_simp [hp.ne']
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (T.lipschitz.continuous.intervalIntegrable 0 s)
  change (∫ x in (0 : ℝ)..s, T.toFun x) = _
  rw [he]
  simp only [zero_add, zero_mul, sub_zero]
  ring

/-- The fixed-test correction cancels the linear term in the normalized primitive. -/
theorem reverse_holder_affine_energy_eq {N q : ℕ}
    {V : Opens (Fin N → ℝ)} {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    (W : WeakSolutionSpatialWeight V X) {c p : ℝ} (hc : 0 < c) (hp : 0 < p) (hp1 : p ≤ 1)
    (w : zeroBoundaryGraph V X)
    (hw : (w : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume] W.toFun)
    (z : zeroBoundaryGraph V X)
    (hz : ∀ᵐ x ∂volume, 0 ≤ (z : GradientSpace (N := N) ⊤ q).fst x) :
    W.affineEnergy (shiftedRpowWeakSolutionTest hc (p := p - 1) (by linarith))
      w (c ^ (p - 1)) z = ∫ x, W.toFun x *
        ((((z : GradientSpace (N := N) ⊤ q).fst x + c) ^ p - c ^ p) / p) := by
  rw [W.affineEnergy_eq_integral _ w _ hw z]
  apply integral_congr_ae
  filter_upwards [hz] with x hx
  rw [reverse_holder_test_primitive hc hp hp1 hx]
  congr 1
  ring

end HeatKernel
