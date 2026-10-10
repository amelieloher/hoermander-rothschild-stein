-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.ReverseHolderAffineEnergy
public import HeatKernel.Moser.ReverseHolderCutoffIntegrability
import all Mathlib.Basic.Real.Basic
import all Mathlib.Analysis.Normed.Group.Real
import all Mathlib.Analysis.Normed.Field.Basic

/-! Normalization of affine concave-power energies as literal moments. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
namespace HeatKernel

/-- The affine primitive and an integrable spatial weight give integrability
of the literal concave-power moment from the original energy-space value. -/
theorem WeakSolutionSpatialWeight.integrable_reverse_holder_moment {N q : ℕ}
    {V : Opens (Fin N → ℝ)} {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    (W : WeakSolutionSpatialWeight V X) {c p : ℝ} (hc : 0 < c) (hp : 0 < p)
    (hp1 : p ≤ 1) (hW : Integrable W.toFun volume) (w : zeroBoundaryGraph V X)
    (hw : (w : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume] W.toFun)
    (z : zeroBoundaryGraph V X)
    (hz : ∀ᵐ x ∂volume, 0 ≤ (z : GradientSpace (N := N) ⊤ q).fst x) :
    Integrable (fun x => W.toFun x *
      ((z : GradientSpace (N := N) ⊤ q).fst x + c) ^ p) volume := by
  let T := shiftedRpowWeakSolutionTest hc (p := p - 1) (by linarith)
  have huLp : MemLp (z : GradientSpace (N := N) ⊤ q).fst 2 volume := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using
      Lp.memLp (z : GradientSpace (N := N) ⊤ q).fst
  have hwLp : MemLp W.toFun 2 volume := by
    have h := Lp.memLp (w : GradientSpace (N := N) ⊤ q).fst
    exact (memLp_congr_ae hw).mp (by
      simpa only [Opens.coe_top, Measure.restrict_univ] using h)
  have hl : Integrable (fun x => W.toFun x *
      (z : GradientSpace (N := N) ⊤ q).fst x) volume := hwLp.integrable_mul huLp
  have hi := (((W.integrable_energy_density T z).add (hl.const_mul (c ^ (p - 1)))).const_mul p).add (hW.const_mul (c ^ p))
  apply hi.congr
  filter_upwards [hz] with x hx
  simp only [Pi.add_apply]
  rw [reverse_holder_test_primitive hc hp hp1 hx]
  have hcancel : p *
      ((((z : GradientSpace (N := N) ⊤ q).fst x + c) ^ p - c ^ p) / p) =
        ((z : GradientSpace (N := N) ⊤ q).fst x + c) ^ p - c ^ p :=
    mul_div_cancel₀ _ hp.ne'
  calc
    _ = W.toFun x * (p *
        ((((z : GradientSpace (N := N) ⊤ q).fst x + c) ^ p - c ^ p) / p) + c ^ p) := by ring
    _ = _ := by rw [hcancel]; ring

/-- Restoring the constant of integration identifies the corrected affine
energy with the literal small-positive-power moment. -/
theorem reverse_holder_corrected_energy_eq_moment {N q : ℕ}
    {V : Opens (Fin N → ℝ)} {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    (W : WeakSolutionSpatialWeight V X) {c p : ℝ} (hc : 0 < c) (hp : 0 < p)
    (hp1 : p ≤ 1) (hW : Integrable W.toFun volume) (w : zeroBoundaryGraph V X)
    (hw : (w : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume] W.toFun)
    (z : zeroBoundaryGraph V X)
    (hz : ∀ᵐ x ∂volume, 0 ≤ (z : GradientSpace (N := N) ⊤ q).fst x) :
    c ^ p * (∫ x, W.toFun x) + p * W.affineEnergy
      (shiftedRpowWeakSolutionTest hc (p := p - 1) (by linarith))
        w (c ^ (p - 1)) z =
      ∫ x, W.toFun x * ((z : GradientSpace (N := N) ⊤ q).fst x + c) ^ p := by
  have hi := W.integrable_reverse_holder_moment hc hp hp1 hW w hw z hz
  have heq : W.affineEnergy
      (shiftedRpowWeakSolutionTest hc (p := p - 1) (by linarith))
        w (c ^ (p - 1)) z =
      ((∫ x, W.toFun x * ((z : GradientSpace (N := N) ⊤ q).fst x + c) ^ p) -
        c ^ p * (∫ x, W.toFun x)) / p := by
    rw [reverse_holder_affine_energy_eq W hc hp hp1 w hw z hz]
    calc
      _ = ∫ x, (W.toFun x * ((z : GradientSpace (N := N) ⊤ q).fst x + c) ^ p -
          c ^ p * W.toFun x) / p := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun x => by ring
      _ = _ := by rw [integral_div, integral_sub hi (hW.const_mul _), integral_const_mul]
  rw [heq]
  nlinarith [div_mul_cancel₀ ((∫ x, W.toFun x *
    ((z : GradientSpace (N := N) ⊤ q).fst x + c) ^ p) - c ^ p * (∫ x, W.toFun x)) hp.ne']

/-- A localization plateau transfers the normalized small-power moment to the
original solution, including the additive constant. -/
theorem reverse_holder_corrected_energy_eq_moment_of_plateau {N q : ℕ}
    {V : Opens (Fin N → ℝ)} {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)}
    (W : WeakSolutionSpatialWeight V X) {c p : ℝ} (hc : 0 < c) (hp : 0 < p)
    (hp1 : p ≤ 1) (hW : Integrable W.toFun volume) (w : zeroBoundaryGraph V X)
    (hw : (w : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume] W.toFun)
    (z : zeroBoundaryGraph V X)
    (hz : ∀ᵐ x ∂volume, 0 ≤ (z : GradientSpace (N := N) ⊤ q).fst x)
    {u φ : (Fin N → ℝ) → ℝ}
    (hval : (z : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume] fun x => u x * φ x)
    (hplateau : ∀ x, W.toFun x ≠ 0 → φ x = 1) :
    c ^ p * (∫ x, W.toFun x) + p * W.affineEnergy
      (shiftedRpowWeakSolutionTest hc (p := p - 1) (by linarith))
        w (c ^ (p - 1)) z = ∫ x, W.toFun x * (u x + c) ^ p := by
  rw [reverse_holder_corrected_energy_eq_moment W hc hp hp1 hW w hw z hz]
  apply integral_congr_ae
  filter_upwards [hval] with x hx
  by_cases hactive : W.toFun x = 0
  · simp only [hactive, zero_mul]
  · rw [hx, hplateau x hactive, mul_one]

end HeatKernel
