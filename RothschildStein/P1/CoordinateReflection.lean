-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.FiniteCoordinateHomogeneity
public import Mathlib.Analysis.Calculus.FDeriv.Mul

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter TopologicalSpace
open scoped Topology
namespace RothschildStein.P1

/-- Reflection reverses each coordinate derivative, with only
punctured C¹ regularity (BB (11.12), p. 546). -/
theorem coordinateDerivative_comp_neg {N : ℕ} (j : Fin N)
    {f : (Fin N → ℝ) → ℝ} (hf : ContDiffOn ℝ 1 f {(0 : Fin N → ℝ)}ᶜ)
    {x : Fin N → ℝ} (hx : x ≠ 0) :
    fieldDerivative (G2.coordinateFields j) (fun y => f (-y)) x =
      -fieldDerivative (G2.coordinateFields j) f (-x) := by
  have hfx : DifferentiableAt ℝ f (-x) :=
    (hf.contDiffAt (isOpen_compl_singleton.mem_nhds
      (show -x ∈ {(0 : Fin N → ℝ)}ᶜ by simpa using hx))).differentiableAt (by norm_num)
  have hneg : HasFDerivAt (fun y : Fin N → ℝ => -y)
      (-ContinuousLinearMap.id ℝ (Fin N → ℝ)) x := (hasFDerivAt_id x).neg
  unfold fieldDerivative
  change fderiv ℝ (f ∘ fun y => -y) x (Hormander.Interface.basisVec j) = _
  rw [fderiv_comp x hfx hneg.differentiableAt, hneg.fderiv]
  change fderiv ℝ f (-x) (-(Hormander.Interface.basisVec j)) = _
  rw [map_neg]
  rfl

/-- Reflection contributes (-1)^length to a coordinate word.
Only that many punctured derivatives are required, so the result applies
to singular fundamental kernels without a smooth extension at zero. -/
theorem coordinateWord_comp_neg {N : ℕ} (l : List (Fin N))
    {f : (Fin N → ℝ) → ℝ} (hf : ContDiffOn ℝ l.length f {(0 : Fin N → ℝ)}ᶜ) :
    ∀ x, x ≠ 0 → wordDerivative G2.coordinateFields l (fun y => f (-y)) x =
      (-1 : ℝ) ^ l.length * wordDerivative G2.coordinateFields l f (-x) := by
  induction l with
  | nil => intro x hx; simp [wordDerivative]
  | cons j l ih =>
    have ht := ih (hf.of_le (by simp))
    let U : Opens (Fin N → ℝ) := ⟨{0}ᶜ, isOpen_compl_singleton⟩
    have hX (a : Fin N) : ContDiffOn ℝ (⊤ : ℕ∞) (G2.coordinateFields a)
        (U : Set (Fin N → ℝ)) := contDiffOn_const
    have hg : ContDiffOn ℝ 1 (wordDerivative G2.coordinateFields l f)
        {(0 : Fin N → ℝ)}ᶜ :=
      S.contDiffOn_wordDerivative_finite U G2.coordinateFields hX l 1 f
        (by change ContDiffOn ℝ (1 + l.length : ℕ) f {(0 : Fin N → ℝ)}ᶜ
            simpa only [List.length_cons, Nat.add_comm] using hf)
    intro x hx
    have he : (wordDerivative G2.coordinateFields l (fun y => f (-y))) =ᶠ[𝓝 x]
        (fun y => (-1 : ℝ) ^ l.length * wordDerivative G2.coordinateFields l f (-y)) := by
      filter_upwards [isOpen_compl_singleton.mem_nhds
        (show x ∈ {(0 : Fin N → ℝ)}ᶜ by simpa using hx)] with y hy
      exact ht y (by simpa using hy)
    change fderiv ℝ (wordDerivative G2.coordinateFields l (fun y => f (-y))) x
      (Hormander.Interface.basisVec j) = _
    rw [he.fderiv_eq]
    change fderiv ℝ (((-1 : ℝ) ^ l.length) •
      (fun y => wordDerivative G2.coordinateFields l f (-y))) x
      (Hormander.Interface.basisVec j) = _
    rw [fderiv_const_smul_field]
    change (-1 : ℝ) ^ l.length *
      fieldDerivative (G2.coordinateFields j) (fun y => wordDerivative G2.coordinateFields l f (-y)) x = _
    rw [coordinateDerivative_comp_neg j hg hx]
    simp only [List.length_cons, pow_succ, wordDerivative]
    ring

end RothschildStein.P1
