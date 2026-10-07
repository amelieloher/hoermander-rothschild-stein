-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.CoordinateFieldJetBounds
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Congr
public import Mathlib.Data.List.OfFn
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology
namespace RothschildStein.G3

/-- Ordinary coordinate partial derivatives, in the listed application order. -/
def coordinatePartialWord {N : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] :
    List (Fin N) → ((Fin N → ℝ) → F) → (Fin N → ℝ) → F
  | [], f => f
  | i :: I, f => fun x => fderiv ℝ (coordinatePartialWord I f) x (Pi.single i (1 : ℝ))

/-- Coordinate jet entries are the ordinary iterated coordinate derivatives. -/
theorem coordinatePartialWord_ofFn_eq_iteratedFDeriv {N k : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Ω : Set (Fin N → ℝ)} (hΩ : IsOpen Ω) {f : (Fin N → ℝ) → F}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f Ω) (dirs : Fin k → Fin N)
    {x : Fin N → ℝ} (hx : x ∈ Ω) :
    coordinatePartialWord (List.ofFn dirs) f x =
      iteratedFDeriv ℝ k f x (fun l => Pi.single (dirs l) (1 : ℝ)) := by
  induction k generalizing x with
  | zero => simp only [List.ofFn_zero,coordinatePartialWord,iteratedFDeriv_zero_apply]
  | succ k ih =>
    rw [List.ofFn_succ]
    change fderiv ℝ (coordinatePartialWord (List.ofFn (fun l => dirs l.succ)) f) x
      (Pi.single (dirs 0) (1 : ℝ)) = _
    have he : coordinatePartialWord (List.ofFn (fun l => dirs l.succ)) f =ᶠ[𝓝 x]
        (fun y => iteratedFDeriv ℝ k f y (fun l => Pi.single (dirs l.succ) (1 : ℝ))) := by
      filter_upwards [hΩ.mem_nhds hx] with y hy
      exact ih (fun l => dirs l.succ) hy
    rw [he.fderiv_eq]
    have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ k f) x :=
      ((hf.contDiffAt (hΩ.mem_nhds hx)).iteratedFDeriv_right
        (m := 1) (by simp)).differentiableAt (by simp)
    exact (hd.iteratedFDeriv_succ_apply_left'
      (m := fun l => Pi.single (dirs l) (1 : ℝ))).symm
end RothschildStein.G3
