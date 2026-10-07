-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.Defs.LieWordEval
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Congr

@[expose] public section

noncomputable section

open Filter Set Topology

namespace Hormander.F

/-- Recursive evaluation of a Lie word preserves smoothness on an open
set when each generator is smooth there. -/
theorem lieWordEval_contDiffOn {k : ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {W : Set E} (hW : IsOpen W)
    (X : Fin (k + 1) → E → E)
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) W) :
    ∀ w : Hormander.Interface.LieWord k,
      ContDiffOn ℝ (⊤ : ℕ∞) (Hormander.lieWordEval X w) W := by
  intro w
  induction w with
  | generator i => exact hX i
  | bracket p q hp hq =>
      intro x hx
      have hpAt : ContDiffAt ℝ (⊤ : ℕ∞) (Hormander.lieWordEval X p) x :=
        (hp x hx).contDiffAt (hW.mem_nhds hx)
      have hqAt : ContDiffAt ℝ (⊤ : ℕ∞) (Hormander.lieWordEval X q) x :=
        (hq x hx).contDiffAt (hW.mem_nhds hx)
      exact (hpAt.lieBracket_vectorField hqAt (by simp)).contDiffWithinAt

/-- Lie words evaluated on two generator families agree throughout any open
set on which the generators agree. -/
theorem lieWordEval_eqOn_of_eqOn {k : ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {W : Set E} (hW : IsOpen W)
    (X Y : Fin (k + 1) → E → E)
    (hXY : ∀ i, EqOn (X i) (Y i) W) :
    ∀ w : Hormander.Interface.LieWord k, EqOn (Hormander.lieWordEval X w)
      (Hormander.lieWordEval Y w) W := by
  intro w
  induction w with
  | generator i => exact hXY i
  | bracket p q hp hq =>
      intro x hx
      have hpNear :
          Hormander.lieWordEval X p =ᶠ[𝓝 x] Hormander.lieWordEval Y p := by
        filter_upwards [hW.mem_nhds hx] with y hy
        exact hp hy
      have hqNear :
        Hormander.lieWordEval X q =ᶠ[𝓝 x] Hormander.lieWordEval Y q := by
        filter_upwards [hW.mem_nhds hx] with y hy
        exact hq hy
      have hpDeriv := hpNear.fderiv_eq (𝕜 := ℝ)
      have hqDeriv := hqNear.fderiv_eq (𝕜 := ℝ)
      change VectorField.lieBracket ℝ (Hormander.lieWordEval X p)
          (Hormander.lieWordEval X q) x =
        VectorField.lieBracket ℝ (Hormander.lieWordEval Y p)
          (Hormander.lieWordEval Y q) x
      change fderiv ℝ (Hormander.lieWordEval X q) x
          (Hormander.lieWordEval X p x) -
        fderiv ℝ (Hormander.lieWordEval X p) x
          (Hormander.lieWordEval X q x) =
        fderiv ℝ (Hormander.lieWordEval Y q) x
          (Hormander.lieWordEval Y p x) -
        fderiv ℝ (Hormander.lieWordEval Y p) x
          (Hormander.lieWordEval Y q x)
      rw [hqDeriv, hpDeriv, hp hx, hq hx]

end Hormander.F
