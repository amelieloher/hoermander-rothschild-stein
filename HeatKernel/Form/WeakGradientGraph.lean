-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.WeakGraph
public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.FunProp

/-!
# The closed graph of a weak horizontal gradient

The graph is a closed linear subspace of the Hilbert product of the function and its finitely
many scalar derivatives. Its first projection is injective by uniqueness of weak derivatives.
-/

@[expose] public section

noncomputable section

open Set MeasureTheory TopologicalSpace
open scoped ENNReal Topology

namespace HeatKernel

/-- Spatial L² on an open coordinate set. -/
abbrev SpatialL2 {N : ℕ} (U : Opens (Fin N → ℝ)) :=
  Lp ℝ 2 (volume.restrict (U : Set (Fin N → ℝ)))

/-- Hilbert product of a function and its scalar horizontal derivatives. -/
abbrev GradientSpace {N : ℕ} (U : Opens (Fin N → ℝ)) (q : ℕ) :=
  WithLp 2 (SpatialL2 U × PiLp 2 (fun _ : Fin q => SpatialL2 U))

variable {N q : ℕ} (U : Opens (Fin N → ℝ))
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (U : Set (Fin N → ℝ)))

/-- The subspace consisting of a function and its weak first-order derivatives. -/
def weakGradientGraph : Submodule ℝ (GradientSpace U q) where
  carrier := {v | ∀ i, RothschildStein.hasWeakWordDeriv X U [i] v.fst (v.snd i)}
  zero_mem' := by
    intro i
    exact RothschildStein.S.hasWeakWordDeriv_congr_ae X U
      (RothschildStein.S.hasWeakWordDeriv_zero X U [i])
      (Lp.coeFn_zero _ _ _).symm (Lp.coeFn_zero _ _ _).symm
  add_mem' := by
    intro v w hv hw i
    exact RothschildStein.S.hasWeakWordDeriv_congr_ae X U
      (RothschildStein.S.hasWeakWordDeriv_add X U hX (hv i) (hw i))
      (Lp.coeFn_add v.fst w.fst).symm (Lp.coeFn_add (v.snd i) (w.snd i)).symm
  smul_mem' := by
    intro c v hv i
    exact RothschildStein.S.hasWeakWordDeriv_congr_ae X U
      (RothschildStein.S.hasWeakWordDeriv_smul X U (hv i) c)
      (Lp.coeFn_smul c v.fst).symm (Lp.coeFn_smul c (v.snd i)).symm

/-- The weak-gradient graph is closed in the Hilbert product topology. -/
theorem isClosed_weakGradientGraph : IsClosed (weakGradientGraph U X hX : Set (GradientSpace U q)) := by
  change IsClosed {v : GradientSpace U q | ∀ i,
    RothschildStein.hasWeakWordDeriv X U [i] v.fst (v.snd i)}
  simp only [ofPred_forall]
  apply isClosed_iInter
  intro i
  exact (RothschildStein.S.isClosed_weakWordGraph U X hX [i] 2 2).preimage
    (f := fun v : GradientSpace U q => (v.fst, v.snd i)) (by fun_prop)

/-- Two elements of the weak-gradient graph with the same function have the same gradient. -/
theorem weakGradientGraph_fst_injective :
    Function.Injective (fun v : weakGradientGraph U X hX => (v : GradientSpace U q).fst) := by
  intro v w h
  apply Subtype.ext
  apply (WithLp.equiv 2 _).injective
  apply Prod.ext h
  apply PiLp.ext
  intro i
  apply Lp.ext
  have hw := w.property i
  change (v : GradientSpace U q).fst = (w : GradientSpace U q).fst at h
  rw [← h] at hw
  exact RothschildStein.S.hasWeakWordDeriv_unique X U (v.property i) hw

end HeatKernel
