-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.C.C9Bridges
public import Hormander.C.Energy.Estimate
public import Hormander.B.Extension.Continuity
public import Hormander.Defs.HormanderOp
public import Hormander.B.Nested.RealDiffOps
public import Hormander.A.Mollifier.Kernel

open MeasureTheory SchwartzMap

@[expose] public section

noncomputable section

namespace Hormander.E
open Hormander.B

/-- An operator on `𝓢` together with a continuous bilinear transpose, so that it extends to
`𝓢'` by transposition. -/
structure ExtOp (N : ℕ) where
  op : Operator N
  tr : Operator N
  isTr : HasBilinearTranspose op tr
  cont : Continuous (fun u : TestFunction N => tr u)

variable {N : ℕ}

/-- The transposition extension to tempered distributions. -/
def ExtOp.ext (T : ExtOp N) : Tempered N →L[ℂ] Tempered N := tempExtension T.tr T.cont

theorem ExtOp.ext_apply (T : ExtOp N) (u : Tempered N) (φ : TestFunction N) :
    T.ext u φ = u (T.tr φ) := rfl

theorem ExtOp.ext_test (T : ExtOp N) (φ : TestFunction N) :
    T.ext (φ : Tempered N) = ((T.op φ : TestFunction N) : Tempered N) :=
  tempExtension_test T.isTr T.cont φ

theorem ExtOp.ext_congr {S T : ExtOp N} (h : S.op = T.op) : S.ext = T.ext := by
  have htr : S.tr = T.tr := HasBilinearTranspose.unique S.isTr (h ▸ T.isTr)
  ext u φ
  rw [ExtOp.ext_apply, ExtOp.ext_apply, htr]

/-- Composition. -/
def ExtOp.comp (S T : ExtOp N) : ExtOp N where
  op := S.op.comp T.op
  tr := T.tr.comp S.tr
  isTr := bilinearTranspose_comp S.isTr T.isTr
  cont := T.cont.comp S.cont

theorem ExtOp.ext_comp (S T : ExtOp N) : (S.comp T).ext = S.ext.comp T.ext := by
  ext u φ
  rfl

/-- Sum. -/
def ExtOp.add (S T : ExtOp N) : ExtOp N where
  op := S.op + T.op
  tr := S.tr + T.tr
  isTr := S.isTr.add T.isTr
  cont := S.cont.add T.cont

theorem ExtOp.ext_add (S T : ExtOp N) : (S.add T).ext = S.ext + T.ext := by
  ext u φ
  simp [ExtOp.ext_apply, ExtOp.add]

/-- Scalar multiples. -/
def ExtOp.smul (c : ℂ) (S : ExtOp N) : ExtOp N where
  op := c • S.op
  tr := c • S.tr
  isTr := S.isTr.smul c
  cont := S.cont.const_smul c

theorem ExtOp.ext_smul (c : ℂ) (S : ExtOp N) : (S.smul c).ext = c • S.ext := by
  ext u φ
  simp [ExtOp.ext_apply, ExtOp.smul]

/-- The multiplier by a real Schwartz function. -/
def ExtOp.realMult (ζ : SchwartzMap (Carrier N) ℝ) : ExtOp N where
  op := realMultiplierOperator ζ
  tr := realMultiplierOperator ζ
  isTr := extMultiplier_transpose ζ
  cont := (multiplierOperator_continuous _)

theorem ExtOp.ext_realMult (ζ : SchwartzMap (Carrier N) ℝ) :
    (ExtOp.realMult ζ).ext = cutoffDistr ζ := rfl

/-- Smart constructor from an operator with continuous transpose. -/
def ExtOp.ofTranspose (T : Operator N) (h : HasContinuousTranspose T) : ExtOp N where
  op := T
  tr := h.choose
  isTr := h.choose_spec.1
  cont := h.choose_spec.2.2

@[simp] theorem ExtOp.ofTranspose_op (T : Operator N) (h : HasContinuousTranspose T) :
    (ExtOp.ofTranspose T h).op = T := rfl


/-- Coordinate derivatives. -/
def ExtOp.coordDeriv (i : Fin N) : ExtOp N where
  op := coordinateDerivative i
  tr := -coordinateDerivative i
  isTr := coordinateDerivative_transpose i
  cont := (coordinateDerivative_continuous i).neg

theorem ExtOp.ext_coordDeriv (i : Fin N) (u : Tempered N) :
    (ExtOp.coordDeriv i).ext u =
      LineDeriv.lineDerivOp (EuclideanSpace.single i (1 : ℝ)) u := by
  ext φ
  rw [ExtOp.ext_apply, TemperedDistribution.lineDerivOp_apply_apply]
  simp [ExtOp.coordDeriv, coordinateDerivative]

/-- Real Schwartz vector fields. -/
def ExtOp.vectorField (V : RealSchwartzVectorField N) : ExtOp N where
  op := vectorFieldOperator V
  tr := -(vectorFieldOperator V) - realMultiplierOperator (vectorFieldDivergence V)
  isTr := vectorFieldOperator_transpose V
  cont := vectorFieldOperator_transpose_continuous V

/-- Mollifier. -/
def ExtOp.mollifier (N : ℕ) (δ : ℝ) (hδ : 0 < δ) : ExtOp N where
  op := mollifierOperator N δ hδ
  tr := mollifierOperator N δ hδ
  isTr := mollifierOperator_transpose δ hδ
  cont := mollifierOperator_continuous δ hδ

theorem ExtOp.ext_mollifier (δ : ℝ) (hδ : 0 < δ) (u : Tempered N) :
    (ExtOp.mollifier N δ hδ).ext u = Hormander.A.Sδ N δ hδ u := by
  ext φ
  rw [ExtOp.ext_apply, Hormander.A.Sδ_apply]
  rfl

/-- Zero. -/
def ExtOp.zero : ExtOp N where
  op := 0
  tr := 0
  isTr := HasBilinearTranspose.zero
  cont := continuous_const

/-- Finite sums. -/
theorem ExtOp.exists_sum {ι : Type*} (s : Finset ι) (S : ι → ExtOp N) :
    ∃ T : ExtOp N, T.op = ∑ i ∈ s, (S i).op ∧ T.ext = ∑ i ∈ s, (S i).ext := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨ExtOp.zero, rfl, ?_⟩
    ext u φ
    simp [ExtOp.ext_apply, ExtOp.zero]
  | insert a s ha ih =>
    obtain ⟨T, h1, h2⟩ := ih
    refine ⟨(S a).add T, ?_, ?_⟩
    · simp [ExtOp.add, h1, Finset.sum_insert ha]
    · rw [ExtOp.ext_add, h2, Finset.sum_insert ha]

theorem ExtOp.ext_vectorField (X : Carrier N → Carrier N) (V : RealSchwartzVectorField N)
    (hV : ∀ i x, V i x = X x i) (u : Tempered N) :
    (ExtOp.vectorField V).ext u = Hormander.vectorFieldOp X u := by
  obtain ⟨T, h1, h2⟩ := ExtOp.exists_sum Finset.univ
    (fun i => (ExtOp.realMult (V i)).comp (ExtOp.coordDeriv i))
  have hop : (ExtOp.vectorField V).op = T.op := by
    rw [h1]; rfl
  rw [ExtOp.ext_congr hop, h2]
  unfold Hormander.vectorFieldOp
  rw [sum_apply]
  simp only [sum_apply, ExtOp.ext_comp, ContinuousLinearMap.comp_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [ExtOp.ext_coordDeriv, ExtOp.ext_realMult]
  simp only [LineDeriv.lineDerivOpCLM_apply]
  have hfun : ⇑(complexifyRealSchwartz (V i)) = fun x => ((X x i : ℝ) : ℂ) := by
    funext x
    rw [complexifyRealSchwartz_apply, hV i x]
  unfold cutoffDistr
  rw [hfun]

end Hormander.E
