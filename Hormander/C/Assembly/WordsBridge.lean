-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.C.Assembly.Bridge
public import Hormander.C.Induction.Words
public import Hormander.C.Words

@[expose] public section

noncomputable section
open MeasureTheory SchwartzMap
namespace Hormander.C
open Hormander.B
variable {N k : ℕ}

theorem fderiv_eq_sum_real (f : Carrier N → ℝ) (y v : Carrier N) :
    fderiv ℝ f y v = ∑ j : Fin N, (v j) * fderiv ℝ f y (EuclideanSpace.single j (1 : ℝ)) := by
  have hv : v = ∑ j : Fin N, (v j) • EuclideanSpace.single j (1 : ℝ) := by
    have := (EuclideanSpace.basisFun (Fin N) ℝ).sum_repr v
    simpa [EuclideanSpace.basisFun_apply, EuclideanSpace.basisFun_repr] using this.symm
  conv_lhs => rw [hv]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, smul_eq_mul]

/-- The pointwise vector of a Schwartz field. -/
def fieldVec (A : RealSchwartzVectorField N) (x : Carrier N) : Carrier N :=
  WithLp.toLp 2 (fun j => A j x)

theorem fieldVec_differentiable (A : RealSchwartzVectorField N) :
    Differentiable ℝ (fieldVec A) := by
  intro x
  exact differentiableAt_euclidean.2 fun j => (A j).differentiableAt

theorem fderiv_fieldVec_proj (A : RealSchwartzVectorField N) (x w : Carrier N) (m : Fin N) :
    fderiv ℝ (fieldVec A) x w m = fderiv ℝ (A m) x w := by
  have h := (EuclideanSpace.proj (𝕜 := ℝ) m).hasFDerivAt.comp x
    ((fieldVec_differentiable A x).hasFDerivAt)
  have h2 : HasFDerivAt (A m) ((EuclideanSpace.proj (𝕜 := ℝ) m).comp (fderiv ℝ (fieldVec A) x)) x := h
  rw [h2.fderiv]
  rfl

theorem bracketField_fieldVec (A B : RealSchwartzVectorField N) (x : Carrier N) :
    fieldVec (bracketField A B) x = VectorField.lieBracket ℝ (fieldVec A) (fieldVec B) x := by
  ext m
  unfold VectorField.lieBracket
  simp only [PiLp.sub_apply]
  have h0 : (fieldVec (bracketField A B) x).ofLp m = bracketField A B m x := rfl
  rw [h0, bracketField_apply, fderiv_fieldVec_proj B x (fieldVec A x) m,
    fderiv_fieldVec_proj A x (fieldVec B x) m, fderiv_eq_sum_real (B m) x (fieldVec A x),
    fderiv_eq_sum_real (A m) x (fieldVec B x), ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [fieldVec]

/-- The right-nested index list of a standard word. -/
def nestedToList {k : ℕ} : NestedWord k → List (Fin (k + 1))
  | .generator i => [i]
  | .bracket i w => i :: nestedToList w

theorem nestedToList_length {k : ℕ} (w : NestedWord k) : (nestedToList w).length = nestedLength w := by
  induction w with
  | generator i => rfl
  | bracket i w ih => simp [nestedToList, nestedLength, ih]

theorem nestedLength_pos {k : ℕ} (w : NestedWord k) : 1 ≤ nestedLength w := by
  cases w <;> simp [nestedLength]

theorem wordField_fieldVec {k : ℕ} (Xs : Fin (k + 1) → RealSchwartzVectorField N)
    (X : Fin (k + 1) → Carrier N → Carrier N) (hXs : ∀ i x j, Xs i j x = X i x j)
    (w : NestedWord k) : fieldVec (wordField Xs (nestedToList w)) = nestedEval X w := by
  have hgen : ∀ i, fieldVec (Xs i) = X i := fun i => by
    funext x; ext j; exact hXs i x j
  induction w with
  | generator i => exact hgen i
  | bracket i w ih =>
    cases w with
    | generator a =>
      funext x
      simp only [nestedToList, wordField]
      rw [bracketField_fieldVec, hgen, hgen a]
      rfl
    | bracket a w' =>
      funext x
      simp only [nestedToList, wordField] at ih ⊢
      rw [bracketField_fieldVec, hgen, ih]
      rfl

/-- The Schwartz field of an integer combination of standard words. -/
def combField {k : ℕ} (Xs : Fin (k + 1) → RealSchwartzVectorField N) :
    WordCombination k → RealSchwartzVectorField N
  | [] => 0
  | (n, w) :: rest => (n : ℝ) • wordField Xs (nestedToList w) + combField Xs rest

theorem combField_fieldVec {k : ℕ} (Xs : Fin (k + 1) → RealSchwartzVectorField N)
    (X : Fin (k + 1) → Carrier N → Carrier N) (hXs : ∀ i x j, Xs i j x = X i x j)
    (c : WordCombination k) : fieldVec (combField Xs c) = combinationEval X c := by
  induction c with
  | nil => funext x; ext j; rfl
  | cons z rest ih =>
    obtain ⟨n, w⟩ := z
    funext x
    have hw := congrFun (wordField_fieldVec Xs X hXs w) x
    have hr := congrFun ih x
    ext j
    simp only [combField, combinationEval]
    have e1 : (fieldVec ((n : ℝ) • wordField Xs (nestedToList w) + combField Xs rest) x).ofLp j =
        (n : ℝ) * (wordField Xs (nestedToList w)) j x + (combField Xs rest) j x := rfl
    rw [e1]
    have e2 := congrArg (fun v : Carrier N => v.ofLp j) hw
    have e3 := congrArg (fun v : Carrier N => v.ofLp j) hr
    simp only [fieldVec] at e2 e3
    rw [e2, e3]
    simp

theorem vf_add (A B : RealSchwartzVectorField N) :
    vectorFieldOperator (A + B) = vectorFieldOperator A + vectorFieldOperator B := by
  ext u x
  simp only [LinearMap.add_apply, add_apply, vectorFieldOperator_apply, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast; ring

theorem vf_smul (r : ℝ) (A : RealSchwartzVectorField N) :
    vectorFieldOperator (r • A) = (r : ℂ) • vectorFieldOperator A := by
  ext u x
  simp only [LinearMap.smul_apply, smul_apply, vectorFieldOperator_apply, Pi.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast; ring

theorem vf_zero : vectorFieldOperator (0 : RealSchwartzVectorField N) = 0 := by
  ext u x
  simp [vectorFieldOperator_apply]

theorem comb_norm_le {k : ℕ} (Xs : Fin (k + 1) → RealSchwartzVectorField N) (s : ℝ)
    (c : WordCombination k) (u : TestFunction N) :
    sobolevNorm s (vectorFieldOperator (combField Xs c) u) ≤
      (c.map fun z => |(z.1 : ℝ)| * sobolevNorm s
        (vectorFieldOperator (wordField Xs (nestedToList z.2)) u)).sum := by
  induction c with
  | nil =>
    simp [combField, vf_zero]
  | cons z rest ih =>
    obtain ⟨n, w⟩ := z
    simp only [combField, vf_add, vf_smul, LinearMap.add_apply, LinearMap.smul_apply, List.map_cons,
      List.sum_cons]
    refine (sobolevNorm_add_le s _ _).trans ?_
    rw [sobolevNorm_smul]
    simp only [Complex.norm_real, Real.norm_eq_abs]
    have := add_le_add_left ih (|(n : ℝ)| * sobolevNorm s (vectorFieldOperator (wordField Xs (nestedToList w)) u))
    simpa using this

end Hormander.C
