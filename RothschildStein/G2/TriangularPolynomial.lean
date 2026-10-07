-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.Algebra
public import RothschildStein.G2.WeightedPolynomial
public import Mathlib.Algebra.MvPolynomial.Variables
public import Mathlib.Algebra.MvPolynomial.PDeriv

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
namespace RothschildStein.G2
open MvPolynomial
open scoped BigOperators
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Polynomial correction to the additive coordinate law (BB (3.5), p. 96). -/
def correction (k : Fin N) : MvPolynomial (Fin N ⊕ Fin N) ℝ :=
  G.productPolynomial k - X (Sum.inl k) - X (Sum.inr k)

/-- Every product coordinate is weighted homogeneous (BB Theorem 3.6, pp. 96–97). -/
theorem product_weightedHomogeneous (k : Fin N) :
    (G.productPolynomial k).IsWeightedHomogeneous (Sum.elim G.weight G.weight) (G.weight k) := by
  apply weightedHomogeneous_of_eval_dilate
  intro t ht z
  let x : Fin N → ℝ := fun j => z (Sum.inl j)
  let y : Fin N → ℝ := fun j => z (Sum.inr j)
  have h := congrFun (dilate_product G ht x y) k
  dsimp [HomogeneousGroup.dilate, coordinateDilation, HomogeneousGroup.mul, polynomialProduct] at h
  have hxy : Sum.elim x y = z := by ext i; cases i <;> rfl
  have hd : Sum.elim (coordinateDilation G.weight t x) (coordinateDilation G.weight t y) =
      (fun i => t ^ Sum.elim G.weight G.weight i * z i) := by
    ext i
    cases i <;> rfl
  rw [hxy, hd] at h
  exact h.symm

/-- The correction is weighted homogeneous (BB (3.5), p. 96). -/
theorem correction_weightedHomogeneous (k : Fin N) :
    (correction G k).IsWeightedHomogeneous (Sum.elim G.weight G.weight) (G.weight k) :=
  ((product_weightedHomogeneous G k).sub (isWeightedHomogeneous_X ℝ (Sum.elim G.weight G.weight) (Sum.inl k))).sub
    (isWeightedHomogeneous_X ℝ (Sum.elim G.weight G.weight) (Sum.inr k))

/-- Evaluation gives the additive part and its polynomial correction (BB (3.5), p. 96). -/
theorem mul_coordinate (x y : Fin N → ℝ) (k : Fin N) :
    G.mul x y k = x k + y k + eval (Sum.elim x y) (correction G k) := by
  simp only [correction, map_sub, eval_X, Sum.elim_inl, Sum.elim_inr,
    HomogeneousGroup.mul, polynomialProduct]
  ring

/-- The correction vanishes when the second argument is zero (BB (3.5), p. 96). -/
theorem correction_eval_zero_right (x : Fin N → ℝ) (k : Fin N) :
    eval (Sum.elim x 0) (correction G k) = 0 := by
  have h := mul_coordinate G x 0 k
  rw [mul_zero] at h
  simpa using (add_left_cancel (a := x k) (by simpa using h.symm))

/-- The correction vanishes when the first argument is zero (BB (3.5), p. 96). -/
theorem correction_eval_zero_left (y : Fin N → ℝ) (k : Fin N) :
    eval (Sum.elim 0 y) (correction G k) = 0 := by
  have h := mul_coordinate G 0 y k
  rw [zero_mul] at h
  simpa using (add_left_cancel (a := y k) (by simpa using h.symm))

private theorem killCompl_X_image {α β : Type*} (f : α → β) (hf : Function.Injective f)
    (j : α) : (killCompl (R := ℝ) hf) (X (f j)) = X j := by
  rw [← rename_X f, killCompl_rename_app]

private theorem killCompl_X_outside {α β : Type*} (f : α → β) (hf : Function.Injective f)
    (j : β) (hj : j ∉ Set.range f) : (killCompl (R := ℝ) hf) (X j) = 0 := by
  simp [killCompl, hj]

private theorem eval_killCompl_inl (p : MvPolynomial (Fin N ⊕ Fin N) ℝ) (x : Fin N → ℝ) :
    eval x (p.killCompl Sum.inl_injective) = eval (Sum.elim x 0) p := by
  have h : (eval x).comp (killCompl (R := ℝ) (f := (Sum.inl : Fin N → Fin N ⊕ Fin N)) Sum.inl_injective).toRingHom =
      eval (Sum.elim x 0) := by
    apply ringHom_ext
    · intro r
      simp
    · intro j
      cases j with
      | inl j => simp [killCompl_X_image]
      | inr j => simp [killCompl_X_outside, Set.mem_range]
  exact RingHom.congr_fun h p

private theorem eval_killCompl_inr (p : MvPolynomial (Fin N ⊕ Fin N) ℝ) (x : Fin N → ℝ) :
    eval x (p.killCompl Sum.inr_injective) = eval (Sum.elim 0 x) p := by
  have h : (eval x).comp (killCompl (R := ℝ) (f := (Sum.inr : Fin N → Fin N ⊕ Fin N)) Sum.inr_injective).toRingHom =
      eval (Sum.elim 0 x) := by
    apply ringHom_ext
    · intro r
      simp
    · intro j
      cases j with
      | inl j => simp [killCompl_X_outside, Set.mem_range]
      | inr j => simp [killCompl_X_image]
  exact RingHom.congr_fun h p

private theorem correction_killCompl_inl (k : Fin N) :
    (correction G k).killCompl Sum.inl_injective = 0 := by
  apply MvPolynomial.funext
  intro x
  rw [eval_killCompl_inl, correction_eval_zero_right, map_zero]

private theorem correction_killCompl_inr (k : Fin N) :
    (correction G k).killCompl Sum.inr_injective = 0 := by
  apply MvPolynomial.funext
  intro x
  rw [eval_killCompl_inr, correction_eval_zero_left, map_zero]

/-- Each correction monomial contains a variable from each argument (BB p. 96). -/
theorem correction_mixed (k : Fin N) {d : (Fin N ⊕ Fin N) →₀ ℕ}
    (hd : (correction G k).coeff d ≠ 0) :
    (∃ j, d (Sum.inl j) ≠ 0) ∧ (∃ j, d (Sum.inr j) ≠ 0) := by
  classical
  constructor
  · by_contra h
    push Not at h
    have hs : (↑d.support : Set (Fin N ⊕ Fin N)) ⊆ Set.range Sum.inr := by
      intro i hi
      cases i with
      | inl j => exact False.elim ((Finsupp.mem_support_iff.mp hi) (h j))
      | inr j => exact ⟨j, rfl⟩
    have he := d.mapDomain_comapDomain Sum.inr Sum.inr_injective hs
    have hc := congrArg (fun p : MvPolynomial (Fin N) ℝ =>
      p.coeff (d.comapDomain Sum.inr Sum.inr_injective.injOn)) (correction_killCompl_inr G k)
    rw [coeff_killCompl, he] at hc
    exact hd hc
  · by_contra h
    push Not at h
    have hs : (↑d.support : Set (Fin N ⊕ Fin N)) ⊆ Set.range Sum.inl := by
      intro i hi
      cases i with
      | inl j => exact ⟨j, rfl⟩
      | inr j => exact False.elim ((Finsupp.mem_support_iff.mp hi) (h j))
    have he := d.mapDomain_comapDomain Sum.inl Sum.inl_injective hs
    have hc := congrArg (fun p : MvPolynomial (Fin N) ℝ =>
      p.coeff (d.comapDomain Sum.inl Sum.inl_injective.injOn)) (correction_killCompl_inl G k)
    rw [coeff_killCompl, he] at hc
    exact hd hc

private theorem weight_strict_of_other {ι : Type*} (w : ι → ℕ) (hw : ∀ i, 0 < w i)
    {d : ι →₀ ℕ} {i j : ι} (hi : d i ≠ 0) (hj : d j ≠ 0) (hij : j ≠ i) :
    w i < Finsupp.weight w d := by
  classical
  have hj' : (d - Finsupp.single i 1 : ι →₀ ℕ) j ≠ 0 := by
    simpa [Finsupp.single_eq_of_ne hij] using hj
  have hle := Finsupp.le_weight_of_ne_zero' w hj'
  have he := Finsupp.weight_sub_single_add (w := w) hi
  have hjpos := hw j
  omega

/-- Correction monomials use strictly smaller weights (BB Theorem 3.6(b), p. 96). -/
theorem correction_support_weight_lt (k : Fin N) {d : (Fin N ⊕ Fin N) →₀ ℕ}
    (hd : (correction G k).coeff d ≠ 0) {i : Fin N ⊕ Fin N} (hi : d i ≠ 0) :
    Sum.elim G.weight G.weight i < G.weight k := by
  have he := correction_weightedHomogeneous G k hd
  rw [← he]
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := correction_mixed G k hd
  cases i with
  | inl i => exact weight_strict_of_other _ (Sum.rec G.weight_pos G.weight_pos) hi hb (by simp)
  | inr i => exact weight_strict_of_other _ (Sum.rec G.weight_pos G.weight_pos) hi ha (by simp)

/-- All variables in a correction precede its coordinate (BB Theorem 3.6(b), p. 96). -/
theorem correction_vars_lt (k : Fin N) {i : Fin N ⊕ Fin N}
    (hi : i ∈ (correction G k).vars) : Sum.elim id id i < k := by
  obtain ⟨d, hd, hi⟩ := (mem_vars_iff_mem_support i).mp hi
  have hw := correction_support_weight_lt G k (mem_support_iff.mp hd) (Finsupp.mem_support_iff.mp hi)
  cases i <;> apply lt_of_not_ge <;> intro h <;> exact (not_le_of_gt hw) (G.weight_mono h)

/-- The correction depends only on earlier coordinates (BB Theorem 3.6(b), p. 96). -/
theorem correction_eval_congr (k : Fin N) {x y x' y' : Fin N → ℝ}
    (hx : ∀ j, j < k → x j = x' j) (hy : ∀ j, j < k → y j = y' j) :
    eval (Sum.elim x y) (correction G k) = eval (Sum.elim x' y') (correction G k) := by
  apply eval₂Hom_congr' rfl _ rfl
  intro i hi hi'
  have h := correction_vars_lt G k hi
  cases i with
  | inl j => exact hx j h
  | inr j => exact hy j h

/-- Polynomial partials of the correction vanish on and above the diagonal
(BB Theorem 3.6(c), pp. 96–98). -/
theorem correction_pderiv_zero (k : Fin N) (i : Fin N ⊕ Fin N)
    (hi : k ≤ Sum.elim id id i) : pderiv i (correction G k) = 0 := by
  apply pderiv_eq_zero_of_notMem_vars
  intro h
  exact (not_lt_of_ge hi) (correction_vars_lt G k h)

/-- The correction has no linear terms (BB Theorem 3.6(b), p. 96). -/
theorem correction_coeff_single (k : Fin N) (i : Fin N ⊕ Fin N) :
    (correction G k).coeff (Finsupp.single i 1) = 0 := by
  classical
  by_contra h
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := correction_mixed G k h
  cases i with
  | inl i => simp at hb
  | inr i => simp at ha

/-- Every correction partial vanishes at the origin
(BB Theorem 3.6(b), p. 96). -/
theorem correction_pderiv_eval_zero (k : Fin N) (i : Fin N ⊕ Fin N) :
    eval 0 (pderiv i (correction G k)) = 0 := by
  rw [eval_zero]
  change (pderiv i (correction G k)).coeff 0 = 0
  rw [coeff_pderiv]
  simp [correction_coeff_single]

/-- The polynomial identity underlying the Jacobian computation
(BB (3.5), p. 96). -/
theorem product_eq_add_correction (k : Fin N) :
    G.productPolynomial k = X (Sum.inl k) + X (Sum.inr k) + correction G k := by
  simp only [correction]
  ring

/-- Polynomial right partials on and above the diagonal are Kronecker entries
(BB Theorem 3.6(c), pp. 96–98). -/
theorem product_pderiv_inr (k j : Fin N) (hj : k ≤ j) :
    pderiv (Sum.inr j) (G.productPolynomial k) = if j = k then 1 else 0 := by
  classical
  rw [product_eq_add_correction]
  simp [pderiv_X, Pi.single_apply, correction_pderiv_zero G k (Sum.inr j) hj, eq_comm]

end RothschildStein.G2
