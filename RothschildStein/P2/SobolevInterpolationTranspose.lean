-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.SobolevInterpolationJets
public import RothschildStein.P1.AdjointExpansion
public import RothschildStein.S.ClassicalWords

/-!
# Sobolev interpolation, far part: integrating `L̃` off the test function (finite regularity)

The far part of the representation integrates `L̃ = ∑ᵢ X̃ᵢ² + X̃₀` off the test function `v`
against the kernel `κ = k(ξ, ·) ψ_ε(ξ, ·)` (integration by parts, BB (2.3), p. 68), where `κ` is only `C²` (the regular
remainder of a type decomposition has finite budget). Here:

* `integral_mul_fieldDerivative_test`: `∫ κ X g = ∫ (Xᵀ κ) g` for `κ ∈ C¹(Ω)` and a test `g`;
* `integral_mul_sumSquaresWithDrift`: `∫ κ L̃ g = ∫ (L̃ᵀ κ) g` for `κ ∈ C²(Ω)`;
* `sumSquaresWithDriftTranspose_apply_of_contDiffAt`: the formal adjoint formula for a function that is
  `C²` at the point;
* `abs_sumSquaresWithDriftTranspose_mul_le`: the pointwise bound of `L̃ᵀ(f g)` by the jets of the
  two factors (the six contributions of BB p. 581 for `f = k`, `g = ψ_ε`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology
namespace RothschildStein.P2

open RothschildStein.P1 RothschildStein

variable {n : ℕ}

/-- The transpose of a `C^{r+1}` function along a smooth field is `C^r`. -/
theorem contDiffOn_fieldTranspose_succ (Ω : Opens (Fin n → ℝ)) (V : (Fin n → ℝ) → (Fin n → ℝ))
    (f : (Fin n → ℝ) → ℝ) (r : ℕ)
    (hV : ContDiffOn ℝ (⊤ : ℕ∞) V (Ω : Set (Fin n → ℝ)))
    (hf : ContDiffOn ℝ ((r + 1 : ℕ) : WithTop ℕ∞) f (Ω : Set (Fin n → ℝ))) :
    ContDiffOn ℝ (r : WithTop ℕ∞) (fieldTranspose V f) (Ω : Set (Fin n → ℝ)) := by
  have hV' : ContDiffOn ℝ ((r + 1 : ℕ) : WithTop ℕ∞) V (Ω : Set (Fin n → ℝ)) :=
    hV.of_le (by exact_mod_cast le_top)
  have hd : ContDiffOn ℝ (r : WithTop ℕ∞) (fun x => fderiv ℝ (fun y => f y • V y) x)
      (Ω : Set (Fin n → ℝ)) :=
    (hf.smul hV').fderiv_of_isOpen Ω.isOpen (by norm_cast)
  unfold fieldTranspose Hormander.Interface.euclideanDivergence
  apply ContDiffOn.neg
  apply ContDiffOn.sum
  intro i _
  exact (contDiff_apply ℝ ℝ i).comp_contDiffOn (hd.clm_apply contDiffOn_const)

/-- **Integration by parts against a test** for a `C¹` function: `∫_Ω κ · X g = ∫_Ω (Xᵀκ) g`
(`Xᵀ κ = -X κ - κ div X`; the test `g` is differentiated, the `C¹` function is not). -/
theorem integral_mul_fieldDerivative_test (Ω : Opens (Fin n → ℝ)) (V : (Fin n → ℝ) → (Fin n → ℝ))
    (hV : ContDiffOn ℝ (⊤ : ℕ∞) V (Ω : Set (Fin n → ℝ))) (κ : (Fin n → ℝ) → ℝ)
    (hκ : ContDiffOn ℝ 1 κ (Ω : Set (Fin n → ℝ))) (g : TestFunction Ω ℝ (⊤ : ℕ∞)) :
    (∫ x in (Ω : Set (Fin n → ℝ)), κ x * fieldDerivative V g x) =
      ∫ x in (Ω : Set (Fin n → ℝ)), fieldTranspose V κ x * g x := by
  have hdV : ∀ y ∈ (Ω : Set (Fin n → ℝ)), DifferentiableAt ℝ V y := fun y hy =>
    (hV.contDiffAt (Ω.isOpen.mem_nhds hy)).differentiableAt (by simp)
  have hdκ : ∀ y ∈ (Ω : Set (Fin n → ℝ)), DifferentiableAt ℝ κ y := fun y hy =>
    (hκ.contDiffAt (Ω.isOpen.mem_nhds hy)).differentiableAt (by norm_num)
  have hdg : ∀ y, DifferentiableAt ℝ (g : (Fin n → ℝ) → ℝ) y := fun y =>
    g.contDiff.differentiable (by simp) y
  have hdiv : ContinuousOn (Hormander.Interface.euclideanDivergence V) (Ω : Set (Fin n → ℝ)) :=
    (contDiffOn_euclideanDivergence Ω V hV).continuousOn
  have hXκ : ContinuousOn (fieldDerivative V κ) (Ω : Set (Fin n → ℝ)) :=
    (hκ.continuousOn_fderiv_of_isOpen Ω.isOpen le_rfl).clm_apply hV.continuousOn
  have hli : ∀ f : (Fin n → ℝ) → ℝ, ContinuousOn f (Ω : Set (Fin n → ℝ)) →
      LocallyIntegrableOn f (Ω : Set (Fin n → ℝ)) volume := fun f hf =>
    hf.locallyIntegrableOn Ω.isOpen.measurableSet
  have i1 : IntegrableOn (fun x => κ x * fieldTranspose V g x) (Ω : Set (Fin n → ℝ)) volume := by
    have h := S.integrable_mul_test Ω (hli κ hκ.continuousOn) (fieldTransposeTest Ω V hV g)
    simp only [S.fieldTransposeTest_coe] at h
    exact h.integrableOn
  have i2 : IntegrableOn (fun x => κ x * Hormander.Interface.euclideanDivergence V x * g x)
      (Ω : Set (Fin n → ℝ)) volume :=
    (S.integrable_mul_test Ω (hli _ (hκ.continuousOn.mul hdiv)) g).integrableOn
  have i3 : IntegrableOn (fun x => fieldDerivative V κ x * g x) (Ω : Set (Fin n → ℝ)) volume :=
    (S.integrable_mul_test Ω (hli _ hXκ) g).integrableOn
  have h1 := S.integral_fieldDerivative_mul_test Ω V hV κ hκ g
  have e1 : ∀ x ∈ (Ω : Set (Fin n → ℝ)), κ x * fieldDerivative V g x =
      -(κ x * fieldTranspose V g x + κ x * Hormander.Interface.euclideanDivergence V x * g x) := by
    intro x hx
    have h := S.fieldTranspose_formula V g x (hdV x hx) (hdg x)
    have h' : fieldDerivative V g x = -fieldTranspose V g x -
        g x * Hormander.Interface.euclideanDivergence V x := by linarith
    rw [h']
    ring
  have e2 : ∀ x ∈ (Ω : Set (Fin n → ℝ)), fieldTranspose V κ x * g x =
      -(fieldDerivative V κ x * g x + κ x * Hormander.Interface.euclideanDivergence V x * g x) := by
    intro x hx
    rw [S.fieldTranspose_formula V κ x (hdV x hx) (hdκ x hx)]
    ring
  rw [setIntegral_congr_fun Ω.isOpen.measurableSet e1,
    setIntegral_congr_fun Ω.isOpen.measurableSet e2, integral_neg, integral_neg,
    integral_add i1 i2, integral_add i3 i2, h1]

/-- **Integration by parts of `L̃` against the test** for a `C²` function `κ` on `Ω`:
`∫_Ω κ · L̃ g = ∫_Ω (L̃ᵀ κ) g` (`sumSquaresWithDrift` and `sumSquaresWithDriftTranspose`;
each `X̃ᵢ` is moved onto `κ` by `integral_mul_fieldDerivative_test`). -/
theorem integral_mul_sumSquaresWithDrift {q : ℕ} (Ω : Opens (Fin n → ℝ))
    (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ))) (κ : (Fin n → ℝ) → ℝ)
    (hκ : ContDiffOn ℝ 2 κ (Ω : Set (Fin n → ℝ))) (g : TestFunction Ω ℝ (⊤ : ℕ∞)) :
    (∫ x in (Ω : Set (Fin n → ℝ)), κ x * sumSquaresWithDrift X g x) =
      ∫ x in (Ω : Set (Fin n → ℝ)), sumSquaresWithDriftTranspose X κ x * g x := by
  have hκ1 : ContDiffOn ℝ 1 κ (Ω : Set (Fin n → ℝ)) := hκ.of_le (by norm_num)
  have hκ2 : ContDiffOn ℝ ((1 + 1 : ℕ) : WithTop ℕ∞) κ (Ω : Set (Fin n → ℝ)) := by
    exact_mod_cast hκ
  have hT1 : ∀ i, ContDiffOn ℝ 1 (fieldTranspose (X i) κ) (Ω : Set (Fin n → ℝ)) := fun i => by
    have := contDiffOn_fieldTranspose_succ Ω (X i) κ 1 (hX i) hκ2
    exact_mod_cast this
  have hT1' : ∀ i, ContDiffOn ℝ ((0 + 1 : ℕ) : WithTop ℕ∞) (fieldTranspose (X i) κ)
      (Ω : Set (Fin n → ℝ)) := fun i => by exact_mod_cast hT1 i
  have hT0 : ∀ i, ContinuousOn (fieldTranspose (X i) κ) (Ω : Set (Fin n → ℝ)) := fun i =>
    (hT1 i).continuousOn
  have hTT : ∀ i, ContinuousOn (fieldTranspose (X i) (fieldTranspose (X i) κ))
      (Ω : Set (Fin n → ℝ)) := fun i => by
    have := contDiffOn_fieldTranspose_succ Ω (X i) (fieldTranspose (X i) κ) 0 (hX i) (hT1' i)
    exact this.continuousOn
  have hli : ∀ f : (Fin n → ℝ) → ℝ, ContinuousOn f (Ω : Set (Fin n → ℝ)) →
      LocallyIntegrableOn f (Ω : Set (Fin n → ℝ)) volume := fun f hf =>
    hf.locallyIntegrableOn Ω.isOpen.measurableSet
  -- the tests `X g` and `X X g`
  let g1 : Fin (q + 1) → TestFunction Ω ℝ (⊤ : ℕ∞) := fun i => S.wordDerivativeTest Ω X hX [i] g
  have hg1 : ∀ i, (g1 i : (Fin n → ℝ) → ℝ) = fieldDerivative (X i) g := fun i => rfl
  let g2 : Fin q → TestFunction Ω ℝ (⊤ : ℕ∞) := fun i =>
    S.wordDerivativeTest Ω X hX [i.succ, i.succ] g
  have hg2 : ∀ i : Fin q, (g2 i : (Fin n → ℝ) → ℝ) =
      fieldDerivative (X i.succ) (fieldDerivative (X i.succ) g) := fun i => rfl
  have lhs0 : IntegrableOn (fun x => κ x * fieldDerivative (X 0) g x) (Ω : Set (Fin n → ℝ))
      volume := by
    have := S.integrable_mul_test Ω (hli κ hκ.continuousOn) (g1 0)
    simp only [hg1] at this
    exact this.integrableOn
  have lhs1 : ∀ i : Fin q, IntegrableOn
      (fun x => κ x * fieldDerivative (X i.succ) (fieldDerivative (X i.succ) g) x)
      (Ω : Set (Fin n → ℝ)) volume := fun i => by
    have := S.integrable_mul_test Ω (hli κ hκ.continuousOn) (g2 i)
    simp only [hg2] at this
    exact this.integrableOn
  have rhs0 : IntegrableOn (fun x => fieldTranspose (X 0) κ x * g x) (Ω : Set (Fin n → ℝ))
      volume := (S.integrable_mul_test Ω (hli _ (hT0 0)) g).integrableOn
  have rhs1 : ∀ i : Fin q, IntegrableOn
      (fun x => fieldTranspose (X i.succ) (fieldTranspose (X i.succ) κ) x * g x)
      (Ω : Set (Fin n → ℝ)) volume := fun i =>
    (S.integrable_mul_test Ω (hli _ (hTT i.succ)) g).integrableOn
  have e1 : ∀ x, κ x * sumSquaresWithDrift X g x = κ x * fieldDerivative (X 0) g x +
      ∑ i : Fin q, κ x * fieldDerivative (X i.succ) (fieldDerivative (X i.succ) g) x := by
    intro x
    simp only [sumSquaresWithDrift, mul_add, Finset.mul_sum]
  have e2 : ∀ x, sumSquaresWithDriftTranspose X κ x * g x =
      fieldTranspose (X 0) κ x * g x + ∑ i : Fin q,
        fieldTranspose (X i.succ) (fieldTranspose (X i.succ) κ) x * g x := by
    intro x
    simp only [sumSquaresWithDriftTranspose, add_mul, Finset.sum_mul]
  simp_rw [e1, e2]
  rw [integral_add lhs0 (integrable_finsetSum _ (fun i _ => lhs1 i)),
    integral_add rhs0 (integrable_finsetSum _ (fun i _ => rhs1 i)),
    integral_finsetSum _ (fun i _ => lhs1 i), integral_finsetSum _ (fun i _ => rhs1 i),
    integral_mul_fieldDerivative_test Ω (X 0) (hX 0) κ hκ1 g]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have h1 := integral_mul_fieldDerivative_test Ω (X i.succ) (hX i.succ) κ hκ1 (g1 i.succ)
  rw [hg1] at h1
  have h2 := integral_mul_fieldDerivative_test Ω (X i.succ) (hX i.succ)
    (fieldTranspose (X i.succ) κ) (hT1 i.succ) g
  rw [h1, h2]

/-- **The square of a field transpose at a point**, for a function that is `C²` at the point
(`(X*)²φ = X²φ + 2 d Xφ + (X d + d²) φ`, `d = div X`; the `C^∞` version is
`RothschildStein.P1.fieldTranspose_fieldTranspose_apply`). -/
theorem fieldTranspose_fieldTranspose_apply_of_contDiffAt (Ω : Opens (Fin n → ℝ))
    (V : (Fin n → ℝ) → (Fin n → ℝ)) (hV : ContDiffOn ℝ (⊤ : ℕ∞) V (Ω : Set (Fin n → ℝ)))
    (φ : (Fin n → ℝ) → ℝ) {x : Fin n → ℝ} (hx : x ∈ (Ω : Set (Fin n → ℝ)))
    (hφ : ContDiffAt ℝ 2 φ x) :
    fieldTranspose V (fieldTranspose V φ) x =
      fieldDerivative V (fieldDerivative V φ) x +
        2 * (Hormander.Interface.euclideanDivergence V x * fieldDerivative V φ x) +
        (fieldDerivative V (Hormander.Interface.euclideanDivergence V) x +
          Hormander.Interface.euclideanDivergence V x ^ 2) * φ x := by
  have hdV : ∀ y ∈ (Ω : Set (Fin n → ℝ)), DifferentiableAt ℝ V y := fun y hy =>
    (hV.contDiffAt (Ω.isOpen.mem_nhds hy)).differentiableAt (by simp)
  have hVc : ContDiffAt ℝ 1 V x :=
    (hV.contDiffAt (Ω.isOpen.mem_nhds hx)).of_le (by simp)
  have hdiv : ContDiffAt ℝ 1 (Hormander.Interface.euclideanDivergence V) x :=
    ((contDiffOn_euclideanDivergence Ω V hV).contDiffAt (Ω.isOpen.mem_nhds hx)).of_le (by simp)
  have hdφ : DifferentiableAt ℝ φ x := hφ.differentiableAt (by norm_num)
  have hd1 : DifferentiableAt ℝ (Hormander.Interface.euclideanDivergence V) x :=
    hdiv.differentiableAt (by norm_num)
  have hd2 : DifferentiableAt ℝ (fieldDerivative V φ) x :=
    (contDiffAt_fieldDerivative hφ hVc).differentiableAt (by norm_num)
  have heq : fieldTranspose V φ =ᶠ[𝓝 x]
      fun y => -fieldDerivative V φ y - φ y * Hormander.Interface.euclideanDivergence V y := by
    filter_upwards [Ω.isOpen.mem_nhds hx, hφ.eventually (by simp)] with y hy hφy
    exact S.fieldTranspose_formula V φ y (hdV y hy) (hφy.differentiableAt (by norm_num))
  have hd3 : DifferentiableAt ℝ (fieldTranspose V φ) x :=
    DifferentiableAt.congr_of_eventuallyEq (hd2.fun_neg.fun_sub (hdφ.fun_mul hd1)) heq
  have hfd : fieldDerivative V (fieldTranspose V φ) x =
      -fieldDerivative V (fieldDerivative V φ) x -
        (fieldDerivative V φ x * Hormander.Interface.euclideanDivergence V x +
          φ x * fieldDerivative V (Hormander.Interface.euclideanDivergence V) x) := by
    have h1 : fderiv ℝ (fieldTranspose V φ) x = fderiv ℝ
        (fun y => -fieldDerivative V φ y - φ y * Hormander.Interface.euclideanDivergence V y) x :=
      heq.fderiv_eq
    have h2 : fderiv ℝ
        (fun y => -fieldDerivative V φ y - φ y * Hormander.Interface.euclideanDivergence V y) x =
        -fderiv ℝ (fieldDerivative V φ) x -
          (φ x • fderiv ℝ (Hormander.Interface.euclideanDivergence V) x +
            Hormander.Interface.euclideanDivergence V x • fderiv ℝ φ x) :=
      ((hd2.hasFDerivAt.neg).sub (hdφ.hasFDerivAt.mul hd1.hasFDerivAt)).fderiv
    show fderiv ℝ (fieldTranspose V φ) x (V x) = _
    rw [h1, h2]
    simp only [sub_apply, neg_apply, add_apply, smul_apply, smul_eq_mul, fieldDerivative]
    ring
  rw [S.fieldTranspose_formula V _ x (hdV x hx) hd3, hfd,
    S.fieldTranspose_formula V φ x (hdV x hx) hdφ]
  ring

/-- **The formal adjoint formula at a point** for a function that is `C²` at the point: the transpose of `L̃ = ∑ᵢ X̃ᵢ² + X̃₀` is `∑ᵢ X̃ᵢ²φ − X̃₀φ + 2 ∑ᵢ dᵢ X̃ᵢφ + ∑ᵢ (X̃ᵢ dᵢ + dᵢ²) φ − d₀ φ`. -/
theorem sumSquaresWithDriftTranspose_apply_of_contDiffAt {q : ℕ} (Ω : Opens (Fin n → ℝ))
    (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (φ : (Fin n → ℝ) → ℝ) {x : Fin n → ℝ} (hx : x ∈ (Ω : Set (Fin n → ℝ)))
    (hφ : ContDiffAt ℝ 2 φ x) :
    sumSquaresWithDriftTranspose X φ x =
      (∑ i : Fin q, fieldDerivative (X i.succ) (fieldDerivative (X i.succ) φ) x -
          fieldDerivative (X 0) φ x) +
        2 * ∑ i : Fin q, Hormander.Interface.euclideanDivergence (X i.succ) x *
          fieldDerivative (X i.succ) φ x +
        ∑ i : Fin q, (fieldDerivative (X i.succ)
            (Hormander.Interface.euclideanDivergence (X i.succ)) x +
          Hormander.Interface.euclideanDivergence (X i.succ) x ^ 2) * φ x -
        Hormander.Interface.euclideanDivergence (X 0) x * φ x := by
  have hdV : DifferentiableAt ℝ (X 0) x :=
    ((hX 0).contDiffAt (Ω.isOpen.mem_nhds hx)).differentiableAt (by simp)
  have hdφ : DifferentiableAt ℝ φ x := hφ.differentiableAt (by norm_num)
  have h0 := S.fieldTranspose_formula (X 0) φ x hdV hdφ
  have hsq : ∀ i : Fin q, fieldTranspose (X i.succ) (fieldTranspose (X i.succ) φ) x =
      fieldDerivative (X i.succ) (fieldDerivative (X i.succ) φ) x +
        2 * (Hormander.Interface.euclideanDivergence (X i.succ) x *
          fieldDerivative (X i.succ) φ x) +
        (fieldDerivative (X i.succ) (Hormander.Interface.euclideanDivergence (X i.succ)) x +
          Hormander.Interface.euclideanDivergence (X i.succ) x ^ 2) * φ x :=
    fun i => fieldTranspose_fieldTranspose_apply_of_contDiffAt Ω (X i.succ) (hX i.succ) φ hx hφ
  simp only [sumSquaresWithDriftTranspose, h0, hsq, Finset.sum_add_distrib, Finset.mul_sum]
  ring

/-- The product rule for two iterated field derivatives along the same field, for `C²`
functions. -/
theorem fieldDerivative_fieldDerivative_mul {V : (Fin n → ℝ) → (Fin n → ℝ)}
    {f g : (Fin n → ℝ) → ℝ} {x : Fin n → ℝ} (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x)
    (hV : ContDiffAt ℝ 1 V x) :
    fieldDerivative V (fieldDerivative V (fun y => f y * g y)) x =
      fieldDerivative V (fieldDerivative V f) x * g x +
        2 * (fieldDerivative V f x * fieldDerivative V g x) +
        f x * fieldDerivative V (fieldDerivative V g) x := by
  have hev : fieldDerivative V (fun y => f y * g y) =ᶠ[𝓝 x]
      fun y => fieldDerivative V f y * g y + f y * fieldDerivative V g y := by
    filter_upwards [hf.eventually (by simp), hg.eventually (by simp)] with y hfy hgy
    exact S.fieldDerivative_mul V f g y (hfy.differentiableAt (by norm_num))
      (hgy.differentiableAt (by norm_num))
  rw [fieldDerivative_congr_eventually hev]
  have hfd : DifferentiableAt ℝ f x := hf.differentiableAt (by norm_num)
  have hgd : DifferentiableAt ℝ g x := hg.differentiableAt (by norm_num)
  have h1 : DifferentiableAt ℝ (fieldDerivative V f) x :=
    (contDiffAt_fieldDerivative hf hV).differentiableAt (by norm_num)
  have h2 : DifferentiableAt ℝ (fieldDerivative V g) x :=
    (contDiffAt_fieldDerivative hg hV).differentiableAt (by norm_num)
  rw [fieldDerivative_add_of_differentiableAt (h1.fun_mul hgd) (hfd.fun_mul h2),
    S.fieldDerivative_mul V (fieldDerivative V f) g x h1 hgd,
    S.fieldDerivative_mul V f (fieldDerivative V g) x hfd h2]
  ring

/-- Triangle inequality for the five groups of terms of the formal adjoint formula. -/
theorem abs_five_le (a b c d e : ℝ) :
    |a - b + 2 * c + d - e| ≤ |a| + |b| + 2 * |c| + |d| + |e| := by
  rw [abs_le]
  constructor <;> linarith [le_abs_self a, neg_abs_le a, le_abs_self b, neg_abs_le b,
    le_abs_self c, neg_abs_le c, le_abs_self d, neg_abs_le d, le_abs_self e, neg_abs_le e]

/-- **The pointwise bound of `L̃ᵀ(f g)`** (the six contributions of BB p. 581): let `f`
(the kernel) and `g` (the cutoff) be `C²` at `x ∈ Ω`, `0 < d ≤ D₀`, and suppose
`|f| ≤ M d² u`, `|X̃ᵢ f| ≤ M d u`, `|X̃ᵢ² f|, |X̃₀ f| ≤ M u` and `|g| ≤ 1`, `d |X̃ᵢ g| ≤ B₁`,
`d² |X̃ᵢ² g|, d² |X̃₀ g| ≤ B₂`, with the divergence coefficients of `L̃ᵀ` bounded by `Cd`. Then
`|L̃ᵀ(f g)(x)| ≤ K u` with `K` depending on `M, B₁, B₂, Cd, D₀, q` only. -/
theorem abs_sumSquaresWithDriftTranspose_mul_le {q : ℕ} (Ω : Opens (Fin n → ℝ))
    (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    {x : Fin n → ℝ} (hx : x ∈ (Ω : Set (Fin n → ℝ))) {f g : (Fin n → ℝ) → ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x)
    {Cd M B₁ B₂ u d D₀ : ℝ}
    (hd : ∀ i : Fin q, |Hormander.Interface.euclideanDivergence (X i.succ) x| ≤ Cd)
    (hd0 : |Hormander.Interface.euclideanDivergence (X 0) x| ≤ Cd)
    (he : ∀ i : Fin q, |fieldDerivative (X i.succ)
      (Hormander.Interface.euclideanDivergence (X i.succ)) x +
        Hormander.Interface.euclideanDivergence (X i.succ) x ^ 2| ≤ Cd)
    (hCd : 0 ≤ Cd) (hM : 0 ≤ M) (hB₁ : 0 ≤ B₁) (hu : 0 ≤ u) (hdpos : 0 < d)
    (hdD : d ≤ D₀)
    (hf0 : |f x| ≤ M * d ^ 2 * u)
    (hf1 : ∀ i : Fin q, |fieldDerivative (X i.succ) f x| ≤ M * d * u)
    (hf2 : ∀ i : Fin q, |fieldDerivative (X i.succ) (fieldDerivative (X i.succ) f) x| ≤ M * u)
    (hfd : |fieldDerivative (X 0) f x| ≤ M * u)
    (hg0 : |g x| ≤ 1)
    (hg1 : ∀ i : Fin q, |fieldDerivative (X i.succ) g x| * d ≤ B₁)
    (hg2 : ∀ i : Fin q, |fieldDerivative (X i.succ) (fieldDerivative (X i.succ) g) x| * d ^ 2 ≤ B₂)
    (hgd : |fieldDerivative (X 0) g x| * d ^ 2 ≤ B₂) :
    |sumSquaresWithDriftTranspose X (fun y => f y * g y) x| ≤
      M * (q * (1 + 2 * B₁ + B₂) + (1 + B₂) + 2 * q * Cd * D₀ * (1 + B₁) +
        (q + 1) * Cd * D₀ ^ 2) * u := by
  have hfg : ContDiffAt ℝ 2 (fun y => f y * g y) x := hf.mul hg
  have hXc : ∀ i, ContDiffAt ℝ 1 (X i) x := fun i =>
    ((hX i).contDiffAt (Ω.isOpen.mem_nhds hx)).of_le (by simp)
  have hfdx : DifferentiableAt ℝ f x := hf.differentiableAt (by norm_num)
  have hgdx : DifferentiableAt ℝ g x := hg.differentiableAt (by norm_num)
  have hd0' : 0 ≤ d := hdpos.le
  have hdd : d ^ 2 ≤ D₀ ^ 2 := pow_le_pow_left₀ hd0' hdD 2
  have habs : |g x| ≤ 1 := hg0
  -- sizes of the jets of the product
  have hφ0 : |f x * g x| ≤ M * d ^ 2 * u := by
    rw [abs_mul]
    calc |f x| * |g x| ≤ (M * d ^ 2 * u) * 1 :=
          mul_le_mul hf0 habs (abs_nonneg _) (by positivity)
      _ = M * d ^ 2 * u := by ring
  have hφ1 : ∀ i : Fin q, |fieldDerivative (X i.succ) (fun y => f y * g y) x| ≤
      M * u * (d + d * B₁) := by
    intro i
    rw [S.fieldDerivative_mul (X i.succ) f g x hfdx hgdx]
    have h1 : |fieldDerivative (X i.succ) f x * g x| ≤ M * d * u := by
      rw [abs_mul]
      calc |fieldDerivative (X i.succ) f x| * |g x| ≤ (M * d * u) * 1 :=
            mul_le_mul (hf1 i) habs (abs_nonneg _) (by positivity)
        _ = M * d * u := by ring
    have h2 : |f x * fieldDerivative (X i.succ) g x| ≤ M * u * (d * B₁) := by
      rw [abs_mul]
      have hg1' : |fieldDerivative (X i.succ) g x| * d ≤ B₁ := hg1 i
      calc |f x| * |fieldDerivative (X i.succ) g x| ≤
            (M * d ^ 2 * u) * |fieldDerivative (X i.succ) g x| :=
            mul_le_mul_of_nonneg_right hf0 (abs_nonneg _)
        _ = M * u * d * (|fieldDerivative (X i.succ) g x| * d) := by ring
        _ ≤ M * u * d * B₁ := mul_le_mul_of_nonneg_left hg1' (by positivity)
        _ = M * u * (d * B₁) := by ring
    calc _ ≤ |fieldDerivative (X i.succ) f x * g x| + |f x * fieldDerivative (X i.succ) g x| :=
          abs_add_le _ _
      _ ≤ M * d * u + M * u * (d * B₁) := add_le_add h1 h2
      _ = M * u * (d + d * B₁) := by ring
  have hφ2 : ∀ i : Fin q, |fieldDerivative (X i.succ) (fieldDerivative (X i.succ)
      (fun y => f y * g y)) x| ≤ M * u * (1 + 2 * B₁ + B₂) := by
    intro i
    rw [fieldDerivative_fieldDerivative_mul hf hg (hXc i.succ)]
    have h1 : |fieldDerivative (X i.succ) (fieldDerivative (X i.succ) f) x * g x| ≤ M * u := by
      rw [abs_mul]
      calc _ ≤ (M * u) * 1 := mul_le_mul (hf2 i) habs (abs_nonneg _) (by positivity)
        _ = M * u := by ring
    have h2 : |2 * (fieldDerivative (X i.succ) f x * fieldDerivative (X i.succ) g x)| ≤
        2 * (M * u * B₁) := by
      rw [abs_mul, abs_mul, abs_two]
      have hg1' : |fieldDerivative (X i.succ) g x| * d ≤ B₁ := hg1 i
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      calc |fieldDerivative (X i.succ) f x| * |fieldDerivative (X i.succ) g x| ≤
            (M * d * u) * |fieldDerivative (X i.succ) g x| :=
            mul_le_mul_of_nonneg_right (hf1 i) (abs_nonneg _)
        _ = M * u * (|fieldDerivative (X i.succ) g x| * d) := by ring
        _ ≤ M * u * B₁ := mul_le_mul_of_nonneg_left hg1' (by positivity)
    have h3 : |f x * fieldDerivative (X i.succ) (fieldDerivative (X i.succ) g) x| ≤
        M * u * B₂ := by
      rw [abs_mul]
      have hg2' := hg2 i
      calc |f x| * |fieldDerivative (X i.succ) (fieldDerivative (X i.succ) g) x| ≤
            (M * d ^ 2 * u) * |fieldDerivative (X i.succ) (fieldDerivative (X i.succ) g) x| :=
            mul_le_mul_of_nonneg_right hf0 (abs_nonneg _)
        _ = M * u * (|fieldDerivative (X i.succ) (fieldDerivative (X i.succ) g) x| * d ^ 2) := by
            ring
        _ ≤ M * u * B₂ := mul_le_mul_of_nonneg_left hg2' (by positivity)
    calc _ ≤ |fieldDerivative (X i.succ) (fieldDerivative (X i.succ) f) x * g x| +
          |2 * (fieldDerivative (X i.succ) f x * fieldDerivative (X i.succ) g x)| +
          |f x * fieldDerivative (X i.succ) (fieldDerivative (X i.succ) g) x| := abs_add_three _ _ _
      _ ≤ M * u + 2 * (M * u * B₁) + M * u * B₂ := add_le_add (add_le_add h1 h2) h3
      _ = M * u * (1 + 2 * B₁ + B₂) := by ring
  have hφd : |fieldDerivative (X 0) (fun y => f y * g y) x| ≤ M * u * (1 + B₂) := by
    rw [S.fieldDerivative_mul (X 0) f g x hfdx hgdx]
    have h1 : |fieldDerivative (X 0) f x * g x| ≤ M * u := by
      rw [abs_mul]
      calc _ ≤ (M * u) * 1 := mul_le_mul hfd habs (abs_nonneg _) (by positivity)
        _ = M * u := by ring
    have h2 : |f x * fieldDerivative (X 0) g x| ≤ M * u * B₂ := by
      rw [abs_mul]
      calc |f x| * |fieldDerivative (X 0) g x| ≤
            (M * d ^ 2 * u) * |fieldDerivative (X 0) g x| :=
            mul_le_mul_of_nonneg_right hf0 (abs_nonneg _)
        _ = M * u * (|fieldDerivative (X 0) g x| * d ^ 2) := by ring
        _ ≤ M * u * B₂ := mul_le_mul_of_nonneg_left hgd (by positivity)
    calc _ ≤ |fieldDerivative (X 0) f x * g x| + |f x * fieldDerivative (X 0) g x| :=
          abs_add_le _ _
      _ ≤ M * u + M * u * B₂ := add_le_add h1 h2
      _ = M * u * (1 + B₂) := by ring
  -- the four sums
  have hS1 : |∑ i : Fin q, fieldDerivative (X i.succ) (fieldDerivative (X i.succ)
      (fun y => f y * g y)) x| ≤ q * (M * u * (1 + 2 * B₁ + B₂)) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i : Fin q, |fieldDerivative (X i.succ) (fieldDerivative (X i.succ)
          (fun y => f y * g y)) x| ≤ ∑ _i : Fin q, M * u * (1 + 2 * B₁ + B₂) :=
          Finset.sum_le_sum (fun i _ => hφ2 i)
      _ = q * (M * u * (1 + 2 * B₁ + B₂)) := by simp
  have hS3 : |∑ i : Fin q, Hormander.Interface.euclideanDivergence (X i.succ) x *
      fieldDerivative (X i.succ) (fun y => f y * g y) x| ≤
      q * (Cd * (M * u * (d + d * B₁))) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i : Fin q, |Hormander.Interface.euclideanDivergence (X i.succ) x *
          fieldDerivative (X i.succ) (fun y => f y * g y) x| ≤
          ∑ _i : Fin q, Cd * (M * u * (d + d * B₁)) :=
          Finset.sum_le_sum (fun i _ => by
            rw [abs_mul]
            exact mul_le_mul (hd i) (hφ1 i) (abs_nonneg _) hCd)
      _ = q * (Cd * (M * u * (d + d * B₁))) := by simp
  have hS4 : |∑ i : Fin q, (fieldDerivative (X i.succ)
      (Hormander.Interface.euclideanDivergence (X i.succ)) x +
        Hormander.Interface.euclideanDivergence (X i.succ) x ^ 2) * (f x * g x)| ≤
      q * (Cd * (M * d ^ 2 * u)) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i : Fin q, |(fieldDerivative (X i.succ)
          (Hormander.Interface.euclideanDivergence (X i.succ)) x +
            Hormander.Interface.euclideanDivergence (X i.succ) x ^ 2) * (f x * g x)| ≤
          ∑ _i : Fin q, Cd * (M * d ^ 2 * u) :=
          Finset.sum_le_sum (fun i _ => by
            rw [abs_mul]
            exact mul_le_mul (he i) hφ0 (abs_nonneg _) hCd)
      _ = q * (Cd * (M * d ^ 2 * u)) := by simp
  have hS5 : |Hormander.Interface.euclideanDivergence (X 0) x * (f x * g x)| ≤
      Cd * (M * d ^ 2 * u) := by
    rw [abs_mul]
    exact mul_le_mul hd0 hφ0 (abs_nonneg _) hCd
  have key := sumSquaresWithDriftTranspose_apply_of_contDiffAt Ω X hX (fun y => f y * g y) hx hfg
  beta_reduce at key
  rw [key]
  refine (abs_five_le _ _ _ _ _).trans ?_
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hMu : 0 ≤ M * u := mul_nonneg hM hu
  have hdB : d + d * B₁ ≤ D₀ + D₀ * B₁ := by nlinarith
  have h4 : M * d ^ 2 * u ≤ M * D₀ ^ 2 * u :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdd hM) hu
  calc _ ≤ q * (M * u * (1 + 2 * B₁ + B₂)) + M * u * (1 + B₂) +
        2 * (q * (Cd * (M * u * (d + d * B₁)))) + q * (Cd * (M * d ^ 2 * u)) +
        Cd * (M * d ^ 2 * u) :=
        add_le_add (add_le_add (add_le_add (add_le_add hS1 hφd)
          (mul_le_mul_of_nonneg_left hS3 (by norm_num))) hS4) hS5
    _ ≤ q * (M * u * (1 + 2 * B₁ + B₂)) + M * u * (1 + B₂) +
        2 * (q * (Cd * (M * u * (D₀ + D₀ * B₁)))) + q * (Cd * (M * D₀ ^ 2 * u)) +
        Cd * (M * D₀ ^ 2 * u) := by
        have h5 : M * u * (d + d * B₁) ≤ M * u * (D₀ + D₀ * B₁) :=
          mul_le_mul_of_nonneg_left hdB hMu
        have h6 : Cd * (M * u * (d + d * B₁)) ≤ Cd * (M * u * (D₀ + D₀ * B₁)) :=
          mul_le_mul_of_nonneg_left h5 hCd
        have h7 : Cd * (M * d ^ 2 * u) ≤ Cd * (M * D₀ ^ 2 * u) :=
          mul_le_mul_of_nonneg_left h4 hCd
        have h8 : (q : ℝ) * (Cd * (M * u * (d + d * B₁))) ≤ q * (Cd * (M * u * (D₀ + D₀ * B₁))) :=
          mul_le_mul_of_nonneg_left h6 hq0
        have h9 : (q : ℝ) * (Cd * (M * d ^ 2 * u)) ≤ q * (Cd * (M * D₀ ^ 2 * u)) :=
          mul_le_mul_of_nonneg_left h7 hq0
        linarith
    _ = M * (q * (1 + 2 * B₁ + B₂) + (1 + B₂) + 2 * q * Cd * D₀ * (1 + B₁) +
        (q + 1) * Cd * D₀ ^ 2) * u := by ring

end RothschildStein.P2
