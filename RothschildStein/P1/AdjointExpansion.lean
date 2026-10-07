-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.IntegrationByParts
public import RothschildStein.S.TransposeSmooth
public import RothschildStein.Definitions.sumSquares
public import RothschildStein.Definitions.sumSquaresTranspose
public import RothschildStein.Definitions.sumSquaresWithDrift
public import RothschildStein.Definitions.sumSquaresWithDriftTranspose

/-!
# The formal adjoint of the lifted operator

For smooth fields `X̃₀, …, X̃_q` on an open set (drift letter `0`, horizontal letters `1, …, q`;
in Lean `X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ)`, horizontal letter `i.succ`) with
divergences `dᵢ = div X̃ᵢ`, the transpose `sumSquaresWithDriftTranspose` of
`L̃ = ∑ᵢ X̃ᵢ² + X̃₀` is

`L̃*φ = ∑ᵢ X̃ᵢ²φ − X̃₀φ + 2 ∑ᵢ dᵢ X̃ᵢφ + ∑ᵢ (X̃ᵢ dᵢ + dᵢ²) φ − d₀ φ`

pointwise on the open set (`sumSquaresWithDriftTranspose_apply`), and
`∫ (L̃ f) φ = ∫ f (L̃* φ)` for tests `φ` (`integral_sumSquaresWithDrift_mul_test`). The no-drift
forms (alphabet `Fin q`, `sumSquares` and `sumSquaresTranspose`) are the same statements
without the letter `0`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology
namespace RothschildStein.P1
variable {n : ℕ}

/-- The Euclidean divergence of a smooth field is smooth on the open
set (BB p. 68; the coefficient `dᵢ` of the formal adjoint `L̃*`). -/
theorem contDiffOn_euclideanDivergence (Ω : Opens (Fin n → ℝ))
    (V : (Fin n → ℝ) → (Fin n → ℝ))
    (hV : ContDiffOn ℝ (⊤ : ℕ∞) V (Ω : Set (Fin n → ℝ))) :
    ContDiffOn ℝ (⊤ : ℕ∞) (Hormander.Interface.euclideanDivergence V)
      (Ω : Set (Fin n → ℝ)) := by
  have hd : ContDiffOn ℝ (⊤ : ℕ∞) (fun x => fderiv ℝ V x) (Ω : Set (Fin n → ℝ)) :=
    hV.fderiv_of_isOpen Ω.isOpen (by simp)
  unfold Hormander.Interface.euclideanDivergence
  apply ContDiffOn.sum
  intro i _
  exact (contDiff_apply ℝ ℝ i).comp_contDiffOn (hd.clm_apply contDiffOn_const)

/-- The square of the field transpose, pointwise on an open
set: `(X*)²φ = X²φ + 2 d Xφ + (X d + d²) φ` with `d = div X` and `X* = -X - d`
(BB (2.3), p. 68; one square in the formal adjoint `L̃*`). -/
theorem fieldTranspose_fieldTranspose_apply (Ω : Opens (Fin n → ℝ))
    (V : (Fin n → ℝ) → (Fin n → ℝ))
    (hV : ContDiffOn ℝ (⊤ : ℕ∞) V (Ω : Set (Fin n → ℝ)))
    (φ : (Fin n → ℝ) → ℝ) (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ (Ω : Set (Fin n → ℝ)))
    {x : Fin n → ℝ} (hx : x ∈ (Ω : Set (Fin n → ℝ))) :
    fieldTranspose V (fieldTranspose V φ) x =
      fieldDerivative V (fieldDerivative V φ) x +
        2 * (Hormander.Interface.euclideanDivergence V x * fieldDerivative V φ x) +
        (fieldDerivative V (Hormander.Interface.euclideanDivergence V) x +
          Hormander.Interface.euclideanDivergence V x ^ 2) * φ x := by
  have hdV : ∀ y ∈ (Ω : Set (Fin n → ℝ)), DifferentiableAt ℝ V y := fun y hy =>
    (hV.contDiffAt (Ω.isOpen.mem_nhds hy)).differentiableAt (by simp)
  have hdφ : ∀ y ∈ (Ω : Set (Fin n → ℝ)), DifferentiableAt ℝ φ y := fun y hy =>
    (hφ.contDiffAt (Ω.isOpen.mem_nhds hy)).differentiableAt (by simp)
  have hdiv := contDiffOn_euclideanDivergence Ω V hV
  have hVφ := S.contDiffOn_fieldDerivative Ω V φ hV hφ
  have hT := S.contDiffOn_fieldTranspose Ω V φ hV hφ
  have hd1 : DifferentiableAt ℝ (Hormander.Interface.euclideanDivergence V) x :=
    (hdiv.contDiffAt (Ω.isOpen.mem_nhds hx)).differentiableAt (by simp)
  have hd2 : DifferentiableAt ℝ (fieldDerivative V φ) x :=
    (hVφ.contDiffAt (Ω.isOpen.mem_nhds hx)).differentiableAt (by simp)
  have hd3 : DifferentiableAt ℝ (fieldTranspose V φ) x :=
    (hT.contDiffAt (Ω.isOpen.mem_nhds hx)).differentiableAt (by simp)
  have heq : fieldTranspose V φ =ᶠ[𝓝 x]
      fun y => -fieldDerivative V φ y - φ y * Hormander.Interface.euclideanDivergence V y := by
    filter_upwards [Ω.isOpen.mem_nhds hx] with y hy
    exact S.fieldTranspose_formula V φ y (hdV y hy) (hdφ y hy)
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
      ((hd2.hasFDerivAt.neg).sub ((hdφ x hx).hasFDerivAt.mul hd1.hasFDerivAt)).fderiv
    show fderiv ℝ (fieldTranspose V φ) x (V x) = _
    rw [h1, h2]
    simp only [sub_apply, neg_apply,
      add_apply, smul_apply, smul_eq_mul, fieldDerivative]
    ring
  rw [S.fieldTranspose_formula V _ x (hdV x hx) hd3, hfd,
    S.fieldTranspose_formula V φ x (hdV x hx) (hdφ x hx)]
  ring

/-- The formal adjoint formula, pointwise on an open set: the transpose of
`L̃ = ∑ᵢ X̃ᵢ² + X̃₀` equals `∑ᵢ X̃ᵢ²φ − X̃₀φ + 2 ∑ᵢ dᵢ X̃ᵢφ + ∑ᵢ (X̃ᵢ dᵢ + dᵢ²) φ − d₀ φ`,
`dᵢ = div X̃ᵢ` (BB pp. 560–561, (11.40); BB (2.2)–(2.3), p. 68). -/
theorem sumSquaresWithDriftTranspose_apply {q : ℕ} (Ω : Opens (Fin n → ℝ))
    (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (φ : (Fin n → ℝ) → ℝ) (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ (Ω : Set (Fin n → ℝ)))
    {x : Fin n → ℝ} (hx : x ∈ (Ω : Set (Fin n → ℝ))) :
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
  have hdφ : DifferentiableAt ℝ φ x :=
    (hφ.contDiffAt (Ω.isOpen.mem_nhds hx)).differentiableAt (by simp)
  have h0 := S.fieldTranspose_formula (X 0) φ x hdV hdφ
  have hsq : ∀ i : Fin q, fieldTranspose (X i.succ) (fieldTranspose (X i.succ) φ) x =
      fieldDerivative (X i.succ) (fieldDerivative (X i.succ) φ) x +
        2 * (Hormander.Interface.euclideanDivergence (X i.succ) x *
          fieldDerivative (X i.succ) φ x) +
        (fieldDerivative (X i.succ) (Hormander.Interface.euclideanDivergence (X i.succ)) x +
          Hormander.Interface.euclideanDivergence (X i.succ) x ^ 2) * φ x :=
    fun i => fieldTranspose_fieldTranspose_apply Ω (X i.succ) (hX i.succ) φ hφ hx
  simp only [sumSquaresWithDriftTranspose, h0, hsq, Finset.sum_add_distrib, Finset.mul_sum]
  ring

/-- The no-drift form of the formal adjoint formula for `sumSquaresTranspose`
of `∑ᵢ X̃ᵢ²` over the alphabet `Fin q`: no `X̃₀` and no `d₀` term. -/
theorem sumSquaresTranspose_apply {q : ℕ} (Ω : Opens (Fin n → ℝ))
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (φ : (Fin n → ℝ) → ℝ) (hφ : ContDiffOn ℝ (⊤ : ℕ∞) φ (Ω : Set (Fin n → ℝ)))
    {x : Fin n → ℝ} (hx : x ∈ (Ω : Set (Fin n → ℝ))) :
    sumSquaresTranspose X φ x =
      ∑ i : Fin q, fieldDerivative (X i) (fieldDerivative (X i) φ) x +
        2 * ∑ i : Fin q, Hormander.Interface.euclideanDivergence (X i) x *
          fieldDerivative (X i) φ x +
        ∑ i : Fin q, (fieldDerivative (X i) (Hormander.Interface.euclideanDivergence (X i)) x +
          Hormander.Interface.euclideanDivergence (X i) x ^ 2) * φ x := by
  simp only [sumSquaresTranspose,
    fun i => fieldTranspose_fieldTranspose_apply Ω (X i) (hX i) φ hφ hx,
    Finset.sum_add_distrib, Finset.mul_sum]

/-- Integrability of `g · fieldTranspose V φ` on `Ω` for continuous
`g` on `Ω` and a test `φ`. -/
theorem integrableOn_mul_fieldTranspose (Ω : Opens (Fin n → ℝ))
    (V : (Fin n → ℝ) → (Fin n → ℝ))
    (hV : ContDiffOn ℝ (⊤ : ℕ∞) V (Ω : Set (Fin n → ℝ)))
    {g : (Fin n → ℝ) → ℝ} (hg : ContinuousOn g (Ω : Set (Fin n → ℝ)))
    (φ : TestFunction Ω ℝ (⊤ : ℕ∞)) :
    IntegrableOn (fun x => g x * fieldTranspose V φ x) (Ω : Set (Fin n → ℝ)) volume := by
  have h := S.integrable_mul_test Ω (hg.locallyIntegrableOn Ω.isOpen.measurableSet)
    (fieldTransposeTest Ω V hV φ)
  simp only [S.fieldTransposeTest_coe] at h
  exact h.integrableOn

/-- Integrability of `g · (X*)² φ` on `Ω`. -/
theorem integrableOn_mul_fieldTranspose_square (Ω : Opens (Fin n → ℝ))
    (V : (Fin n → ℝ) → (Fin n → ℝ))
    (hV : ContDiffOn ℝ (⊤ : ℕ∞) V (Ω : Set (Fin n → ℝ)))
    {g : (Fin n → ℝ) → ℝ} (hg : ContinuousOn g (Ω : Set (Fin n → ℝ)))
    (φ : TestFunction Ω ℝ (⊤ : ℕ∞)) :
    IntegrableOn (fun x => g x * fieldTranspose V (fieldTranspose V φ) x)
      (Ω : Set (Fin n → ℝ)) volume := by
  have h := S.integrable_mul_test Ω (hg.locallyIntegrableOn Ω.isOpen.measurableSet)
    (fieldTransposeTest Ω V hV (fieldTransposeTest Ω V hV φ))
  simp only [S.fieldTransposeTest_coe] at h
  exact h.integrableOn

/-- Integration by parts for the square of one smooth field on an open
set: `∫ X²f · φ = ∫ f · (X*)²φ` for `f` smooth on `Ω` and a test `φ` (BB (2.3), p. 68). -/
theorem integral_fieldDerivative_square_mul_test (Ω : Opens (Fin n → ℝ))
    (V : (Fin n → ℝ) → (Fin n → ℝ))
    (hV : ContDiffOn ℝ (⊤ : ℕ∞) V (Ω : Set (Fin n → ℝ)))
    (f : (Fin n → ℝ) → ℝ) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (Ω : Set (Fin n → ℝ)))
    (φ : TestFunction Ω ℝ (⊤ : ℕ∞)) :
    (∫ x in (Ω : Set (Fin n → ℝ)),
      fieldDerivative V (fieldDerivative V f) x * φ x) =
      ∫ x in (Ω : Set (Fin n → ℝ)), f x * fieldTranspose V (fieldTranspose V φ) x := by
  have hdf := S.contDiffOn_fieldDerivative Ω V f hV hf
  have h1 := S.integral_fieldDerivative_mul_test Ω V hV (fieldDerivative V f)
    (hdf.of_le (by norm_num)) φ
  have h2 := S.integral_fieldDerivative_mul_test Ω V hV f (hf.of_le (by norm_num))
    (fieldTransposeTest Ω V hV φ)
  simp only [S.fieldTransposeTest_coe] at h2
  rw [h1, h2]

/-- The pairing identity `∫ (L̃f) φ = ∫ f (L̃*φ)` for the lifted
operator with drift, `f` smooth on the open set `Ω` and `φ` a test function there; the
transpose is `sumSquaresWithDriftTranspose` (BB (2.1)–(2.3), p. 68). -/
theorem integral_sumSquaresWithDrift_mul_test {q : ℕ} (Ω : Opens (Fin n → ℝ))
    (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (f : (Fin n → ℝ) → ℝ) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (Ω : Set (Fin n → ℝ)))
    (φ : TestFunction Ω ℝ (⊤ : ℕ∞)) :
    (∫ x in (Ω : Set (Fin n → ℝ)), sumSquaresWithDrift X f x * φ x) =
      ∫ x in (Ω : Set (Fin n → ℝ)), f x * sumSquaresWithDriftTranspose X φ x := by
  have hi1 (i : Fin (q + 1)) : IntegrableOn (fun x => fieldDerivative (X i) f x * φ x)
      (Ω : Set (Fin n → ℝ)) volume :=
    (S.integrable_mul_test Ω (((S.contDiffOn_fieldDerivative Ω (X i) f (hX i) hf).continuousOn
      ).locallyIntegrableOn Ω.isOpen.measurableSet) φ).integrableOn
  have hi2 (i : Fin q) : IntegrableOn
      (fun x => fieldDerivative (X i.succ) (fieldDerivative (X i.succ) f) x * φ x)
      (Ω : Set (Fin n → ℝ)) volume :=
    (S.integrable_mul_test Ω (((S.contDiffOn_fieldDerivative Ω (X i.succ) _ (hX i.succ)
      (S.contDiffOn_fieldDerivative Ω (X i.succ) f (hX i.succ) hf)).continuousOn
      ).locallyIntegrableOn Ω.isOpen.measurableSet) φ).integrableOn
  have hi3 : IntegrableOn (fun x => f x * fieldTranspose (X 0) φ x)
      (Ω : Set (Fin n → ℝ)) volume :=
    integrableOn_mul_fieldTranspose Ω (X 0) (hX 0) hf.continuousOn φ
  have hi4 (i : Fin q) : IntegrableOn
      (fun x => f x * fieldTranspose (X i.succ) (fieldTranspose (X i.succ) φ) x)
      (Ω : Set (Fin n → ℝ)) volume :=
    integrableOn_mul_fieldTranspose_square Ω (X i.succ) (hX i.succ) hf.continuousOn φ
  have e1 : ∀ x, sumSquaresWithDrift X f x * φ x =
      fieldDerivative (X 0) f x * φ x + ∑ i : Fin q,
        fieldDerivative (X i.succ) (fieldDerivative (X i.succ) f) x * φ x := by
    intro x
    simp only [sumSquaresWithDrift, add_mul, Finset.sum_mul]
  have e2 : ∀ x, f x * sumSquaresWithDriftTranspose X φ x =
      f x * fieldTranspose (X 0) φ x + ∑ i : Fin q,
        f x * fieldTranspose (X i.succ) (fieldTranspose (X i.succ) φ) x := by
    intro x
    simp only [sumSquaresWithDriftTranspose, mul_add, Finset.mul_sum]
  simp_rw [e1, e2]
  rw [integral_add (hi1 0) (integrable_finsetSum _ (fun i _ => hi2 i)),
    integral_add hi3 (integrable_finsetSum _ (fun i _ => hi4 i)),
    integral_finsetSum _ (fun i _ => hi2 i), integral_finsetSum _ (fun i _ => hi4 i),
    S.integral_fieldDerivative_mul_test Ω (X 0) (hX 0) f (hf.of_le (by norm_num)) φ]
  congr 1
  exact Finset.sum_congr rfl (fun i _ =>
    integral_fieldDerivative_square_mul_test Ω (X i.succ) (hX i.succ) f hf φ)

/-- The no-drift pairing identity `∫ (∑ᵢ X̃ᵢ² f) φ = ∫ f (∑ᵢ (X̃ᵢ*)² φ)`
for `sumSquares` and `sumSquaresTranspose`. -/
theorem integral_sumSquares_mul_test {q : ℕ} (Ω : Opens (Fin n → ℝ))
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (f : (Fin n → ℝ) → ℝ) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (Ω : Set (Fin n → ℝ)))
    (φ : TestFunction Ω ℝ (⊤ : ℕ∞)) :
    (∫ x in (Ω : Set (Fin n → ℝ)), sumSquares X f x * φ x) =
      ∫ x in (Ω : Set (Fin n → ℝ)), f x * sumSquaresTranspose X φ x := by
  have hi2 (i : Fin q) : IntegrableOn
      (fun x => fieldDerivative (X i) (fieldDerivative (X i) f) x * φ x)
      (Ω : Set (Fin n → ℝ)) volume :=
    (S.integrable_mul_test Ω (((S.contDiffOn_fieldDerivative Ω (X i) _ (hX i)
      (S.contDiffOn_fieldDerivative Ω (X i) f (hX i) hf)).continuousOn
      ).locallyIntegrableOn Ω.isOpen.measurableSet) φ).integrableOn
  have hi4 (i : Fin q) : IntegrableOn
      (fun x => f x * fieldTranspose (X i) (fieldTranspose (X i) φ) x)
      (Ω : Set (Fin n → ℝ)) volume :=
    integrableOn_mul_fieldTranspose_square Ω (X i) (hX i) hf.continuousOn φ
  have e1 : ∀ x, sumSquares X f x * φ x = ∑ i : Fin q,
      fieldDerivative (X i) (fieldDerivative (X i) f) x * φ x := by
    intro x
    simp only [sumSquares, Finset.sum_mul]
  have e2 : ∀ x, f x * sumSquaresTranspose X φ x = ∑ i : Fin q,
      f x * fieldTranspose (X i) (fieldTranspose (X i) φ) x := by
    intro x
    simp only [sumSquaresTranspose, Finset.mul_sum]
  simp_rw [e1, e2]
  rw [integral_finsetSum _ (fun i _ => hi2 i), integral_finsetSum _ (fun i _ => hi4 i)]
  exact Finset.sum_congr rfl (fun i _ =>
    integral_fieldDerivative_square_mul_test Ω (X i) (hX i) f hf φ)

end RothschildStein.P1
