-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.SobolevInterpolationTranspose
public import RothschildStein.Definitions.sumSquaresTranspose

/-!
# Sobolev interpolation without drift, far part: integrating `L̃` off the test function (finite regularity)

The no-drift counterpart of `SobolevInterpolationTranspose`: here `L̃ = ∑ᵢ X̃ᵢ²` (`sumSquares`, alphabet
`Fin q`, no drift field) and its transpose `L̃ᵀ = ∑ᵢ (X̃ᵢᵀ)²` (`sumSquaresTranspose`). The generic
ingredients (`integral_mul_fieldDerivative_test`, `fieldTranspose_fieldTranspose_apply_of_contDiffAt`,
`fieldDerivative_fieldDerivative_mul`) are reused.

* `integral_mul_sumSquares_noDrift`: `∫ κ L̃ g = ∫ (L̃ᵀ κ) g` for `κ ∈ C²(Ω)` and a test `g`;
* `sumSquaresTranspose_apply_of_contDiffAt_noDrift`: the formal adjoint formula without the drift term;
* `abs_sumSquaresTranspose_mul_le_noDrift`: the pointwise bound of `L̃ᵀ(f g)` by the jets of the two
  factors (the contributions of BB p. 581 without drift).
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

/-- **Integration by parts of `L̃` against the test, no drift**, for a `C²` function `κ` on `Ω`:
`∫_Ω κ · L̃ g = ∫_Ω (L̃ᵀ κ) g` (`sumSquares` and `sumSquaresTranspose`; each `X̃ᵢ` is moved onto
`κ` by `integral_mul_fieldDerivative_test`). -/
theorem integral_mul_sumSquares_noDrift {q : ℕ} (Ω : Opens (Fin n → ℝ))
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ))) (κ : (Fin n → ℝ) → ℝ)
    (hκ : ContDiffOn ℝ 2 κ (Ω : Set (Fin n → ℝ))) (g : TestFunction Ω ℝ (⊤ : ℕ∞)) :
    (∫ x in (Ω : Set (Fin n → ℝ)), κ x * sumSquares X g x) =
      ∫ x in (Ω : Set (Fin n → ℝ)), sumSquaresTranspose X κ x * g x := by
  have hκ1 : ContDiffOn ℝ 1 κ (Ω : Set (Fin n → ℝ)) := hκ.of_le (by norm_num)
  have hκ2 : ContDiffOn ℝ ((1 + 1 : ℕ) : WithTop ℕ∞) κ (Ω : Set (Fin n → ℝ)) := by
    exact_mod_cast hκ
  have hT1 : ∀ i, ContDiffOn ℝ 1 (fieldTranspose (X i) κ) (Ω : Set (Fin n → ℝ)) := fun i => by
    have := contDiffOn_fieldTranspose_succ Ω (X i) κ 1 (hX i) hκ2
    exact_mod_cast this
  have hT1' : ∀ i, ContDiffOn ℝ ((0 + 1 : ℕ) : WithTop ℕ∞) (fieldTranspose (X i) κ)
      (Ω : Set (Fin n → ℝ)) := fun i => by exact_mod_cast hT1 i
  have hTT : ∀ i, ContinuousOn (fieldTranspose (X i) (fieldTranspose (X i) κ))
      (Ω : Set (Fin n → ℝ)) := fun i => by
    have := contDiffOn_fieldTranspose_succ Ω (X i) (fieldTranspose (X i) κ) 0 (hX i) (hT1' i)
    exact this.continuousOn
  have hli : ∀ f : (Fin n → ℝ) → ℝ, ContinuousOn f (Ω : Set (Fin n → ℝ)) →
      LocallyIntegrableOn f (Ω : Set (Fin n → ℝ)) volume := fun f hf =>
    hf.locallyIntegrableOn Ω.isOpen.measurableSet
  -- the tests `X g` and `X X g`
  let g1 : Fin q → TestFunction Ω ℝ (⊤ : ℕ∞) := fun i => S.wordDerivativeTest Ω X hX [i] g
  have hg1 : ∀ i, (g1 i : (Fin n → ℝ) → ℝ) = fieldDerivative (X i) g := fun i => rfl
  let g2 : Fin q → TestFunction Ω ℝ (⊤ : ℕ∞) := fun i =>
    S.wordDerivativeTest Ω X hX [i, i] g
  have hg2 : ∀ i : Fin q, (g2 i : (Fin n → ℝ) → ℝ) =
      fieldDerivative (X i) (fieldDerivative (X i) g) := fun i => rfl
  have lhs1 : ∀ i : Fin q, IntegrableOn
      (fun x => κ x * fieldDerivative (X i) (fieldDerivative (X i) g) x)
      (Ω : Set (Fin n → ℝ)) volume := fun i => by
    have := S.integrable_mul_test Ω (hli κ hκ.continuousOn) (g2 i)
    simp only [hg2] at this
    exact this.integrableOn
  have rhs1 : ∀ i : Fin q, IntegrableOn
      (fun x => fieldTranspose (X i) (fieldTranspose (X i) κ) x * g x)
      (Ω : Set (Fin n → ℝ)) volume := fun i =>
    (S.integrable_mul_test Ω (hli _ (hTT i)) g).integrableOn
  have e1 : ∀ x, κ x * sumSquares X g x =
      ∑ i : Fin q, κ x * fieldDerivative (X i) (fieldDerivative (X i) g) x := by
    intro x
    simp only [sumSquares, Finset.mul_sum]
  have e2 : ∀ x, sumSquaresTranspose X κ x * g x =
      ∑ i : Fin q, fieldTranspose (X i) (fieldTranspose (X i) κ) x * g x := by
    intro x
    simp only [sumSquaresTranspose, Finset.sum_mul]
  simp_rw [e1, e2]
  rw [integral_finsetSum _ (fun i _ => lhs1 i), integral_finsetSum _ (fun i _ => rhs1 i)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have h1 := integral_mul_fieldDerivative_test Ω (X i) (hX i) κ hκ1 (g1 i)
  rw [hg1] at h1
  have h2 := integral_mul_fieldDerivative_test Ω (X i) (hX i)
    (fieldTranspose (X i) κ) (hT1 i) g
  rw [h1, h2]

/-- **The formal adjoint formula at a point, no drift**, for a function that is `C²` at the point: the transpose of `L̃ = ∑ᵢ X̃ᵢ²` is `∑ᵢ X̃ᵢ²φ + 2 ∑ᵢ dᵢ X̃ᵢφ + ∑ᵢ (X̃ᵢ dᵢ + dᵢ²) φ`. -/
theorem sumSquaresTranspose_apply_of_contDiffAt_noDrift {q : ℕ} (Ω : Opens (Fin n → ℝ))
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (φ : (Fin n → ℝ) → ℝ) {x : Fin n → ℝ} (hx : x ∈ (Ω : Set (Fin n → ℝ)))
    (hφ : ContDiffAt ℝ 2 φ x) :
    sumSquaresTranspose X φ x =
      ∑ i : Fin q, fieldDerivative (X i) (fieldDerivative (X i) φ) x +
        2 * ∑ i : Fin q, Hormander.Interface.euclideanDivergence (X i) x *
          fieldDerivative (X i) φ x +
        ∑ i : Fin q, (fieldDerivative (X i)
            (Hormander.Interface.euclideanDivergence (X i)) x +
          Hormander.Interface.euclideanDivergence (X i) x ^ 2) * φ x := by
  have hsq : ∀ i : Fin q, fieldTranspose (X i) (fieldTranspose (X i) φ) x =
      fieldDerivative (X i) (fieldDerivative (X i) φ) x +
        2 * (Hormander.Interface.euclideanDivergence (X i) x *
          fieldDerivative (X i) φ x) +
        (fieldDerivative (X i) (Hormander.Interface.euclideanDivergence (X i)) x +
          Hormander.Interface.euclideanDivergence (X i) x ^ 2) * φ x :=
    fun i => fieldTranspose_fieldTranspose_apply_of_contDiffAt Ω (X i) (hX i) φ hx hφ
  simp only [sumSquaresTranspose, hsq, Finset.sum_add_distrib, Finset.mul_sum]

/-- Triangle inequality for the three groups of terms of the formal adjoint formula without drift. -/
theorem abs_three_le_noDrift (a c d : ℝ) :
    |a + 2 * c + d| ≤ |a| + 2 * |c| + |d| := by
  rw [abs_le]
  constructor <;> linarith [le_abs_self a, neg_abs_le a, le_abs_self c, neg_abs_le c,
    le_abs_self d, neg_abs_le d]

/-- **The pointwise bound of `L̃ᵀ(f g)`, no drift** (the contributions of BB p. 581): let
`f` (the kernel) and `g` (the cutoff) be `C²` at `x ∈ Ω`, `0 < d ≤ D₀`, and suppose
`|f| ≤ M d² u`, `|X̃ᵢ f| ≤ M d u`, `|X̃ᵢ² f| ≤ M u` and `|g| ≤ 1`, `d |X̃ᵢ g| ≤ B₁`,
`d² |X̃ᵢ² g| ≤ B₂`, with the divergence coefficients of `L̃ᵀ` bounded by `Cd`. Then
`|L̃ᵀ(f g)(x)| ≤ K u` with `K` depending on `M, B₁, B₂, Cd, D₀, q` only. -/
theorem abs_sumSquaresTranspose_mul_le_noDrift {q : ℕ} (Ω : Opens (Fin n → ℝ))
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    {x : Fin n → ℝ} (hx : x ∈ (Ω : Set (Fin n → ℝ))) {f g : (Fin n → ℝ) → ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x)
    {Cd M B₁ B₂ u d D₀ : ℝ}
    (hd : ∀ i : Fin q, |Hormander.Interface.euclideanDivergence (X i) x| ≤ Cd)
    (he : ∀ i : Fin q, |fieldDerivative (X i)
      (Hormander.Interface.euclideanDivergence (X i)) x +
        Hormander.Interface.euclideanDivergence (X i) x ^ 2| ≤ Cd)
    (hCd : 0 ≤ Cd) (hM : 0 ≤ M) (hB₁ : 0 ≤ B₁) (hu : 0 ≤ u) (hdpos : 0 < d)
    (hdD : d ≤ D₀)
    (hf0 : |f x| ≤ M * d ^ 2 * u)
    (hf1 : ∀ i : Fin q, |fieldDerivative (X i) f x| ≤ M * d * u)
    (hf2 : ∀ i : Fin q, |fieldDerivative (X i) (fieldDerivative (X i) f) x| ≤ M * u)
    (hg0 : |g x| ≤ 1)
    (hg1 : ∀ i : Fin q, |fieldDerivative (X i) g x| * d ≤ B₁)
    (hg2 : ∀ i : Fin q, |fieldDerivative (X i) (fieldDerivative (X i) g) x| * d ^ 2 ≤ B₂) :
    |sumSquaresTranspose X (fun y => f y * g y) x| ≤
      M * (q * (1 + 2 * B₁ + B₂) + 2 * q * Cd * D₀ * (1 + B₁) + q * Cd * D₀ ^ 2) * u := by
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
  have hφ1 : ∀ i : Fin q, |fieldDerivative (X i) (fun y => f y * g y) x| ≤
      M * u * (d + d * B₁) := by
    intro i
    rw [S.fieldDerivative_mul (X i) f g x hfdx hgdx]
    have h1 : |fieldDerivative (X i) f x * g x| ≤ M * d * u := by
      rw [abs_mul]
      calc |fieldDerivative (X i) f x| * |g x| ≤ (M * d * u) * 1 :=
            mul_le_mul (hf1 i) habs (abs_nonneg _) (by positivity)
        _ = M * d * u := by ring
    have h2 : |f x * fieldDerivative (X i) g x| ≤ M * u * (d * B₁) := by
      rw [abs_mul]
      have hg1' : |fieldDerivative (X i) g x| * d ≤ B₁ := hg1 i
      calc |f x| * |fieldDerivative (X i) g x| ≤
            (M * d ^ 2 * u) * |fieldDerivative (X i) g x| :=
            mul_le_mul_of_nonneg_right hf0 (abs_nonneg _)
        _ = M * u * d * (|fieldDerivative (X i) g x| * d) := by ring
        _ ≤ M * u * d * B₁ := mul_le_mul_of_nonneg_left hg1' (by positivity)
        _ = M * u * (d * B₁) := by ring
    calc _ ≤ |fieldDerivative (X i) f x * g x| + |f x * fieldDerivative (X i) g x| :=
          abs_add_le _ _
      _ ≤ M * d * u + M * u * (d * B₁) := add_le_add h1 h2
      _ = M * u * (d + d * B₁) := by ring
  have hφ2 : ∀ i : Fin q, |fieldDerivative (X i) (fieldDerivative (X i)
      (fun y => f y * g y)) x| ≤ M * u * (1 + 2 * B₁ + B₂) := by
    intro i
    rw [fieldDerivative_fieldDerivative_mul hf hg (hXc i)]
    have h1 : |fieldDerivative (X i) (fieldDerivative (X i) f) x * g x| ≤ M * u := by
      rw [abs_mul]
      calc _ ≤ (M * u) * 1 := mul_le_mul (hf2 i) habs (abs_nonneg _) (by positivity)
        _ = M * u := by ring
    have h2 : |2 * (fieldDerivative (X i) f x * fieldDerivative (X i) g x)| ≤
        2 * (M * u * B₁) := by
      rw [abs_mul, abs_mul, abs_two]
      have hg1' : |fieldDerivative (X i) g x| * d ≤ B₁ := hg1 i
      refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
      calc |fieldDerivative (X i) f x| * |fieldDerivative (X i) g x| ≤
            (M * d * u) * |fieldDerivative (X i) g x| :=
            mul_le_mul_of_nonneg_right (hf1 i) (abs_nonneg _)
        _ = M * u * (|fieldDerivative (X i) g x| * d) := by ring
        _ ≤ M * u * B₁ := mul_le_mul_of_nonneg_left hg1' (by positivity)
    have h3 : |f x * fieldDerivative (X i) (fieldDerivative (X i) g) x| ≤
        M * u * B₂ := by
      rw [abs_mul]
      have hg2' := hg2 i
      calc |f x| * |fieldDerivative (X i) (fieldDerivative (X i) g) x| ≤
            (M * d ^ 2 * u) * |fieldDerivative (X i) (fieldDerivative (X i) g) x| :=
            mul_le_mul_of_nonneg_right hf0 (abs_nonneg _)
        _ = M * u * (|fieldDerivative (X i) (fieldDerivative (X i) g) x| * d ^ 2) := by
            ring
        _ ≤ M * u * B₂ := mul_le_mul_of_nonneg_left hg2' (by positivity)
    calc _ ≤ |fieldDerivative (X i) (fieldDerivative (X i) f) x * g x| +
          |2 * (fieldDerivative (X i) f x * fieldDerivative (X i) g x)| +
          |f x * fieldDerivative (X i) (fieldDerivative (X i) g) x| := abs_add_three _ _ _
      _ ≤ M * u + 2 * (M * u * B₁) + M * u * B₂ := add_le_add (add_le_add h1 h2) h3
      _ = M * u * (1 + 2 * B₁ + B₂) := by ring
  -- the three sums
  have hS1 : |∑ i : Fin q, fieldDerivative (X i) (fieldDerivative (X i)
      (fun y => f y * g y)) x| ≤ q * (M * u * (1 + 2 * B₁ + B₂)) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i : Fin q, |fieldDerivative (X i) (fieldDerivative (X i)
          (fun y => f y * g y)) x| ≤ ∑ _i : Fin q, M * u * (1 + 2 * B₁ + B₂) :=
          Finset.sum_le_sum (fun i _ => hφ2 i)
      _ = q * (M * u * (1 + 2 * B₁ + B₂)) := by simp
  have hS3 : |∑ i : Fin q, Hormander.Interface.euclideanDivergence (X i) x *
      fieldDerivative (X i) (fun y => f y * g y) x| ≤
      q * (Cd * (M * u * (d + d * B₁))) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i : Fin q, |Hormander.Interface.euclideanDivergence (X i) x *
          fieldDerivative (X i) (fun y => f y * g y) x| ≤
          ∑ _i : Fin q, Cd * (M * u * (d + d * B₁)) :=
          Finset.sum_le_sum (fun i _ => by
            rw [abs_mul]
            exact mul_le_mul (hd i) (hφ1 i) (abs_nonneg _) hCd)
      _ = q * (Cd * (M * u * (d + d * B₁))) := by simp
  have hS4 : |∑ i : Fin q, (fieldDerivative (X i)
      (Hormander.Interface.euclideanDivergence (X i)) x +
        Hormander.Interface.euclideanDivergence (X i) x ^ 2) * (f x * g x)| ≤
      q * (Cd * (M * d ^ 2 * u)) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i : Fin q, |(fieldDerivative (X i)
          (Hormander.Interface.euclideanDivergence (X i)) x +
            Hormander.Interface.euclideanDivergence (X i) x ^ 2) * (f x * g x)| ≤
          ∑ _i : Fin q, Cd * (M * d ^ 2 * u) :=
          Finset.sum_le_sum (fun i _ => by
            rw [abs_mul]
            exact mul_le_mul (he i) hφ0 (abs_nonneg _) hCd)
      _ = q * (Cd * (M * d ^ 2 * u)) := by simp
  have key := sumSquaresTranspose_apply_of_contDiffAt_noDrift Ω X hX (fun y => f y * g y) hx hfg
  beta_reduce at key
  rw [key]
  refine (abs_three_le_noDrift _ _ _).trans ?_
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hMu : 0 ≤ M * u := mul_nonneg hM hu
  have hdB : d + d * B₁ ≤ D₀ + D₀ * B₁ := by nlinarith
  have h4 : M * d ^ 2 * u ≤ M * D₀ ^ 2 * u :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdd hM) hu
  calc _ ≤ q * (M * u * (1 + 2 * B₁ + B₂)) + 2 * (q * (Cd * (M * u * (d + d * B₁)))) +
        q * (Cd * (M * d ^ 2 * u)) :=
        add_le_add (add_le_add hS1 (mul_le_mul_of_nonneg_left hS3 (by norm_num))) hS4
    _ ≤ q * (M * u * (1 + 2 * B₁ + B₂)) + 2 * (q * (Cd * (M * u * (D₀ + D₀ * B₁)))) +
        q * (Cd * (M * D₀ ^ 2 * u)) := by
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
    _ = M * (q * (1 + 2 * B₁ + B₂) + 2 * q * Cd * D₀ * (1 + B₁) + q * Cd * D₀ ^ 2) * u := by ring

end RothschildStein.P2
