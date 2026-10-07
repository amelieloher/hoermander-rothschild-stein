-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.FractionalInterpolationFar
public import RothschildStein.Definitions.sumSquares
public import RothschildStein.Definitions.sumSquaresWithDrift
public import RothschildStein.Definitions.fieldDerivative

/-!
# Hölder interpolation: the lifted operator in coordinates

The lifted operators `L̃ = ∑ᵢ X̃ᵢ² + X̃₀` (drift chart) and `L̃ = ∑ᵢ X̃ᵢ²` (drift-free chart) are second
order operators with smooth coefficients: on an open set `O` where the fields are smooth,
`L̃ f = ∑_{a,b} A_{ab} ∂_a ∂_b f + ∑_a B_a ∂_a f`, `A_{ab} = ∑ᵢ X̃ᵢ^a X̃ᵢ^b`,
`B_a = ∑ᵢ X̃ᵢ(X̃ᵢ^a) + X̃₀^a` (`sumSquaresWithDrift_eq_diffOp2`, `sumSquares_eq_diffOp2`). This is the
form consumed by the far estimate (`far_estimate`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators
namespace RothschildStein.P2

variable {N : ℕ}

theorem fieldDerivative_eq_sum {V : (Fin N → ℝ) → (Fin N → ℝ)} {f : (Fin N → ℝ) → ℝ}
    {x : Fin N → ℝ} :
    RothschildStein.fieldDerivative V f x = ∑ a, V x a * pdv a f x := by
  unfold RothschildStein.fieldDerivative
  conv_lhs => rw [← sum_unitVec_smul (V x)]
  simp only [map_sum, map_smul, smul_eq_mul]
  rfl

/-- `X(X f)` in coordinates, for a field smooth on the open set `O` and `f ∈ C²(O)`. -/
theorem fieldDerivative_square_eq {O : Set (Fin N → ℝ)} (hO : IsOpen O)
    {V : (Fin N → ℝ) → (Fin N → ℝ)} (hV : ContDiffOn ℝ (⊤ : ℕ∞) V O)
    {f : (Fin N → ℝ) → ℝ} (hf : ContDiffOn ℝ 2 f O) {x : Fin N → ℝ} (hx : x ∈ O) :
    RothschildStein.fieldDerivative V (RothschildStein.fieldDerivative V f) x =
      ∑ a, ∑ b, (V x a * V x b) * pdv a (pdv b f) x +
        ∑ a, RothschildStein.fieldDerivative V (fun y => V y a) x * pdv a f x := by
  have hdf : ∀ y ∈ O, DifferentiableAt ℝ f y := fun y hy =>
    (hf.contDiffAt (hO.mem_nhds hy)).differentiableAt (by norm_num)
  have hev : RothschildStein.fieldDerivative V f =ᶠ[𝓝 x] fun y => ∑ a, V y a * pdv a f y := by
    filter_upwards [hO.mem_nhds hx] with y hy
    exact fieldDerivative_eq_sum
  have hVa : ∀ a, DifferentiableAt ℝ (fun y => V y a) x := fun a =>
    (((contDiff_apply ℝ ℝ a).comp_contDiffOn hV).contDiffAt (hO.mem_nhds hx)).differentiableAt
      (by simp)
  have hpa : ∀ a, DifferentiableAt ℝ (pdv a f) x := fun a =>
    ((contDiffOn_pdv (n := 1) hO hf a).contDiffAt (hO.mem_nhds hx)).differentiableAt one_ne_zero
  unfold RothschildStein.fieldDerivative
  have h1 : fderiv ℝ (fun y => fderiv ℝ f y (V y)) x =
      fderiv ℝ (fun y => ∑ a, V y a * pdv a f y) x := hev.fderiv_eq
  rw [h1]
  have h2 : HasFDerivAt (fun y => ∑ a, V y a * pdv a f y)
      (∑ a, ((V x a) • fderiv ℝ (pdv a f) x + pdv a f x • fderiv ℝ (fun y => V y a) x)) x := by
    refine HasFDerivAt.fun_sum (fun a _ => ?_)
    exact (hVa a).hasFDerivAt.mul (hpa a).hasFDerivAt
  rw [h2.fderiv]
  simp only [sum_apply, add_apply, smul_apply, smul_eq_mul]
  have h3 : ∀ a, fderiv ℝ (pdv a f) x (V x) = ∑ b, V x b * pdv b (pdv a f) x := fun a =>
    fieldDerivative_eq_sum
  simp only [h3, Finset.sum_add_distrib]
  have e1 : ∑ a, V x a * ∑ b, V x b * pdv b (pdv a f) x =
      ∑ a, ∑ b, (V x a * V x b) * pdv a (pdv b f) x := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring
  rw [e1]
  congr 1
  exact Finset.sum_congr rfl fun a _ => by ring

/-- A sum of squares of smooth fields plus a smooth first-order field is a second-order
operator in coordinates with `C²`/`C¹` coefficients on `O`. -/
theorem exists_diffOp2_of_fields {p : ℕ} {O : Set (Fin N → ℝ)} (hO : IsOpen O)
    (V : Fin p → (Fin N → ℝ) → (Fin N → ℝ)) (W : (Fin N → ℝ) → (Fin N → ℝ))
    (hV : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (V i) O) (hW : ContDiffOn ℝ (⊤ : ℕ∞) W O) :
    ∃ (A : Fin N → Fin N → (Fin N → ℝ) → ℝ) (B : Fin N → (Fin N → ℝ) → ℝ),
      (∀ a b, ContDiffOn ℝ 2 (A a b) O) ∧ (∀ a, ContDiffOn ℝ 1 (B a) O) ∧
      ∀ f : (Fin N → ℝ) → ℝ, ContDiffOn ℝ 2 f O → ∀ x ∈ O,
        RothschildStein.fieldDerivative W f x +
          ∑ i, RothschildStein.fieldDerivative (V i)
            (RothschildStein.fieldDerivative (V i) f) x = diffOp2 A B f x := by
  have hVa : ∀ i a, ContDiffOn ℝ (⊤ : ℕ∞) (fun y => V i y a) O := fun i a =>
    (contDiff_apply ℝ ℝ a).comp_contDiffOn (hV i)
  refine ⟨fun a b x => ∑ i, V i x a * V i x b,
    fun a x => ∑ i, RothschildStein.fieldDerivative (V i) (fun y => V i y a) x + W x a,
    fun a b => ?_, fun a => ?_, fun f hf x hx => ?_⟩
  · refine (ContDiffOn.sum fun i _ => (hVa i a).mul (hVa i b)).of_le (by simp)
  · refine ((ContDiffOn.sum fun i _ => ?_).add ((contDiff_apply ℝ ℝ a).comp_contDiffOn hW)).of_le
      (by simp)
    exact ((hVa i a).fderiv_of_isOpen hO (by simp)).clm_apply (hV i)
  · rw [fieldDerivative_eq_sum]
    simp_rw [fieldDerivative_square_eq hO (hV _) hf hx]
    simp only [diffOp2, Finset.sum_add_distrib, add_mul, Finset.sum_mul]
    have e1 : ∑ i, ∑ a, ∑ b, V i x a * V i x b * pdv a (pdv b f) x =
        ∑ a, ∑ b, ∑ i, V i x a * V i x b * pdv a (pdv b f) x := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_comm
    have e2 : ∑ i, ∑ a, RothschildStein.fieldDerivative (V i) (fun y => V i y a) x * pdv a f x =
        ∑ a, ∑ i, RothschildStein.fieldDerivative (V i) (fun y => V i y a) x * pdv a f x :=
      Finset.sum_comm
    rw [e1, e2]
    ring

/-- The lifted operator with drift `L̃ = X̃₀ + ∑ᵢ X̃ᵢ²` is a second-order operator in
coordinates on any open set where the fields are smooth. -/
theorem sumSquaresWithDrift_eq_diffOp2 {q : ℕ} {O : Set (Fin N → ℝ)} (hO : IsOpen O)
    (X : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) O) :
    ∃ (A : Fin N → Fin N → (Fin N → ℝ) → ℝ) (B : Fin N → (Fin N → ℝ) → ℝ),
      (∀ a b, ContDiffOn ℝ 2 (A a b) O) ∧ (∀ a, ContDiffOn ℝ 1 (B a) O) ∧
      ∀ f : (Fin N → ℝ) → ℝ, ContDiffOn ℝ 2 f O → ∀ x ∈ O,
        sumSquaresWithDrift X f x = diffOp2 A B f x := by
  obtain ⟨A, B, hA, hB, h⟩ := exists_diffOp2_of_fields hO (fun i : Fin q => X i.succ) (X 0)
    (fun i => hX i.succ) (hX 0)
  exact ⟨A, B, hA, hB, fun f hf x hx => (h f hf x hx)⟩

/-- The drift-free lifted operator `L̃ = ∑ᵢ X̃ᵢ²` is a second-order operator in coordinates. -/
theorem sumSquares_eq_diffOp2 {q : ℕ} {O : Set (Fin N → ℝ)} (hO : IsOpen O)
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)) (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) O) :
    ∃ (A : Fin N → Fin N → (Fin N → ℝ) → ℝ) (B : Fin N → (Fin N → ℝ) → ℝ),
      (∀ a b, ContDiffOn ℝ 2 (A a b) O) ∧ (∀ a, ContDiffOn ℝ 1 (B a) O) ∧
      ∀ f : (Fin N → ℝ) → ℝ, ContDiffOn ℝ 2 f O → ∀ x ∈ O,
        sumSquares X f x = diffOp2 A B f x := by
  obtain ⟨A, B, hA, hB, h⟩ := exists_diffOp2_of_fields hO X (fun _ => 0) hX contDiffOn_const
  refine ⟨A, B, hA, hB, fun f hf x hx => ?_⟩
  have := h f hf x hx
  simpa [RothschildStein.fieldDerivative, sumSquares] using this

end RothschildStein.P2
