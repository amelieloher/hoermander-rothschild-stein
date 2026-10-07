-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.FlowDirectionalDerivatives
public import RothschildStein.G4.IteratedGeneratorDifferentiation
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.List.OfFn

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped BigOperators Topology

namespace RothschildStein.G4

/-- Ordered field derivatives are smooth on the original open domain. -/
theorem shortDerivatives_contDiffOn {ι : Type*} {n : ℕ} {Ω : Set (Fin n → ℝ)}
    (hΩ : IsOpen Ω) {Z : ι → (Fin n → ℝ) → (Fin n → ℝ)}
    (hZ : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Z i) Ω)
    {f : (Fin n → ℝ) → ℝ} (hf : ContDiffOn ℝ (⊤ : ℕ∞) f Ω) (L : List ι) :
    ContDiffOn ℝ (⊤ : ℕ∞) (shortDerivatives Z L f) Ω := by
  induction L with
  | nil => exact hf
  | cons i L ih => exact (ih.fderiv_of_isOpen hΩ (by simp)).clm_apply (hZ i)

/-- A constant control derivative is the exact finite linear
combination of the component derivatives. -/
theorem fieldDerivative_constantControl {ι : Type*} [Fintype ι] {n : ℕ}
    (Z : ι → (Fin n → ℝ) → (Fin n → ℝ)) (a : ι → ℝ)
    (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) :
    fieldDerivative (fun y => ∑ i, a i • Z i y) f x =
      ∑ i, a i * fieldDerivative (Z i) f x := by
  simp only [fieldDerivative, map_sum, map_smul, smul_eq_mul]

/-- Directional differentiation distributes over a finite
constant-coefficient sum of smooth functions on the open domain. -/
theorem fieldDerivative_sum_const_mul {κ : Type*} {n : ℕ} {Ω : Set (Fin n → ℝ)}
    (hΩ : IsOpen Ω) (T : (Fin n → ℝ) → (Fin n → ℝ)) (S : Finset κ)
    (c : κ → ℝ) (f : κ → (Fin n → ℝ) → ℝ)
    (hf : ∀ i ∈ S, ContDiffOn ℝ (⊤ : ℕ∞) (f i) Ω) {x : Fin n → ℝ} (hx : x ∈ Ω) :
    fieldDerivative T (fun y => ∑ i ∈ S, c i * f i y) x =
      ∑ i ∈ S, c i * fieldDerivative T (f i) x := by
  have hd : ∀ i ∈ S, DifferentiableAt ℝ (f i) x :=
    fun i hi => ((hf i hi).contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by simp)
  simp only [fieldDerivative]
  rw [fderiv_fun_sum (fun i hi => (hd i hi).const_mul (c i))]
  simp only [sum_apply]
  apply Finset.sum_congr rfl
  intro i hi
  rw [fderiv_const_mul (hd i hi) (c i)]
  simp only [smul_apply, smul_eq_mul]

/-- Actual powers of the constant-control derivative expand into
all ordered component words, with their exact coefficient products. -/
theorem fieldIterates_constantControl_expansion {ι : Type*} [Fintype ι] {n : ℕ}
    {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω)
    {Z : ι → (Fin n → ℝ) → (Fin n → ℝ)}
    (hZ : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Z i) Ω)
    (a : ι → ℝ) {f : (Fin n → ℝ) → ℝ} (hf : ContDiffOn ℝ (⊤ : ℕ∞) f Ω) (j : ℕ) :
    EqOn (fieldIterates (fun y => ∑ i, a i • Z i y) j f)
      (fun x => ∑ L : Fin j → ι, (∏ i, a (L i)) * shortDerivatives Z (List.ofFn L) f x) Ω := by
  classical
  induction j with
  | zero => intro x hx; simp [fieldIterates, shortDerivatives]
  | succ j ih =>
    intro x hx
    have he : fieldIterates (fun y => ∑ i, a i • Z i y) j f =ᶠ[𝓝 x]
        (fun y => ∑ L : Fin j → ι, (∏ i, a (L i)) * shortDerivatives Z (List.ofFn L) f y) :=
      Filter.eventuallyEq_of_mem (hΩ.mem_nhds hx) ih
    change fieldDerivative (fun y => ∑ i, a i • Z i y)
      (fieldIterates (fun y => ∑ i, a i • Z i y) j f) x = _
    rw [fieldDerivative_constantControl]
    simp_rw [fieldDerivative, he.fderiv_eq (𝕜 := ℝ)]
    change (∑ i, a i * fieldDerivative (Z i)
      (fun y => ∑ L : Fin j → ι, (∏ k, a (L k)) * shortDerivatives Z (List.ofFn L) f y) x) = _
    simp_rw [fieldDerivative_sum_const_mul hΩ _ Finset.univ _ _
      (fun L _ => shortDerivatives_contDiffOn hΩ hZ hf (List.ofFn L)) hx]
    rw [← (Fin.consEquiv (fun _ : Fin (j + 1) => ι)).sum_comp]
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro L hL
    simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
    change a i * ((∏ k, a (L k)) * fieldDerivative (Z i) (shortDerivatives Z (List.ofFn L) f) x) =
      (a i * ∏ k, a (L k)) * shortDerivatives Z (List.ofFn (Fin.cons i L)) f x
    rw [List.ofFn_cons]
    change _ = (a i * ∏ k, a (L k)) * fieldDerivative (Z i) (shortDerivatives Z (List.ofFn L) f) x
    ring

end RothschildStein.G4
