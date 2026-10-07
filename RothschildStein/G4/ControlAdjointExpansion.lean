-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.FrameCalculus
public import RothschildStein.G1.BracketAlgebra
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.List.OfFn

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped BigOperators Topology

namespace RothschildStein.G4

/-- Ordered adjoints of the component fields, with the list head
acting on the left (BB Lemma 9.48, pp. 441–443). -/
def orderedAdjoints {ι : Type*} {n : ℕ}
    (Z : ι → (Fin n → ℝ) → (Fin n → ℝ)) :
    List ι → ((Fin n → ℝ) → (Fin n → ℝ)) → (Fin n → ℝ) → (Fin n → ℝ)
  | [], Y => Y
  | i :: L, Y => VectorField.lieBracket ℝ (Z i) (orderedAdjoints Z L Y)

/-- Ordered adjoints retain smoothness on the original open domain. -/
theorem orderedAdjoints_contDiffOn {ι : Type*} {n : ℕ} {Ω : Set (Fin n → ℝ)}
    (hΩ : IsOpen Ω) {Z : ι → (Fin n → ℝ) → (Fin n → ℝ)}
    (hZ : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Z i) Ω)
    {Y : (Fin n → ℝ) → (Fin n → ℝ)} (hY : ContDiffOn ℝ (⊤ : ℕ∞) Y Ω)
    (L : List ι) : ContDiffOn ℝ (⊤ : ℕ∞) (orderedAdjoints Z L Y) Ω := by
  induction L with
  | nil => exact hY
  | cons i L ih => exact G1.bracket_contDiffOn hΩ (hZ i) ih

/-- A bracket distributes over the actual constant-control field. -/
theorem bracket_constantControl_left {ι : Type*} [Fintype ι] {n : ℕ}
    (Z : ι → (Fin n → ℝ) → (Fin n → ℝ)) (a : ι → ℝ)
    (Y : (Fin n → ℝ) → (Fin n → ℝ)) {x : Fin n → ℝ}
    (hZ : ∀ i, DifferentiableAt ℝ (Z i) x) :
    VectorField.lieBracket ℝ (fun y => ∑ i, a i • Z i y) Y x =
      ∑ i, a i • VectorField.lieBracket ℝ (Z i) Y x := by
  simp only [VectorField.lieBracket]
  rw [fderiv_fun_sum (A := fun i y => a i • Z i y)
    (fun i _ => (hZ i).const_smul (a i))]
  simp only [map_sum, map_smul, sum_apply, Finset.sum_sub_distrib, smul_sub]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  change (fderiv ℝ (a i • Z i) x) (Y x) = _
  rw [fderiv_const_smul (hZ i), smul_apply]

/-- Constant coefficients factor out of a finite right-entry sum. -/
theorem bracket_sum_constantControl_right {ι : Type*} [Fintype ι] {n : ℕ}
    (T : (Fin n → ℝ) → (Fin n → ℝ))
    (Y : ι → (Fin n → ℝ) → (Fin n → ℝ)) (a : ι → ℝ)
    {x : Fin n → ℝ} (hY : ∀ i, DifferentiableAt ℝ (Y i) x) :
    VectorField.lieBracket ℝ T (fun y => ∑ i, a i • Y i y) x =
      ∑ i, a i • VectorField.lieBracket ℝ T (Y i) x := by
  rw [bracket_sum_right T (fun i y => a i • Y i y)
    (fun i => (hY i).const_smul (a i))]
  apply Finset.sum_congr rfl
  intro i hi
  exact VectorField.lieBracket_const_smul_right (hY i)

/-- Actual repeated adjoints of a constant-control field expand
into all ordered component brackets with exact coefficient products. -/
theorem adjoint_constantControl_expansion {ι : Type*} [Fintype ι] {n : ℕ}
    {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω)
    {Z : ι → (Fin n → ℝ) → (Fin n → ℝ)}
    (hZ : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Z i) Ω) (a : ι → ℝ)
    {Y : (Fin n → ℝ) → (Fin n → ℝ)} (hY : ContDiffOn ℝ (⊤ : ℕ∞) Y Ω)
    (j : ℕ) : EqOn
      ((VectorField.lieBracket ℝ (fun y => ∑ i, a i • Z i y))^[j] Y)
      (fun x => ∑ L : Fin j → ι,
        (∏ i, a (L i)) • orderedAdjoints Z (List.ofFn L) Y x) Ω := by
  classical
  induction j with
  | zero => intro x hx; simp [orderedAdjoints]
  | succ j ih =>
    intro x hx
    have he : ((VectorField.lieBracket ℝ (fun y => ∑ i, a i • Z i y))^[j] Y)
        =ᶠ[𝓝 x] (fun y => ∑ L : Fin j → ι,
          (∏ k, a (L k)) • orderedAdjoints Z (List.ofFn L) Y y) :=
      Filter.eventuallyEq_of_mem (hΩ.mem_nhds hx) ih
    rw [Function.iterate_succ_apply']
    simp only [VectorField.lieBracket, he.fderiv_eq (𝕜 := ℝ), he.eq_of_nhds]
    change VectorField.lieBracket ℝ (fun y => ∑ i, a i • Z i y)
      (fun y => ∑ L : Fin j → ι,
        (∏ k, a (L k)) • orderedAdjoints Z (List.ofFn L) Y y) x = _
    rw [bracket_constantControl_left Z a _
      (fun i => ((hZ i).contDiffAt (hΩ.mem_nhds hx)).differentiableAt (by simp))]
    simp_rw [bracket_sum_constantControl_right _ _ _
      (fun L => ((orderedAdjoints_contDiffOn hΩ hZ hY (List.ofFn L)).contDiffAt
        (hΩ.mem_nhds hx)).differentiableAt (by simp))]
    rw [← (Fin.consEquiv (fun _ : Fin (j + 1) => ι)).sum_comp,
      Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro L hL
    simp only [Fin.consEquiv_apply, Fin.prod_univ_succ, Fin.cons_zero,
      Fin.cons_succ, smul_smul]
    change _ = (a i * ∏ k, a (L k)) •
      orderedAdjoints Z (List.ofFn (Fin.cons i L)) Y x
    rw [List.ofFn_cons]
    rfl

end RothschildStein.G4
