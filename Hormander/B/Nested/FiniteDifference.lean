-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Comp
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries

@[expose] public section

noncomputable section

open scoped ContDiff

namespace Hormander.B

section
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V]
  [NormedSpace ℝ V]

/-- The forward difference `Δ_h Φ (η) = Φ (η + h) - Φ η`. -/
def fdiff (h : E) (Φ : E → V) : E → V := fun η => Φ (η + h) - Φ η

/-- The `q`-fold finite difference `Δ_{h₀} Δ_{h₁} ⋯ Δ_{h_{q-1}} Φ` (outermost `h₀`). -/
def fdiffs : (q : ℕ) → (Fin q → E) → (E → V) → (E → V)
  | 0, _, Φ => Φ
  | q + 1, h, Φ => fdiff (h 0) (fdiffs q (Fin.tail h) Φ)

omit [NormedSpace ℝ E] [NormedSpace ℝ V] in
@[simp] theorem fdiffs_zero (h : Fin 0 → E) (Φ : E → V) : fdiffs 0 h Φ = Φ := rfl

omit [NormedSpace ℝ E] [NormedSpace ℝ V] in
theorem fdiffs_succ (q : ℕ) (h : Fin (q + 1) → E) (Φ : E → V) :
    fdiffs (q + 1) h Φ = fdiff (h 0) (fdiffs q (Fin.tail h) Φ) := rfl

theorem differentiable_fdiff {Ψ : E → V} (hΨ : Differentiable ℝ Ψ) (h : E) :
    Differentiable ℝ (fdiff h Ψ) := by
  unfold fdiff
  exact (hΨ.comp (differentiable_id.add_const h)).sub hΨ

theorem differentiable_fdiffs (q : ℕ) (h : Fin q → E) {Φ : E → V} (hΦ : Differentiable ℝ Φ) :
    Differentiable ℝ (fdiffs q h Φ) := by
  induction q with
  | zero => simpa using hΦ
  | succ q ih => exact differentiable_fdiff (ih _) _

/-- Directional derivatives commute with finite differences. -/
theorem fderiv_fdiffs (q : ℕ) (h : Fin q → E) {Φ : E → V} (hΦ : Differentiable ℝ Φ) (v : E)
    (z : E) :
    fderiv ℝ (fdiffs q h Φ) z v = fdiffs q h (fun y => fderiv ℝ Φ y v) z := by
  induction q generalizing z with
  | zero => simp
  | succ q ih =>
    have hΨ := differentiable_fdiffs q (Fin.tail h) hΦ
    have e : fdiff (h 0) (fdiffs q (Fin.tail h) Φ) = fun y =>
        fdiffs q (Fin.tail h) Φ (y + h 0) - fdiffs q (Fin.tail h) Φ y := rfl
    rw [fdiffs_succ, e]
    rw [fderiv_fun_sub (by exact (hΨ.comp (differentiable_id.add_const (h 0))) z) (hΨ z),
      fderiv_comp_add_right, sub_apply, ih, ih, fdiffs_succ]
    rfl

/-- Mean value inequality along a segment, in directional form. -/
theorem norm_fdiff_le_of_segment {Ψ : E → V} (hΨ : Differentiable ℝ Ψ) (η h : E) {B : ℝ}
    (hB : ∀ t : ℝ, t ∈ Set.Icc (0 : ℝ) 1 → ‖fderiv ℝ Ψ (η + t • h) h‖ ≤ B) :
    ‖fdiff h Ψ η‖ ≤ B := by
  have hd : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Ψ (η + t • h)) (fderiv ℝ Ψ (η + t • h) h) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => η + t • h) h t := by
      simpa using ((hasDerivAt_id t).smul_const h).const_add η
    exact (hΨ (η + t • h)).hasFDerivAt.comp_hasDerivAt t h1
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := fun t : ℝ => Ψ (η + t • h))
    (f' := fun t => fderiv ℝ Ψ (η + t • h) h) (C := B) (s := Set.Icc (0 : ℝ) 1) (x := 0) (y := 1)
    (fun t _ => (hd t).hasDerivWithinAt) (fun t ht => hB t ht) (convex_Icc 0 1)
    ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩
  simpa [fdiff] using this

/-- Norm of the iterated derivative of a directional derivative. -/
theorem norm_iteratedFDeriv_fderiv_apply_le {q : ℕ} {Φ : E → V} (hΦ : ContDiff ℝ (q + 1 : ℕ) Φ)
    (v w : E) :
    ‖iteratedFDeriv ℝ q (fun y => fderiv ℝ Φ y v) w‖ ≤ ‖v‖ * ‖iteratedFDeriv ℝ (q + 1) Φ w‖ := by
  have hf : ContDiff ℝ q (fderiv ℝ Φ) :=
    ContDiff.fderiv_right (m := (q : WithTop ℕ∞)) hΦ (by norm_cast)
  have e := (ContinuousLinearMap.apply ℝ V v).iteratedFDeriv_comp_left (hf.contDiffAt (x := w))
    (i := q) le_rfl
  rw [← norm_iteratedFDeriv_fderiv]
  have e' : iteratedFDeriv ℝ q (fun y => fderiv ℝ Φ y v) w =
      (ContinuousLinearMap.apply ℝ V v).compContinuousMultilinearMap
        (iteratedFDeriv ℝ q (fderiv ℝ Φ) w) := e
  rw [e']
  have hL : ‖ContinuousLinearMap.apply ℝ V v‖ ≤ ‖v‖ :=
    ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg v) (fun f => by
      simpa [mul_comm] using f.le_opNorm v)
  exact (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans
    (mul_le_mul_of_nonneg_right hL (norm_nonneg _))

/-- Finite-difference estimate by the `q`-th derivative on the parallelepiped spanned by the
increments (integral remainder in inequality form). -/
theorem norm_fdiffs_le (q : ℕ) : ∀ {Φ : E → V}, ContDiff ℝ q Φ → ∀ (η : E) (h : Fin q → E) (M : ℝ),
    (∀ t : Fin q → ℝ, (∀ i, t i ∈ Set.Icc (0 : ℝ) 1) →
      ‖iteratedFDeriv ℝ q Φ (η + ∑ i, t i • h i)‖ ≤ M) →
    ‖fdiffs q h Φ η‖ ≤ (∏ i, ‖h i‖) * M := by
  induction q with
  | zero =>
    intro Φ _ η h M hM
    have := hM (fun i => i.elim0) (fun i => i.elim0)
    simpa [norm_iteratedFDeriv_zero] using this
  | succ q ih =>
    intro Φ hΦ η h M hM
    have hdiff : Differentiable ℝ Φ := hΦ.differentiable (by simp)
    have hΨ := differentiable_fdiffs q (Fin.tail h) hdiff
    rw [fdiffs_succ]
    have hΦ1 : ContDiff ℝ q (fun y => fderiv ℝ Φ y (h 0)) := by
      have hf : ContDiff ℝ q (fderiv ℝ Φ) :=
        ContDiff.fderiv_right (m := (q : WithTop ℕ∞)) hΦ (by norm_cast)
      exact hf.clm_apply contDiff_const
    have key : ∀ t₀ : ℝ, t₀ ∈ Set.Icc (0 : ℝ) 1 →
        ‖fderiv ℝ (fdiffs q (Fin.tail h) Φ) (η + t₀ • h 0) (h 0)‖ ≤
          (∏ i : Fin q, ‖Fin.tail h i‖) * (‖h 0‖ * M) := by
      intro t₀ ht₀
      rw [fderiv_fdiffs q (Fin.tail h) hdiff]
      refine ih hΦ1 (η + t₀ • h 0) (Fin.tail h) (‖h 0‖ * M) (fun t ht => ?_)
      refine (norm_iteratedFDeriv_fderiv_apply_le hΦ _ _).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      have := hM (Fin.cons t₀ t) (fun i => by
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa using ht₀
        · simpa using ht j)
      convert this using 3
      rw [Fin.sum_univ_succ]
      simp [Fin.tail, add_assoc]
    have := norm_fdiff_le_of_segment hΨ η (h 0) key
    calc ‖fdiff (h 0) (fdiffs q (Fin.tail h) Φ) η‖
        ≤ (∏ i : Fin q, ‖Fin.tail h i‖) * (‖h 0‖ * M) := this
      _ = (∏ i : Fin (q + 1), ‖h i‖) * M := by
        rw [Fin.prod_univ_succ]
        simp only [Fin.tail]
        ring

end

section
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V]
  [NormedSpace ℝ V]

omit [NormedSpace ℝ E] in
/-- Reflection of the increments turns the output-based difference into the input-based one:
`δ_{a₁}⋯δ_{a_q}Φ (ξ) = (−1)^q Δ_{a₁}⋯Δ_{a_q}Φ (ξ − Σ a_i)`. -/
theorem fdiffs_neg (q : ℕ) (Φ : E → V) :
    ∀ (a : Fin q → E) (ξ : E),
      fdiffs q (fun i => -a i) Φ ξ = ((-1 : ℝ) ^ q) • fdiffs q a Φ (ξ - ∑ i, a i) := by
  induction q with
  | zero => intro a ξ; simp
  | succ q ih =>
    intro a ξ
    rw [fdiffs_succ, fdiffs_succ]
    have e1 : (Fin.tail fun i => -a i) = fun i => -(Fin.tail a i) := rfl
    simp only [fdiff, e1, ih (Fin.tail a)]
    rw [Fin.sum_univ_succ]
    have h1 : ξ - (a 0 + ∑ i : Fin q, a i.succ) + a 0 = ξ - ∑ i : Fin q, Fin.tail a i := by
      simp only [Fin.tail]; abel
    have h2 : ξ + -a 0 - ∑ i : Fin q, Fin.tail a i = ξ - (a 0 + ∑ i : Fin q, a i.succ) := by
      simp only [Fin.tail]; abel
    rw [h1, h2, pow_succ]
    generalize fdiffs q (Fin.tail a) Φ (ξ - (a 0 + ∑ i : Fin q, a i.succ)) = X
    generalize fdiffs q (Fin.tail a) Φ (ξ - ∑ i : Fin q, Fin.tail a i) = Y
    module

omit [NormedSpace ℝ E] in
/-- Finite differences commute with continuous additive maps. -/
theorem fdiffs_map {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] (L : V →L[ℝ] W) (q : ℕ) :
    ∀ (h : Fin q → E) (Φ : E → V) (ξ : E), fdiffs q h (fun x => L (Φ x)) ξ = L (fdiffs q h Φ ξ) := by
  induction q with
  | zero => intro h Φ ξ; simp
  | succ q ih =>
    intro h Φ ξ
    simp only [fdiffs_succ, fdiff, ih, map_sub]

end

end Hormander.B
