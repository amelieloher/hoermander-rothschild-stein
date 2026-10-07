-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.ContinuityRegular

/-!
# Continuity of every positive-type operator

Assembly of the positive-type continuity theorem for a type-`λ` operator `T`, `λ ≥ 1` (BB pp. 566–576,
Thm 11.29): choose a decomposition of budget `1`; the finitely many
principal terms have `deg D ≤ 2 - λ ≤ 1` (the positive homogeneous part) and the remainder is a
regular kernel (the regular part); each is a `PatchKernel`, so their sum is, and `T` has the
kernel's off-diagonal values. On a lifted chart frame:

* `‖T f‖_{L^p(V)} ≤ Λ ‖f‖_{L^p(V)}` for `1 ≤ p < ∞`, on `L^p(V)` (hence on tests), `Λ` independent of
  `p` and `f` (`TypeOperator.exists_lp_bound`);
* `‖T f‖_{C^α(V)} ≤ CH ‖f‖_{C^α(V)}` for `0 < α < 1`, in `holderENorm` with the lifted
  control distance; in fact `‖T f‖_{C^α(V)} ≤ CH sup_V |f|` (`TypeOperator.exists_holderENorm_bound`);
* the operator `T f` is the absolutely convergent integral, and vanishes off `V` (support control).

The assertions about the type-0 singular part, the reconstruction and the agreement of the `L^p`
extension with the pointwise realization on `C^α` are not part of this module (they concern `λ = 0`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace RothschildStein.P1

/-- At positive type the action of `T` is the integral `∫ k(ξ, η) f(η) dη`. -/
theorem TypeOperator.apply_eq_integral {N : ℕ} {F : KernelFrame N} {lam : ℕ} (hlam : lam ≠ 0)
    (T : TypeOperator F lam) (f : (Fin N → ℝ) → ℝ) :
    T.apply f = fun ξ => ∫ η, T.kernel ξ η * f η := by
  funext ξ
  simp [TypeOperator.apply, hlam]

namespace TypeOperator

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {F : KernelFrame (n + m)} {lam : ℕ}
  (hF : C.IsLiftedFrame F) (hlam : 1 ≤ lam) (T : TypeOperator F lam)
include hF hlam

/-- **The kernel of a positive-type operator is a patch kernel** (on `S = cl V`): the budget-one
decomposition is a finite sum of positive principal terms
and a regular remainder, which agrees
with `T.kernel` off the diagonal. -/
theorem patchKernel :
    C.PatchKernel (closure (F.V : Set (Fin (n + m) → ℝ))) (F.V : Set (Fin (n + m) → ℝ))
      T.kernel := by
  obtain ⟨d, hd⟩ := T.exists_decomposition_budget (m := 1) le_rfl
  have hprin : ∀ t ∈ d.principal,
      C.PatchKernel (closure (F.V : Set (Fin (n + m) → ℝ))) (F.V : Set (Fin (n + m) → ℝ))
        t.kernel := fun t ht =>
    PrincipalTerm.patchKernel hF t (by have := d.principal_degree t ht; omega)
  have hsum := LiftedChart.PatchKernel.list_sum hF.isCompact_closure hF.closure_subset subset_closure
    F.V.isOpen.measurableSet d.principal (κι := fun t => t.kernel) hprin
  exact (hsum.add (hd.patchKernel hF)).congr_off_diagonal
    (fun ξ η hne => (d.eq_off_diagonal ξ η hne).symm)

/-- **Absolute convergence at positive type**: for `f` measurable and bounded on `V` every row
`η ↦ k(ξ, η) f(η)` is Lebesgue integrable, so `T f(ξ)` is the absolutely convergent integral
`∫ k(ξ, η) f(η) dη` (the Bochner integral is not the junk value `0`). -/
theorem integrable_row {f : (Fin (n + m) → ℝ) → ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict (F.V : Set (Fin (n + m) → ℝ)))) {M : ℝ}
    (hM0 : 0 ≤ M) (hM : ∀ y ∈ (F.V : Set (Fin (n + m) → ℝ)), |f y| ≤ M)
    (ξ : Fin (n + m) → ℝ) : Integrable (fun η => T.kernel ξ η * f η) :=
  (patchKernel hF hlam T).integrable_row hf hM0 hM ξ

/-- **`L^∞` bound**: `|T f| ≤ Cs sup_V |f|` everywhere. -/
theorem exists_sup_bound :
    ∃ Cs : ℝ, 0 < Cs ∧ ∀ (f : (Fin (n + m) → ℝ) → ℝ) (M : ℝ), 0 ≤ M →
      (∀ y ∈ (F.V : Set (Fin (n + m) → ℝ)), |f y| ≤ M) → ∀ x, |T.apply f x| ≤ Cs * M := by
  obtain ⟨Cs, hCs, h⟩ := (patchKernel hF hlam T).exists_sup_bound
  refine ⟨Cs, hCs, fun f M hM0 hM x => ?_⟩
  rw [T.apply_eq_integral (by omega)]
  exact h f M hM0 hM x

/-- **`L^∞ → C^α` for positive type** (BB pp. 566–576, Thm 11.29): for `0 < α < 1` there is
`CH` with `‖T f‖_{C^α(V)} ≤ CH sup_V |f|` for every `f` measurable on `V`, in `holderENorm`
with the lifted control distance `d̃`. -/
theorem exists_holderENorm_bound {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ CH : ℝ, 0 < CH ∧ ∀ f : (Fin (n + m) → ℝ) → ℝ,
      AEStronglyMeasurable f (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) →
        holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) (T.apply f) ≤
          ENNReal.ofReal CH * ⨆ x : (F.V : Set (Fin (n + m) → ℝ)), ENNReal.ofReal |f x| := by
  obtain ⟨CH, hCH, h⟩ := (patchKernel hF hlam T).exists_holderENorm_bound hα0 hα1
  refine ⟨CH, hCH, fun f hf => ?_⟩
  rw [T.apply_eq_integral (by omega)]
  exact h f hf

end TypeOperator

end RothschildStein.P1
