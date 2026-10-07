-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.ContinuityPositive

/-!
# Regular remainders and the regularity budget

* Regularity budget: a type-`λ` kernel has a decomposition into principal terms of every regularity
  budget `m`; budget `m ≥ 1` gives a remainder that is jointly `C¹` with compact support in
  `V × V`, which is all the continuity proof uses (`TypeOperator.exists_decomposition_budget`,
  `IsRegularKernel.mono`). The passage from weighted to ordinary derivatives (triangular bracket
  basis, BB p. 569) is built into the ordinary-regularity convention of the type calculus (`IsRegularKernel`).
* Regular part: a regular kernel (`C¹`, compact support in `V × V`) is a `PatchKernel` on a
  lifted chart frame: it is bounded, and Lipschitz for the lifted control distance `d̃` in each
  variable (weighted Lagrange inequality, G1 mean value: `exists_lipschitz`; distant pairs by the
  sup bound), hence satisfies the kernel bounds of exponent one on the compact patch. It therefore
  maps `L^p → L^p` (Schur, `1 ≤ p < ∞`) and `L^∞ → C^α` for every `0 < α < 1`.

(BB pp. 566–576, Thm 11.29.)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace RothschildStein.P1

/-- A regular remainder of a larger budget is a regular remainder of
every smaller budget. -/
theorem IsRegularKernel.mono {N : ℕ} {F : KernelFrame N} {m m' : ℕ}
    {r : (Fin N → ℝ) → (Fin N → ℝ) → ℝ} (h : IsRegularKernel F m r) (hm : m' ≤ m) :
    IsRegularKernel F m' r :=
  ⟨h.1.of_le (by exact_mod_cast hm), h.2.1, h.2.2⟩

/-- **Choice of the decomposition**: a type-`λ` operator has, for every
budget `m ≥ 1`, a decomposition into principal terms whose regular remainder is jointly `C¹` with compact support
in `V × V` (the ordinary regularity needed for the Lipschitz estimate of the regular part; budgets
beyond `1` are needed only for continuity on derivative spaces). -/
theorem TypeOperator.exists_decomposition_budget {N : ℕ} {F : KernelFrame N} {lam : ℕ}
    (T : TypeOperator F lam) {m : ℕ} (hm : 1 ≤ m) :
    ∃ d : TypeDecomposition F lam m T.kernel, IsRegularKernel F 1 d.regular := by
  obtain ⟨d⟩ := T.isType m
  exact ⟨d, d.regular_isRegular.mono hm⟩

namespace IsRegularKernel

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {F : KernelFrame (n + m)}
  {r : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ}

/-- **Bounds of a regular kernel**: a jointly `C¹` kernel is bounded and
`d̃`-Lipschitz in each variable on a compact `L ⊆ U` (G1 mean value, `exists_lipschitz`; distant pairs
by the sup bound), hence has the kernel bounds of exponent one there. -/
theorem hasKernelBounds (hr : IsRegularKernel F 1 r)
    {L : Set (Fin (n + m) → ℝ)} (hL : IsCompact L) (hLU : L ⊆ C.U) :
    C.HasKernelBounds L 1 r := by
  have hG : ContDiffOn ℝ 1 (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => r p.1 p.2)
      (C.U ×ˢ C.U) := (by exact_mod_cast hr.1 : ContDiff ℝ 1 _).contDiffOn
  obtain ⟨M₀, hM₀, hb⟩ := C.exists_bound_prod hG hL hLU
  obtain ⟨M, hM0, hl₁, hl₂⟩ := C.exists_lipschitz hG hL hLU
  exact LiftedChart.hasKernelBounds_one_of_bounded_lipschitz hL hLU hM₀ hM0 hb hl₁ hl₂

/-- **A regular kernel is a patch kernel** (on `S = cl V`, `V ⋐ U`): it is
continuous (so its cut is measurable), vanishes off `V × V` (compact support in `V × V`) and has
the kernel bounds of exponent one. -/
theorem patchKernel (hF : C.IsLiftedFrame F) (hr : IsRegularKernel F 1 r) :
    C.PatchKernel (closure (F.V : Set (Fin (n + m) → ℝ))) (F.V : Set (Fin (n + m) → ℝ)) r := by
  refine ⟨hF.isCompact_closure, hF.closure_subset, subset_closure, F.V.isOpen.measurableSet,
    hr.hasKernelBounds hF.isCompact_closure hF.closure_subset,
    measurable_sliceKernel_of_continuousOn hF.isCompact_closure.measurableSet
      (hr.1.continuous.continuousOn), fun ξ η _ hout => ?_⟩
  refine image_eq_zero_of_notMem_tsupport (f := fun z : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) =>
    r z.1 z.2) (x := (ξ, η)) fun hmem => ?_
  have := hr.2.2 hmem
  rcases hout with h | h
  · exact h this.1
  · exact h this.2

end IsRegularKernel

end RothschildStein.P1
