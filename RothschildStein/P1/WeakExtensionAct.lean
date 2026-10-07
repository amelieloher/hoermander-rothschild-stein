-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.WeakExtensionLimit

/-!
# Weak extension: the bounded `L^P` extensions `T̄` as operators on functions

For a type-`λ` operator `T` of a standard frame (`LiftedChart.IsStandardFrame`) and `1 < P < ∞`,
The continuity theorem gives the unique bounded operator `T̄` on `L^P(V)` which agrees with the action of `T` on tests
(and, a.e., on every function of finite Hölder norm). This file names that extension and its action on
functions:

* `TypeOperator.lpExt`: `T̄ : L^P(V) →L[ℝ] L^P(V)` (`exists_lpExtension_standard`);
* `TypeOperator.lpAct`: `g ↦ T̄ g` as a function (`0` if `g ∉ L^P(V)`), with
  `lpAct_test` (agreement a.e. with `T.apply` on tests), `lpAct_holder` (agreement a.e. with the
  pointwise integral/principal value on `C^α` inputs: the identification of the continuous
  representatives) and `ConvLp.lpAct` (`T̄` preserves `L^P` convergence, by the continuity theorem).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped ENNReal Topology
namespace RothschildStein.P1

/-- The Lebesgue space `L^P(V)` of the open patch `V`. -/
abbrev LpV {N : ℕ} (V : Opens (Fin N → ℝ)) (P : ℝ≥0∞) [Fact (1 ≤ P)] : Type :=
  Lp ℝ P (volume.restrict (V : Set (Fin N → ℝ)))

namespace LiftedChart

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {F : KernelFrame (n + m)}
  {q : ℕ} {H : H1.StandingHypotheses C.G q} {K : H1.FundamentalKernel C.G H}
  {hQ : 2 < (C.G.homogeneousDimension : ℝ)} {lam : ℕ} {P : ℝ≥0∞} [Fact (1 ≤ P)]

/-- **The `L^P` extension `T̄`** (continuity theorem): a bounded operator on `L^P(V)`
which agrees a.e. with the action of `T` on every test function and on every measurable function of
finite Hölder norm. -/
theorem _root_.RothschildStein.P1.TypeOperator.exists_lpExt (hF : C.IsStandardFrame F H K hQ)
    (T : TypeOperator F lam) (hP1 : 1 < P) (hP : P ≠ ⊤) :
    ∃ Tb : LpV F.V P →L[ℝ] LpV F.V P,
      (∀ f : TestFunction F.V ℝ (⊤ : ℕ∞),
        Tb (testToLp F.V hF.lifted.volume_lt_top P f) =ᵐ[volume.restrict
          (F.V : Set (Fin (n + m) → ℝ))] T.apply f) ∧
      (∀ {α : ℝ}, 0 < α → α < 1 → ∀ f : (Fin (n + m) → ℝ) → ℝ,
        ∀ hf : holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) f ≠ ⊤,
        ∀ hfm : AEStronglyMeasurable f (volume.restrict (F.V : Set (Fin (n + m) → ℝ))),
        Tb ((memLp_of_holderENorm_ne_top F.V.isOpen.measurableSet hF.lifted.volume_lt_top hf hfm
            P).toLp f) =ᵐ[volume.restrict (F.V : Set (Fin (n + m) → ℝ))] T.apply f) := by
  obtain ⟨-, -, Tb, -, ht, hh, -⟩ := T.exists_lpExtension_standard hF hP1 hP
  exact ⟨Tb, fun f => (ht f).2, hh⟩

/-- The bounded extension `T̄ : L^P(V) → L^P(V)` of a type-`λ` operator of
a standard frame (a choice of the operator of `exists_lpExt`; it is unique by the continuity theorem). -/
def _root_.RothschildStein.P1.TypeOperator.lpExt (hF : C.IsStandardFrame F H K hQ)
    (T : TypeOperator F lam) (hP1 : 1 < P) (hP : P ≠ ⊤) : LpV F.V P →L[ℝ] LpV F.V P :=
  Classical.choose (T.exists_lpExt hF hP1 hP)

/-- The action of `T̄` on functions: `T̄ g` for `g ∈ L^P(V)`
(a representative of the class), `0` otherwise. -/
def _root_.RothschildStein.P1.TypeOperator.lpAct (hF : C.IsStandardFrame F H K hQ)
    (T : TypeOperator F lam) (hP1 : 1 < P) (hP : P ≠ ⊤) (g : (Fin (n + m) → ℝ) → ℝ) :
    (Fin (n + m) → ℝ) → ℝ :=
  actLp (T.lpExt hF hP1 hP) g

/-- `T̄` agrees a.e. with the action of `T` on tests. -/
theorem _root_.RothschildStein.P1.TypeOperator.lpAct_test (hF : C.IsStandardFrame F H K hQ)
    (T : TypeOperator F lam) (hP1 : 1 < P) (hP : P ≠ ⊤) (f : TestFunction F.V ℝ (⊤ : ℕ∞)) :
    T.lpAct hF hP1 hP (f : (Fin (n + m) → ℝ) → ℝ) =ᵐ[volume.restrict
      (F.V : Set (Fin (n + m) → ℝ))] T.apply f := by
  have h := (Classical.choose_spec (T.exists_lpExt hF hP1 hP)).1 f
  unfold TypeOperator.lpAct
  rw [actLp_eq _ (testFunction_memLp F.V hF.lifted.volume_lt_top f P)]
  exact h

/-- **Identification of the continuous representatives**:
`T̄ g` agrees a.e. with the pointwise integral/principal value `T.apply g` on every measurable
function `g` of finite Hölder norm `‖g‖_{C^α(V)}`, `0 < α < 1` (by the continuity theorem, the two realizations agree on
the intersection). -/
theorem _root_.RothschildStein.P1.TypeOperator.lpAct_holder (hF : C.IsStandardFrame F H K hQ)
    (T : TypeOperator F lam) (hP1 : 1 < P) (hP : P ≠ ⊤) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {g : (Fin (n + m) → ℝ) → ℝ}
    (hg : holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) g ≠ ⊤)
    (hgm : AEStronglyMeasurable g (volume.restrict (F.V : Set (Fin (n + m) → ℝ)))) :
    T.lpAct hF hP1 hP g =ᵐ[volume.restrict (F.V : Set (Fin (n + m) → ℝ))] T.apply g := by
  have h := (Classical.choose_spec (T.exists_lpExt hF hP1 hP)).2 hα0 hα1 g hg hgm
  unfold TypeOperator.lpAct
  rw [actLp_eq _ (memLp_of_holderENorm_ne_top F.V.isOpen.measurableSet hF.lifted.volume_lt_top hg
    hgm P)]
  exact h

/-- **`T̄` is bounded: it preserves `L^P(V)` convergence** (continuity theorem). -/
theorem _root_.RothschildStein.P1.ConvLp.lpAct (hF : C.IsStandardFrame F H K hQ)
    (T : TypeOperator F lam) (hP1 : 1 < P) (hP : P ≠ ⊤) {f : ℕ → (Fin (n + m) → ℝ) → ℝ}
    {g : (Fin (n + m) → ℝ) → ℝ} (h : ConvLp F.V P f g) :
    ConvLp F.V P (fun j => T.lpAct hF hP1 hP (f j)) (T.lpAct hF hP1 hP g) :=
  h.actLp (T.lpExt hF hP1 hP)

end LiftedChart

end RothschildStein.P1
