-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.RepresentationHigher

/-!
# First-order representation without drift: `X̃_l(a u) = F_l L̃u + S_l u`

Without drift (alphabet `Fin k`, all weights one, `L̃ = sumSquares Xt = ∑ᵢ X̃ᵢ²`): differentiate
`a u = P₂ L̃u + F₂ u` (the second identity of the signed parametrix, `SignedParametrixNoDrift`); by left differentiation
(`LeftDifferentiation`, BB pp. 546–551) `X̃_l P₂` has type 1 and `X̃_l F₂` has type 0, an endpoint operator (a single
term `X̃_l F₂`). With `F_l = X̃_l P₂` and `S_l = X̃_l F₂` this is the first representation identity (BB p. 564,
Thm 11.26, (11.41)) without drift. Derivatives are weak derivatives on `V` (`hasWeakWordDeriv`).
This is the no-drift counterpart of `representation_firstOrder_of`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped Topology
namespace RothschildStein.P1

variable {N k : ℕ} {F : KernelFrame N} {w : Fin k → ℕ+}
  {Xt : Fin k → (Fin N → ℝ) → (Fin N → ℝ)}

/-- The weak `X̃_l`-derivative of `a u`, from `a u = P₂ L̃u + F₂ u` on `V`
(no drift, alphabet `Fin k`): if `X̃_l (P₂ g) = Fl g` and `X̃_l (F₂ g) = Sl g` weakly for tests `g`,
then `X̃_l (a u) = Fl (L̃u) + Sl u` (generic in the operator `L̃ = Lt`, which maps tests to
tests). -/
theorem rep_firstOrder_weak_noDrift
    (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Xt i) (F.V : Set (Fin N → ℝ)))
    {Lt : ((Fin N → ℝ) → ℝ) → (Fin N → ℝ) → ℝ}
    (Lap : TestFunction F.V ℝ (⊤ : ℕ∞) → TestFunction F.V ℝ (⊤ : ℕ∞))
    (hLap : ∀ u, (Lap u : (Fin N → ℝ) → ℝ) = Lt u) {a : TestFunction F.V ℝ (⊤ : ℕ∞)}
    {P₂ : TypeOperator F 2} {F₂ : TypeOperator F 1}
    (hzero : ∀ f : TestFunction F.V ℝ (⊤ : ℕ∞), ∀ ξ ∈ (F.V : Set (Fin N → ℝ)),
      a ξ * f ξ = P₂.apply (Lt f) ξ + F₂.apply f ξ)
    {l : Fin k} {Fl : TypeOperator F 1} {Sl : TypeOperator F 0}
    (hFl : ∀ g : TestFunction F.V ℝ (⊤ : ℕ∞), hasWeakWordDeriv Xt F.V [l] (P₂.apply g) (Fl.apply g))
    (hSl : ∀ g : TestFunction F.V ℝ (⊤ : ℕ∞), hasWeakWordDeriv Xt F.V [l] (F₂.apply g) (Sl.apply g))
    (u : TestFunction F.V ℝ (⊤ : ℕ∞)) :
    hasWeakWordDeriv Xt F.V [l] (fun x => a x * u x)
      (fun ξ => Fl.apply (Lt u) ξ + Sl.apply u ξ) := by
  have h1 := hFl (Lap u)
  rw [hLap] at h1
  exact repWeak_congr (S.hasWeakWordDeriv_add Xt F.V hXt h1 (hSl u))
    (fun x hx => (hzero u x hx).symm) (fun x _ => rfl)

/-- First-order representation without drift: for `a ∈ C_c^∞(V)` (with `b = 1` near its
support), `SignedParametrixNoDrift` and left differentiation (`LeftDifferentiation`) there are type-1 `F_l` and type-0
endpoint operators `S_l` (`S_l = X̃_l F₂`, a single term) with `X̃_l(a u) = F_l L̃u + S_l u` for every
test `u` and every generator `l` (weak derivative on `V`, `L̃ = sumSquares`; BB p. 564, Thm 11.26,
(11.41), without drift). The density data `c` are the standing hypotheses of
`SignedParametrixNoDrift`. -/
theorem representation_firstOrder_noDrift_of
    (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Xt i) (F.V : Set (Fin N → ℝ)))
    (hw : ∀ j, (w j : ℕ) = 1) (hLeftDiff : LeftDifferentiation F w Xt)
    {c : (Fin N → ℝ) → ℝ} (hc : ContDiffOn ℝ (⊤ : ℕ∞) c (F.V : Set (Fin N → ℝ)))
    (hc0 : ∀ ξ ∈ (F.V : Set (Fin N → ℝ)), 0 < c ξ) (a : TestFunction F.V ℝ (⊤ : ℕ∞))
    (hParametrix : ∀ b : TestFunction F.V ℝ (⊤ : ℕ∞), SignedParametrixNoDrift F Xt c a b) :
    ∃ (Fl : Fin k → TypeOperator F 1) (Sl : Fin k → TypeOperator F 0),
      (∀ l, IsEndpoint F Xt (Sl l)) ∧
      ∀ (l : Fin k) (u : TestFunction F.V ℝ (⊤ : ℕ∞)),
        hasWeakWordDeriv Xt F.V [l] (fun x => a x * u x)
          (fun ξ => (Fl l).apply (sumSquares Xt u) ξ + (Sl l).apply u ξ) := by
  obtain ⟨P₂, F₂, hzero⟩ := exists_zeroth_rep hc hc0 a hParametrix
  choose Fl hFl using fun l : Fin k =>
    exists_leftOp_of_eq (lam' := 1) hLeftDiff P₂ l (by have := hw l; omega) (by have := hw l; omega)
  choose Sl hSl using fun l : Fin k =>
    exists_leftOp_of_eq (lam' := 0) hLeftDiff F₂ l (by have := hw l; omega) (by have := hw l; omega)
  exact ⟨Fl, Sl, fun l => IsEndpoint.of_weakDeriv (hSl l), fun l u =>
    rep_firstOrder_weak_noDrift hXt (repSumSquaresTest F Xt hXt)
      (fun u => coe_repSumSquaresTest hXt u) hzero (hFl l) (hSl l) u⟩

end RothschildStein.P1
