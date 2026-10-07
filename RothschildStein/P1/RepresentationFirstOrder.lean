-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.RepresentationBasic
public import RothschildStein.P1.LeftParametrixAlgebra

/-!
# First-order representation: `X̃_l(a u) = F_l L̃u + S_l u`

Differentiate `a u = P₂ L̃u + F₂ u` (the second identity of the signed parametrix, `SignedParametrix`): by left
differentiation (`LeftDifferentiation`, BB pp. 546–551) `X̃_l P₂` has type 1 and `X̃_l F₂` has type 0, an endpoint
operator (a single term `X̃_l F₂`). With `F_l = X̃_l P₂` and `S_l = X̃_l F₂` this is the first
representation identity (BB p. 564, Thm 11.26, (11.41)). Derivatives are weak derivatives on `V`
(`hasWeakWordDeriv`); `L̃ = sumSquaresWithDrift`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped Topology
namespace RothschildStein.P1

variable {N q : ℕ} {F : KernelFrame N} {w : Fin (q + 1) → ℕ+}
  {Xt : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ)}

/-- The weak `X̃_l`-derivative of `a u`, from `a u = P₂ L̃u + F₂ u` on `V`:
if `X̃_l (P₂ g) = Fl g` and `X̃_l (F₂ g) = Sl g` weakly for tests `g`, then
`X̃_l (a u) = Fl (L̃u) + Sl u` (generic in the operator `L̃ = Lt`, which maps tests to tests). -/
theorem rep_firstOrder_weak (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Xt i) (F.V : Set (Fin N → ℝ)))
    {Lt : ((Fin N → ℝ) → ℝ) → (Fin N → ℝ) → ℝ}
    (Lap : TestFunction F.V ℝ (⊤ : ℕ∞) → TestFunction F.V ℝ (⊤ : ℕ∞))
    (hLap : ∀ u, (Lap u : (Fin N → ℝ) → ℝ) = Lt u) {a : TestFunction F.V ℝ (⊤ : ℕ∞)}
    {P₂ : TypeOperator F 2} {F₂ : TypeOperator F 1}
    (hzero : ∀ f : TestFunction F.V ℝ (⊤ : ℕ∞), ∀ ξ ∈ (F.V : Set (Fin N → ℝ)),
      a ξ * f ξ = P₂.apply (Lt f) ξ + F₂.apply f ξ)
    {l : Fin (q + 1)} {Fl : TypeOperator F 1} {Sl : TypeOperator F 0}
    (hFl : ∀ g : TestFunction F.V ℝ (⊤ : ℕ∞), hasWeakWordDeriv Xt F.V [l] (P₂.apply g) (Fl.apply g))
    (hSl : ∀ g : TestFunction F.V ℝ (⊤ : ℕ∞), hasWeakWordDeriv Xt F.V [l] (F₂.apply g) (Sl.apply g))
    (u : TestFunction F.V ℝ (⊤ : ℕ∞)) :
    hasWeakWordDeriv Xt F.V [l] (fun x => a x * u x)
      (fun ξ => Fl.apply (Lt u) ξ + Sl.apply u ξ) := by
  have h1 := hFl (Lap u)
  rw [hLap] at h1
  exact repWeak_congr (S.hasWeakWordDeriv_add Xt F.V hXt h1 (hSl u))
    (fun x hx => (hzero u x hx).symm) (fun x _ => rfl)

/-- First-order representation: for `a ∈ C_c^∞(V)` (with `b = 1` near its support), `SignedParametrix`
and left differentiation (`LeftDifferentiation`) there are type-1 `F_l` and type-0 endpoint operators `S_l`
(`S_l = X̃_l F₂`, a single term) with `X̃_l(a u) = F_l L̃u + S_l u` for every test `u` and horizontal
`l ≥ 1` (weak derivative on `V`; BB p. 564, Thm 11.26, (11.41)). The density data `c` are the
standing hypotheses of `SignedParametrix`. -/
theorem representation_firstOrder_of
    (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Xt i) (F.V : Set (Fin N → ℝ)))
    (hw : ∀ j : Fin q, (w j.succ : ℕ) = 1) (hLeftDiff : LeftDifferentiation F w Xt)
    {c : (Fin N → ℝ) → ℝ} (hc : ContDiffOn ℝ (⊤ : ℕ∞) c (F.V : Set (Fin N → ℝ)))
    (hc0 : ∀ ξ ∈ (F.V : Set (Fin N → ℝ)), 0 < c ξ) (a : TestFunction F.V ℝ (⊤ : ℕ∞))
    (hParametrix : ∀ b : TestFunction F.V ℝ (⊤ : ℕ∞), SignedParametrix F Xt c a b) :
    ∃ (Fl : Fin q → TypeOperator F 1) (Sl : Fin q → TypeOperator F 0),
      (∀ l, IsEndpoint F Xt (Sl l)) ∧
      ∀ (l : Fin q) (u : TestFunction F.V ℝ (⊤ : ℕ∞)),
        hasWeakWordDeriv Xt F.V [l.succ] (fun x => a x * u x)
          (fun ξ => (Fl l).apply (sumSquaresWithDrift Xt u) ξ + (Sl l).apply u ξ) := by
  obtain ⟨P₂, F₂, hzero⟩ := exists_zeroth_rep hc hc0 a hParametrix
  choose Fl hFl using fun l : Fin q =>
    exists_leftOp_of_eq (lam' := 1) hLeftDiff P₂ l.succ (by have := hw l; omega) (by have := hw l; omega)
  choose Sl hSl using fun l : Fin q =>
    exists_leftOp_of_eq (lam' := 0) hLeftDiff F₂ l.succ (by have := hw l; omega) (by have := hw l; omega)
  exact ⟨Fl, Sl, fun l => IsEndpoint.of_weakDeriv (hSl l), fun l u =>
    rep_firstOrder_weak hXt (sumSquaresWithDriftTest F.V Xt hXt)
      (fun u => sumSquaresWithDriftTest_coe F.V Xt hXt u) hzero (hFl l) (hSl l) u⟩

end RothschildStein.P1
