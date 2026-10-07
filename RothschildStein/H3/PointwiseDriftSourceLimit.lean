-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.Definitions.driftWeight
public import RothschildStein.Definitions.wordWeight
public import Mathlib.Topology.Algebra.Monoid
public import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace RothschildStein.H3

/-- The drift-plus-diagonal source equation passes to the
pointwise limits of all weight-two jets and the actual source.
The finite sum keeps every diagonal term (BB pp. 386–387). -/
theorem drift_source_eqOn_of_pointwise_jet_limits {N q : ℕ}
    (U : Set (Fin N → ℝ))
    (F : ℕ → List (Fin (q + 1)) → (Fin N → ℝ) → ℝ)
    (jet : List (Fin (q + 1)) → (Fin N → ℝ) → ℝ)
    (φ : ℕ → (Fin N → ℝ) → ℝ) (f : (Fin N → ℝ) → ℝ)
    (hjet : ∀ I, wordWeight driftWeight I ≤ 2 → ∀ x ∈ U,
      Tendsto (fun n => F n I x) atTop (𝓝 (jet I x)))
    (hf : ∀ x ∈ U, Tendsto (fun n => φ n x) atTop (𝓝 (f x)))
    (heq : ∀ n x, x ∈ U → F n [0] x + ∑ i : Fin q, F n [i.succ, i.succ] x = φ n x) :
    EqOn (fun x => jet [0] x + ∑ i : Fin q, jet [i.succ, i.succ] x) f U := by
  intro x hx
  have h0 := hjet [0] (by simp [wordWeight, driftWeight]) x hx
  have hi := tendsto_finsetSum (Finset.univ : Finset (Fin q)) (fun i _ =>
    hjet [i.succ, i.succ] (by simp [wordWeight, driftWeight]) x hx)
  exact tendsto_nhds_unique ((h0.add hi).congr (fun n => heq n x hx)) (hf x hx)

end RothschildStein.H3
