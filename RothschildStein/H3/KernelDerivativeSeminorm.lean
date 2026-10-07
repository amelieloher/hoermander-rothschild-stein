-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.SphereMaximum
public import RothschildStein.H1.LocalFinitePartialPairing
public import Mathlib.Data.Finset.Lattice.Fold

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace RothschildStein.H3
variable {N : ℕ} {G : HomogeneousGroup N}

/-- Finite encoding of all Euclidean multiindices of total order at
most k, with every coordinate in Fin(k+1) (BB Definition 8.13, p. 346). -/
abbrev KernelPartialIndex (N k : ℕ) :=
  {a : Fin N → Fin (k + 1) // (∑ j, (a j).val) ≤ k}

instance kernelPartialIndexNonempty (N k : ℕ) : Nonempty (KernelPartialIndex N k) :=
  ⟨⟨fun _ => 0, by simp⟩⟩

/-- The actual finite maximum Λ_{T,k} over Euclidean derivatives
through order k on the gauge unit sphere (BB p. 346). -/
def kernelDerivativeBound (ν T : (Fin N → ℝ) → ℝ) (k : ℕ) : ℝ :=
  (Finset.univ : Finset (KernelPartialIndex N k)).sup' Finset.univ_nonempty
    (fun a => kernelSphereBound ν (euclideanPartial (fun j => (a.val j).val) T))

/-- All Euclidean partial derivatives of a punctured smooth kernel
remain punctured smooth; the differentiability order is explicitly C∞. -/
theorem euclideanPartial_punctured_smooth {T : (Fin N → ℝ) → ℝ}
    (hT : ContDiffOn ℝ (⊤ : ℕ∞) T {0}ᶜ) (a : Fin N → ℕ) :
    ContDiffOn ℝ (⊤ : ℕ∞) (euclideanPartial a T) {0}ᶜ := by
  apply contDiffOn_infty.mpr
  intro k
  exact H1.contDiffOn_euclideanPartial_finite ⟨{0}ᶜ, isOpen_compl_singleton⟩
    a k T (hT.of_le (by simp))

/-- Every raw natural multiindex of order at most k is represented
in the finite family defining Λ_{T,k}, with no omitted derivatives. -/
theorem kernelSphereBound_partial_le {ν T : (Fin N → ℝ) → ℝ}
    (a : Fin N → ℕ) {k : ℕ} (ha : (∑ j, a j) ≤ k) :
    kernelSphereBound ν (euclideanPartial a T) ≤ kernelDerivativeBound ν T k := by
  have hcoord (j : Fin N) : a j ≤ k :=
    (Finset.single_le_sum (fun i _ => Nat.zero_le (a i)) (Finset.mem_univ j)).trans ha
  let b : KernelPartialIndex N k :=
    ⟨fun j => ⟨a j, Nat.lt_succ_of_le (hcoord j)⟩, ha⟩
  exact Finset.le_sup' (s := Finset.univ)
    (f := fun a => kernelSphereBound ν (euclideanPartial (fun j => (a.val j).val) T))
    (Finset.mem_univ b)

/-- The finite derivative maximum is nonnegative and bounds every
partial derivative through the specified order on the unit sphere. -/
theorem kernelDerivativeBound_properties {ν T : (Fin N → ℝ) → ℝ}
    (hν : G.IsHomogeneousGauge ν) (hT : ContDiffOn ℝ (⊤ : ℕ∞) T {0}ᶜ) (k : ℕ) :
    0 ≤ kernelDerivativeBound ν T k ∧
      ∀ a : Fin N → ℕ, (∑ j, a j) ≤ k →
        ∀ x, ν x = 1 → |euclideanPartial a T x| ≤ kernelDerivativeBound ν T k := by
  have hp (a : Fin N → ℕ) :=
    kernelSphereBound_continuous hν (euclideanPartial_punctured_smooth hT a).continuousOn
  refine ⟨(hp (fun _ => 0)).1.trans (kernelSphereBound_partial_le (fun _ => 0) (by simp)), ?_⟩
  intro a ha x hx
  exact ((hp a).2.2 x hx).trans (kernelSphereBound_partial_le a ha)

end RothschildStein.H3
