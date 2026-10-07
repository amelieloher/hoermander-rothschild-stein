-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.B.Defs
public import Hormander.B.Mollifier.CutoffAlgebra
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Topology.Algebra.Support

@[expose] public section

noncomputable section

open SchwartzMap
open Hormander.B

namespace Hormander.C

/-- Schwartz coordinate fields associated to compactly supported smooth vector fields. -/
def c9SchwartzVectorField {k N : ℕ}
    (X : Fin (k + 1) → Carrier N → Carrier N)
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (hXc : ∀ i, HasCompactSupport (X i)) :
    Fin (k + 1) → RealSchwartzVectorField N := fun i j => by
  have hcoordSupport : Function.support (fun x => X i x j) ⊆ tsupport (X i) := by
    intro x hx
    have hnonzero : X i x j ≠ 0 := by simpa using hx
    apply subset_tsupport
    intro hzero
    apply hnonzero
    simp [hzero]
  have hcoordCompact : HasCompactSupport (fun x => X i x j) := (hXc i).mono' hcoordSupport
  have hcoordSmooth : ContDiff ℝ (⊤ : ℕ∞) (fun x => X i x j) :=
    (EuclideanSpace.proj (𝕜 := ℝ) j).contDiff.comp (hX i)
  exact hcoordCompact.toSchwartzMap hcoordSmooth

@[simp]
theorem c9SchwartzVectorField_apply {k N : ℕ}
    (X : Fin (k + 1) → Carrier N → Carrier N)
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (hXc : ∀ i, HasCompactSupport (X i))
    (i : Fin (k + 1)) (j : Fin N) (x : Carrier N) :
    c9SchwartzVectorField X hX hXc i j x = X i x j := rfl

/-- The real Schwartz representative of a compactly supported smooth coefficient. -/
def c9SchwartzMultiplier {N : ℕ} (c : Carrier N → ℝ)
    (hc : ContDiff ℝ (⊤ : ℕ∞) c) (hcc : HasCompactSupport c) :
    SchwartzMap (Carrier N) ℝ := hcc.toSchwartzMap hc

@[simp]
theorem c9SchwartzMultiplier_apply {N : ℕ} (c : Carrier N → ℝ)
    (hc : ContDiff ℝ (⊤ : ℕ∞) c) (hcc : HasCompactSupport c) (x : Carrier N) :
    c9SchwartzMultiplier c hc hcc x = c x := rfl

end Hormander.C

end
