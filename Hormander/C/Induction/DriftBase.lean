-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.C.Induction.Duality

@[expose] public section

noncomputable section
open MeasureTheory SchwartzMap
open scoped ComplexConjugate
namespace Hormander.C
open Hormander.B
variable {N : ℕ}

/-- The fixed data of the drift step: diffusion fields, coefficient, the vector field `Y`, and `α`. -/
structure DriftData (N k : ℕ) where
  X : Fin (k + 1) → RealSchwartzVectorField N
  c : SchwartzMap (Carrier N) ℝ
  Y : RealSchwartzVectorField N
  α : ℝ

namespace DriftData
variable {k : ℕ} (D : DriftData N k)

def L : Operator N := diffusionOperator D.X D.c
def V (j : Fin (k + 1)) : Operator N := vectorFieldOperator (D.X j)
def W : Operator N := vectorFieldOperator D.Y

/-- The quantity `S(u) = ‖Lu‖₂ + ‖u‖₂ + ‖Yu‖_{4α-1} + ∑ᵢ ‖Xᵢu‖₂`. -/
def S (u : TestFunction N) : ℝ :=
  sobolevNorm 0 (D.L u) + sobolevNorm 0 u + sobolevNorm (4 * D.α - 1) (D.W u) +
    ∑ i : Fin k, sobolevNorm 0 (D.V i.succ u)

theorem S_nonneg (u : TestFunction N) : 0 ≤ D.S u := by
  unfold S
  have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => sobolevNorm_nonneg 0 (D.V (i : Fin k).succ u))
  have := sobolevNorm_nonneg 0 (D.L u)
  have := sobolevNorm_nonneg 0 u
  have := sobolevNorm_nonneg (4 * D.α - 1) (D.W u)
  linarith

theorem a_le_S (u : TestFunction N) : sobolevNorm 0 (D.L u) ≤ D.S u := by
  unfold S
  have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => sobolevNorm_nonneg 0 (D.V (i : Fin k).succ u))
  have := sobolevNorm_nonneg 0 u
  have := sobolevNorm_nonneg (4 * D.α - 1) (D.W u)
  linarith

theorem n_le_S (u : TestFunction N) : sobolevNorm 0 u ≤ D.S u := by
  unfold S
  have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => sobolevNorm_nonneg 0 (D.V (i : Fin k).succ u))
  have := sobolevNorm_nonneg 0 (D.L u)
  have := sobolevNorm_nonneg (4 * D.α - 1) (D.W u)
  linarith

theorem w_le_S (u : TestFunction N) : sobolevNorm (4 * D.α - 1) (D.W u) ≤ D.S u := by
  unfold S
  have := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => sobolevNorm_nonneg 0 (D.V (i : Fin k).succ u))
  have := sobolevNorm_nonneg 0 (D.L u)
  have := sobolevNorm_nonneg 0 u
  linarith

theorem e_le_S (i : Fin k) (u : TestFunction N) : sobolevNorm 0 (D.V i.succ u) ≤ D.S u := by
  unfold S
  have h := Finset.single_le_sum (f := fun i : Fin k => sobolevNorm 0 (D.V i.succ u))
    (fun j _ => sobolevNorm_nonneg _ _) (Finset.mem_univ i)
  have := sobolevNorm_nonneg 0 (D.L u)
  have := sobolevNorm_nonneg 0 u
  have := sobolevNorm_nonneg (4 * D.α - 1) (D.W u)
  linarith

/-- `‖Yu‖_{2α-1} ≤ ‖Yu‖_{4α-1}` for `α ≥ 0`. -/
theorem wτ_le_S (hα : 0 ≤ D.α) (u : TestFunction N) : sobolevNorm (2 * D.α - 1) (D.W u) ≤ D.S u :=
  (sobolevNorm_mono (by linarith) _).trans (D.w_le_S u)

end DriftData

/-- A function of `u` bounded by `K S(u)²`. -/
def SBound {k : ℕ} (D : DriftData N k) (t : TestFunction N → ℂ) : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ u, ‖t u‖ ≤ K * D.S u ^ 2

namespace SBound
variable {k : ℕ} {D : DriftData N k}

theorem of_le {t : TestFunction N → ℂ} {K : ℝ} (hK : 0 ≤ K) (h : ∀ u, ‖t u‖ ≤ K * D.S u ^ 2) :
    SBound D t := ⟨K, hK, h⟩

theorem add {t s : TestFunction N → ℂ} (ht : SBound D t) (hs : SBound D s) :
    SBound D (fun u => t u + s u) := by
  obtain ⟨K, hK, h⟩ := ht
  obtain ⟨K', hK', h'⟩ := hs
  exact ⟨K + K', add_nonneg hK hK', fun u => (norm_add_le _ _).trans (by
    have := h u; have := h' u; nlinarith)⟩

theorem sub {t s : TestFunction N → ℂ} (ht : SBound D t) (hs : SBound D s) :
    SBound D (fun u => t u - s u) := by
  obtain ⟨K, hK, h⟩ := ht
  obtain ⟨K', hK', h'⟩ := hs
  exact ⟨K + K', add_nonneg hK hK', fun u => (norm_sub_le _ _).trans (by
    have := h u; have := h' u; nlinarith)⟩

theorem neg {t : TestFunction N → ℂ} (ht : SBound D t) : SBound D (fun u => -t u) := by
  obtain ⟨K, hK, h⟩ := ht
  exact ⟨K, hK, fun u => by rw [norm_neg]; exact h u⟩

theorem sum {t : Fin k → TestFunction N → ℂ} (ht : ∀ i, SBound D (t i)) :
    SBound D (fun u => ∑ i, t i u) := by
  choose K hK h using ht
  refine ⟨∑ i, K i, Finset.sum_nonneg fun i _ => hK i, fun u => ?_⟩
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun i _ => h i u

end SBound

end Hormander.C
