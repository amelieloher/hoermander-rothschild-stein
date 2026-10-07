-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.C.Induction.DriftBase

@[expose] public section

noncomputable section
open MeasureTheory SchwartzMap
open scoped ComplexConjugate
namespace Hormander.C
open Hormander.B
variable {N k : ℕ} {D : DriftData N k}

/-- Bounded by a constant multiple of `S`. -/
def SLe (D : DriftData N k) (f : TestFunction N → ℝ) : Prop := ∃ K : ℝ, 0 ≤ K ∧ ∀ u, f u ≤ K * D.S u

theorem SLe.of_le {f : TestFunction N → ℝ} (h : ∀ u, f u ≤ D.S u) : SLe D f :=
  ⟨1, zero_le_one, fun u => by simpa using h u⟩

theorem SBound.right (F : B10Facts N) {m : ℝ} {Sop : Operator N} (hS : OperatorClass m Sop) (s : ℝ)
    {A B : TestFunction N → TestFunction N}
    (hA : SLe D (fun u => sobolevNorm (-s) (A u))) (hB : SLe D (fun u => sobolevNorm (s + m) (B u))) :
    SBound D (fun u => hermitianPairing (A u) (Sop (B u))) := by
  obtain ⟨C, hC0, hC⟩ := F.pairing_right hS s
  obtain ⟨K1, hK1, h1⟩ := hA
  obtain ⟨K2, hK2, h2⟩ := hB
  refine ⟨C * (K2 * K1), by positivity, fun u => ?_⟩
  have hSn := D.S_nonneg u
  calc ‖hermitianPairing (A u) (Sop (B u))‖ ≤ C * (sobolevNorm (s + m) (B u) * sobolevNorm (-s) (A u)) :=
        hC _ _
    _ ≤ C * ((K2 * D.S u) * (K1 * D.S u)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul (h2 u) (h1 u) (sobolevNorm_nonneg _ _) (by positivity)) hC0
    _ = _ := by ring

theorem SBound.left (F : B10Facts N) {m : ℝ} {Sop : Operator N} (hS : OperatorClass m Sop) (s : ℝ)
    {A B : TestFunction N → TestFunction N}
    (hA : SLe D (fun u => sobolevNorm (s + m) (A u))) (hB : SLe D (fun u => sobolevNorm (-s) (B u))) :
    SBound D (fun u => hermitianPairing (Sop (A u)) (B u)) := by
  obtain ⟨C, hC0, hC⟩ := F.pairing_left hS s
  obtain ⟨K1, hK1, h1⟩ := hA
  obtain ⟨K2, hK2, h2⟩ := hB
  refine ⟨C * (K1 * K2), by positivity, fun u => ?_⟩
  have hSn := D.S_nonneg u
  calc ‖hermitianPairing (Sop (A u)) (B u)‖ ≤ C * (sobolevNorm (s + m) (A u) * sobolevNorm (-s) (B u)) :=
        hC _ _
    _ ≤ C * ((K1 * D.S u) * (K2 * D.S u)) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul (h1 u) (h2 u) (sobolevNorm_nonneg _ _) (by positivity)) hC0
    _ = _ := by ring

theorem SLe.mono {f g : TestFunction N → ℝ} (hg : SLe D g) (h : ∀ u, f u ≤ g u) : SLe D f := by
  obtain ⟨K, hK, hg⟩ := hg
  exact ⟨K, hK, fun u => (h u).trans (hg u)⟩

/-- `‖Su‖_s ≤ K S` from `‖u‖_{s'} ≤ K' S` and a class bound. -/
theorem SLe.of_order {m : ℝ} {Sop : Operator N} (h : HasOrder m Sop) (s : ℝ) {B : TestFunction N → TestFunction N}
    (hB : SLe D (fun u => sobolevNorm (s + m) (B u))) :
    SLe D (fun u => sobolevNorm s (Sop (B u))) := by
  obtain ⟨C, hC⟩ := h s
  obtain ⟨K, hK, hB⟩ := hB
  refine ⟨C * K, by positivity, fun u => ?_⟩
  calc sobolevNorm s (Sop (B u)) ≤ C * sobolevNorm (s + m) (B u) := hC _
    _ ≤ C * (K * D.S u) := mul_le_mul_of_nonneg_left (hB u) C.2
    _ = _ := by ring

/-- Right-slot pairing with index bookkeeping `p + q = m`. -/
theorem SBound.right' (F : B10Facts N) {m : ℝ} {Sop : Operator N} (hS : OperatorClass m Sop)
    (p q : ℝ) (hpq : p + q = m) {A B : TestFunction N → TestFunction N}
    (hA : SLe D (fun u => sobolevNorm p (A u))) (hB : SLe D (fun u => sobolevNorm q (B u))) :
    SBound D (fun u => hermitianPairing (A u) (Sop (B u))) := by
  refine SBound.right F hS (-p) ?_ ?_
  · simpa using hA
  · have : -p + m = q := by linarith
    rw [this]; exact hB

/-- Left-slot pairing with index bookkeeping `p + q = m`. -/
theorem SBound.left' (F : B10Facts N) {m : ℝ} {Sop : Operator N} (hS : OperatorClass m Sop)
    (p q : ℝ) (hpq : p + q = m) {A B : TestFunction N → TestFunction N}
    (hA : SLe D (fun u => sobolevNorm q (A u))) (hB : SLe D (fun u => sobolevNorm p (B u))) :
    SBound D (fun u => hermitianPairing (Sop (A u)) (B u)) := by
  refine SBound.left F hS (-p) ?_ ?_
  · have : -p + m = q := by linarith
    rw [this]; exact hA
  · simpa using hB

end Hormander.C
