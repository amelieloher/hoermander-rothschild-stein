-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.Interface.HasWeakHormanderEquation
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Topology.Algebra.Support

@[expose] public section

noncomputable section

open Function MeasureTheory Set Topology

namespace Hormander.F

private theorem tsupport_realPart_subset {N : ℕ}
    (φ : (Fin N → ℝ) → ℂ) :
    tsupport (fun x => (φ x).re) ⊆ tsupport φ := by
  change closure (support (fun x => (φ x).re)) ⊆ tsupport φ
  refine closure_minimal ?_ (isClosed_tsupport φ)
  intro x hx
  by_contra hxnot
  have hφzero : φ x = 0 := by
    have hxSupport : x ∉ support φ := fun hxs => hxnot (subset_tsupport φ hxs)
    simpa only [mem_support, not_not] using hxSupport
  exact (mem_support.mp hx) (by simp [hφzero])

private theorem tsupport_imagPart_subset {N : ℕ}
    (φ : (Fin N → ℝ) → ℂ) :
    tsupport (fun x => (φ x).im) ⊆ tsupport φ := by
  change closure (support (fun x => (φ x).im)) ⊆ tsupport φ
  refine closure_minimal ?_ (isClosed_tsupport φ)
  intro x hx
  by_contra hxnot
  have hφzero : φ x = 0 := by
    have hxSupport : x ∉ support φ := fun hxs => hxnot (subset_tsupport φ hxs)
    simpa only [mem_support, not_not] using hxSupport
  exact (mem_support.mp hx) (by simp [hφzero])

private theorem compactSupport_realPart {N : ℕ} (φ : (Fin N → ℝ) → ℂ)
    (hφ : HasCompactSupport φ) : HasCompactSupport (fun x => (φ x).re) := by
  rw [hasCompactSupport_iff_eventuallyEq] at hφ ⊢
  exact hφ.mono fun x hx => by simp [hx]

private theorem compactSupport_imagPart {N : ℕ} (φ : (Fin N → ℝ) → ℂ)
    (hφ : HasCompactSupport φ) : HasCompactSupport (fun x => (φ x).im) := by
  rw [hasCompactSupport_iff_eventuallyEq] at hφ ⊢
  exact hφ.mono fun x hx => by simp [hx]

private theorem contDiff_realPart {N : ℕ} {φ : (Fin N → ℝ) → ℂ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => (φ x).re) := by
  have h := Complex.reCLM.contDiff.comp hφ
  simpa only [Complex.reCLM_apply, Function.comp_def] using h

private theorem contDiff_imagPart {N : ℕ} {φ : (Fin N → ℝ) → ℂ}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => (φ x).im) := by
  have h := Complex.imCLM.contDiff.comp hφ
  simpa only [Complex.imCLM_apply, Function.comp_def] using h

/-- The weak identity extends to complex tests by applying it
separately to the real and imaginary parts. -/
theorem weakEquation_complexified {k N : ℕ} {Ω : Set (Fin N → ℝ)}
    (X : Fin (k + 1) → (Fin N → ℝ) → (Fin N → ℝ))
    (c g u : (Fin N → ℝ) → ℝ)
    (hEq : Hormander.Interface.HasWeakHormanderEquation Ω X c g u) :
    ∀ φ : (Fin N → ℝ) → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ x in Ω, u x * Hormander.Interface.hormanderAdjointTest X c
          (fun y => (φ y).re) x = ∫ x in Ω, g x * (φ x).re) ∧
      (∫ x in Ω, u x * Hormander.Interface.hormanderAdjointTest X c
          (fun y => (φ y).im) x = ∫ x in Ω, g x * (φ x).im) := by
  rcases hEq with ⟨hu, hg, hweak⟩
  intro φ hφ hcompact hsupport
  have hrealSmooth := contDiff_realPart hφ
  have himagSmooth := contDiff_imagPart hφ
  have hrealCompact := compactSupport_realPart φ hcompact
  have himagCompact := compactSupport_imagPart φ hcompact
  have hrealSupport : tsupport (fun x => (φ x).re) ⊆ Ω :=
    (tsupport_realPart_subset φ).trans hsupport
  have himagSupport : tsupport (fun x => (φ x).im) ⊆ Ω :=
    (tsupport_imagPart_subset φ).trans hsupport
  exact ⟨hweak _ hrealSmooth hrealCompact hrealSupport,
    hweak _ himagSmooth himagCompact himagSupport⟩

end Hormander.F
