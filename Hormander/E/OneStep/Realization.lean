-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.E.OneStep.Transfer
public import Hormander.A.SmoothRepresentative.Main

open MeasureTheory SchwartzMap

@[expose] public section

noncomputable section

namespace Hormander.E
open Hormander.B
variable {N : ℕ}
/-- A compactly supported tempered distribution lying in every `H^s` is a
Schwartz function, since it is smooth. -/
theorem exists_schwartz_of_compactSupport (u : Tempered N)
    (hmem : ∀ s : ℝ, TemperedDistribution.MemSobolev s 2 u)
    (ζ : SchwartzMap (Carrier N) ℝ) (hζ : HasCompactSupport (ζ : Carrier N → ℝ))
    (hu : cutoffDistr ζ u = u) :
    ∃ g : TestFunction N, (g : Tempered N) = u := by
  obtain ⟨f, hf, hfu⟩ := Hormander.A.exists_contDiff_of_forall_memSobolev hmem
  have hcd : ContDiff ℝ (⊤ : ℕ∞) (fun x => (ζ x : ℂ) * f x) := by
    exact (Complex.ofRealCLM.contDiff.comp ζ.smooth').mul hf
  have hcs : HasCompactSupport (fun x => (ζ x : ℂ) * f x) := by
    exact (hζ.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)).mul_right
  refine ⟨hcs.toSchwartzMap hcd, ?_⟩
  ext φ
  conv_rhs => rw [← hu]
  rw [cutoffDistr_apply_apply, testToTempered_apply]
  have := (hfu (realMultiplierOperator ζ φ)).2
  rw [this]
  unfold bilinearPairing
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [realMultiplierOperator_apply]
  simp
  ring
end Hormander.E
