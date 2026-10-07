-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.L1.FreeTriangularLift
public import RothschildStein.L1.BoundedWordStep
public import RothschildStein.L1.TriangularSmoothness
public import RothschildStein.Definitions.StepSpansAt

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.L1

/-- The fixed polynomial lift chosen before the model,
coordinates and geometric constants (BB pp. 493–494). -/
structure FixedLiftData {n k : ℕ} (w : Fin k → ℕ+) (s : ℕ)
    (Ω : Set (Fin n → ℝ)) (X : Fin k → (Fin n → ℝ) → (Fin n → ℝ))
    (x₀ : Fin n → ℝ) (m : ℕ) where
  dimension : n+m = freeDimension k s w
  P : Fin k → Fin m → MvPolynomial (Fin (n+m)) ℝ
  U : Opens (Fin (n+m) → ℝ)
  center_mem : joinPoint x₀ (0 : Fin m → ℝ) ∈ U
  subset_domain : (U : Set (Fin (n+m) → ℝ)) ⊆ basePoint ⁻¹' Ω
  vars_lt : ∀ i l, ∀ j ∈ (P i l).vars, j.val < n+l.val
  smooth : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (triangularLift X P i) (basePoint ⁻¹' Ω)
  free_spanning : ∀ ξ ∈ U, FreeAt w s (triangularLift X P) ξ ∧ StepSpansAt w s (triangularLift X P) ξ

/-- The pointwise bracket-step hypothesis constructs the fixed
lift with the exact lifted dimension (BB pp. 483–485, 493–494). -/
theorem exists_fixedLiftData {n k : ℕ} (w : Fin k → ℕ+) (s : ℕ)
    (Ω : Set (Fin n → ℝ)) (hΩ : IsOpen Ω)
    (X : Fin k → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (x₀ : Fin n → ℝ) (hx₀ : x₀ ∈ Ω) (hspan : StepSpansAt w s X x₀) :
    ∃ m : ℕ, Nonempty (FixedLiftData w s Ω X x₀ m) := by
  have hstep : bracketStepOn {x₀} w X s := by
    intro x hx
    simpa only [StepSpansAt, Set.mem_singleton_iff.mp hx] using hspan
  have hs := bounded_word_span_eq_top_of_bracketStepOn hstep (Set.mem_singleton x₀)
  obtain ⟨m,U,P,hd,_,hc,hU,hP,_,hfree⟩ :=
    exists_free_polynomial_triangular_lift ⟨Ω,hΩ⟩ X hX x₀ hx₀ hs
  have hspans := bracketStepOn_of_bounded_word_spans (U : Set (Fin (n+m) → ℝ)) w
    (triangularLift X P) (fun ξ hξ => (hfree ξ hξ).2)
  exact ⟨m, ⟨⟨hd,P,U,hc,hU,hP,contDiffOn_triangularLift X hX P,
    fun ξ hξ => ⟨(hfree ξ hξ).1, by simpa only [StepSpansAt] using hspans ξ hξ⟩⟩⟩⟩

end RothschildStein.L1
