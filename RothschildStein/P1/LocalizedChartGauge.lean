-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.TypeKernelJointContinuity

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set
namespace RothschildStein.P1.LiftedChart
variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  (C : LiftedChart w s Ω hΩ X x₀ m)

/-- The original chart gauge on interior pairs, extended by zero.
This auxiliary extension supplies measurability without imposing any
regularity on the chart map outside its domain. -/
def localizedInputGauge (ν : (Fin (n + m) → ℝ) → ℝ)
    (ξ η : Fin (n + m) → ℝ) : ℝ := by
  classical
  exact if ξ ∈ C.U ∧ η ∈ C.U then ν (C.Θ η ξ) else 0

theorem localizedInputGauge_eq (ν : (Fin (n + m) → ℝ) → ℝ)
    {ξ η : Fin (n + m) → ℝ} (hξ : ξ ∈ C.U) (hη : η ∈ C.U) :
    C.localizedInputGauge ν ξ η = ν (C.Θ η ξ) := by
  classical
  exact ite_eq_left ⟨hξ, hη⟩

theorem measurable_localizedInputGauge {ν : (Fin (n + m) → ℝ) → ℝ}
    (hν : Continuous ν) : Measurable (Function.uncurry (C.localizedInputGauge ν)) := by
  classical
  have hc : ContinuousOn
      (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => ν (C.Θ p.2 p.1)) (C.U ×ˢ C.U) :=
    hν.comp_continuousOn ((C.theta_smooth.comp (contDiffOn_snd.prodMk contDiffOn_fst)
      (fun _ hp => ⟨hp.2, hp.1⟩)).continuousOn)
  exact hc.measurable_piecewise continuousOn_const
    (C.isOpen_U.prod C.isOpen_U).measurableSet

theorem localizedInputGauge_symm {ν : (Fin (n + m) → ℝ) → ℝ}
    (hs : ∀ u, ν (-u) = ν u) (ξ η : Fin (n + m) → ℝ) :
    C.localizedInputGauge ν ξ η = C.localizedInputGauge ν η ξ := by
  classical
  by_cases h : ξ ∈ C.U ∧ η ∈ C.U
  · rw [C.localizedInputGauge_eq ν h.1 h.2, C.localizedInputGauge_eq ν h.2 h.1,
      C.theta_antisymm η h.2 ξ h.1, hs]
  · have ht : ¬ (η ∈ C.U ∧ ξ ∈ C.U) := fun hh => h ⟨hh.2, hh.1⟩
    simp only [localizedInputGauge, ite_eq_right h, ite_eq_right ht]

end RothschildStein.P1.LiftedChart
