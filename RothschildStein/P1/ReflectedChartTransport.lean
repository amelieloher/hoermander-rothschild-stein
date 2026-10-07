-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.RightParametrixTransport

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped Topology
namespace RothschildStein.P1.LiftedChart
variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart w s Ω hΩ X x₀ m}

/-- Reflect the existing transported density to
use the input chart variable Θ(η,ξ) at fixed output ξ (BB p. 550). -/
def reflectedTransport (C : LiftedChart w s Ω hΩ X x₀ m)
    (ξ : Fin (n + m) → ℝ) (ψ : (Fin (n + m) → ℝ) → ℝ)
    (u : Fin (n + m) → ℝ) : ℝ := C.modelTransport ξ ψ (-u)

/-- The reflected density has the same diagonal
value c(ξ)ψ(ξ). -/
theorem reflectedTransport_zero {ξ : Fin (n + m) → ℝ} (hξ : ξ ∈ C.U)
    (ψ : (Fin (n + m) → ℝ) → ℝ) :
    C.reflectedTransport ξ ψ 0 = C.c ξ * ψ ξ := by
  simpa only [reflectedTransport, neg_zero] using modelTransport_zero hξ ψ

/-- Actual change of variables for the input endpoint,
including the positive chart density; this reuses the existing transport. -/
theorem integral_input_theta_mul {ξ : Fin (n + m) → ℝ} (hξ : ξ ∈ C.U)
    (g ψ : (Fin (n + m) → ℝ) → ℝ) :
    (∫ η in C.U, g (C.Θ η ξ) * ψ η) =
      ∫ u, g u * C.reflectedTransport ξ ψ u := by
  calc
    _ = ∫ η in C.U, g (-C.Θ ξ η) * ψ η :=
      setIntegral_congr_fun C.isOpen_U.measurableSet
        (fun η hη => by rw [C.theta_antisymm ξ hξ η hη])
    _ = ∫ u, g (-u) * C.modelTransport ξ ψ u :=
      integral_comp_theta_mul hξ (fun u => g (-u)) ψ
    _ = ∫ u, g u * C.reflectedTransport ξ ψ u := by
      simpa only [reflectedTransport, neg_neg] using
        (integral_neg_eq_self (fun u => g (-u) * C.modelTransport ξ ψ u) volume).symm

/-- A compact smooth input test gives a compact smooth
reflected density. -/
theorem reflectedTransport_regular {ξ : Fin (n + m) → ℝ} (hξ : ξ ∈ C.U)
    (ψ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞)) :
    ContDiff ℝ (⊤ : ℕ∞) (C.reflectedTransport ξ ψ) ∧
      HasCompactSupport (C.reflectedTransport ξ ψ) := by
  refine ⟨(contDiff_modelTransport hξ ψ).comp contDiff_neg, ?_⟩
  exact (hasCompactSupport_modelTransport hξ ψ).comp_homeomorph (Homeomorph.neg _)

end RothschildStein.P1.LiftedChart
