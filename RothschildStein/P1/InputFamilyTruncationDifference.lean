-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.ReflectedChartTransport
public import RothschildStein.P1.GaugeChartIntegrability
public import RothschildStein.P1.AmbientTruncationLocalization

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
namespace RothschildStein.P1.LiftedChart
variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart w s Ω hΩ X x₀ m}

/-- The truncation error of any genuinely
integrable chart family equals its negative transported small-ball
integral, including the moving endpoint and positive chart density. -/
theorem inputFamily_truncation_sub_integral
    {ξ : Fin (n + m) → ℝ} (hξ : ξ ∈ C.U)
    (ν : (Fin (n + m) → ℝ) → ℝ) (hν : Continuous ν)
    (Ψ : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ)
    (ψ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞))
    (hi : Integrable (fun η => Ψ ξ η (C.Θ η ξ) * ψ η)) (ε : ℝ) :
    (∫ η in {η | ε < ν (C.Θ η ξ)}, Ψ ξ η (C.Θ η ξ) * ψ η) -
      (∫ η, Ψ ξ η (C.Θ η ξ) * ψ η) =
      -(∫ u in {u | ν u ≤ ε}, Ψ ξ ((C.e ξ).symm (-u)) u * C.reflectedTransport ξ ψ u) := by
  classical
  let f := fun η => Ψ ξ η (C.Θ η ξ) * ψ η
  let g := fun u => Ψ ξ ((C.e ξ).symm (-u)) u
  let A := C.U ∩ {η | ε < ν (C.Θ η ξ)}
  let B := {u : Fin (n + m) → ℝ | ν u ≤ ε}
  let b := fun η => (B.indicator g) (C.Θ η ξ) * ψ η
  have hA : MeasurableSet A :=
    ((hν.comp_continuousOn (C.contDiffOn_Θ_fst hξ).continuousOn).isOpen_inter_preimage
      C.isOpen_U isOpen_Ioi).measurableSet
  have hB : MeasurableSet B := (isClosed_le hν continuous_const).measurableSet
  have hz : ∀ η, η ∉ C.U → f η = 0 := by
    intro η hη
    dsimp only [f]
    rw [image_eq_zero_of_notMem_tsupport (fun ht => hη (ψ.tsupport_subset ht)), mul_zero]
  have he : (fun η => f η - A.indicator f η) = b := by
    funext η
    by_cases hη : η ∈ C.U
    · have hinv : (C.e ξ).symm (-C.Θ η ξ) = η := by
        rw [C.theta_antisymm ξ hξ η hη, neg_neg]
        exact C.symm_theta hξ hη
      by_cases ht : ε < ν (C.Θ η ξ)
      · rw [indicator_of_mem (show η ∈ A from ⟨hη, ht⟩)]
        change f η - f η = (B.indicator g) (C.Θ η ξ) * ψ η
        rw [indicator_of_notMem (show C.Θ η ξ ∉ B from not_le.mpr ht), zero_mul, sub_self]
      · rw [indicator_of_notMem (show η ∉ A from fun h => ht h.2), sub_zero]
        change f η = (B.indicator g) (C.Θ η ξ) * ψ η
        rw [indicator_of_mem (show C.Θ η ξ ∈ B from le_of_not_gt ht)]
        dsimp only [f, g]
        rw [hinv]
    · rw [hz η hη, indicator_of_notMem (show η ∉ A from fun h => hη h.1), sub_self]
      change 0 = (B.indicator g) (C.Θ η ξ) * ψ η
      rw [image_eq_zero_of_notMem_tsupport (fun ht => hη (ψ.tsupport_subset ht)), mul_zero]
  have hiA := hi.indicator hA
  have heb : (∫ η, b η) = (∫ η, f η) - (∫ η, A.indicator f η) := by
    rw [← he]
    exact integral_sub hi hiA
  have heSmall : (∫ η, b η) = ∫ u in B, g u * C.reflectedTransport ξ ψ u := by
    have hzB : ∀ η, η ∉ C.U → b η = 0 := by
      intro η hη
      dsimp only [b]
      rw [image_eq_zero_of_notMem_tsupport (fun ht => hη (ψ.tsupport_subset ht)), mul_zero]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzB,
      C.integral_input_theta_mul hξ (B.indicator g) ψ, ← integral_indicator hB]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro u
    by_cases hu : u ∈ B
    · simp only [indicator_of_mem hu]
    · simp only [indicator_of_notMem hu, zero_mul]
  have heSharp : (∫ η, A.indicator f η) =
      ∫ η in {η | ε < ν (C.Θ η ξ)}, f η := by
    rw [integral_indicator hA]
    change (∫ η in C.U ∩ {η | ε < ν (C.Θ η ξ)}, f η) = _
    simpa only [inter_comm] using integral_localizedTruncation
      (A := {η | ε < ν (C.Θ η ξ)}) C.isOpen_U.measurableSet hz
  rw [heSmall, heSharp] at heb
  change (∫ η in {η | ε < ν (C.Θ η ξ)}, f η) - (∫ η, f η) =
    -(∫ u in B, g u * C.reflectedTransport ξ ψ u)
  linarith

end RothschildStein.P1.LiftedChart
