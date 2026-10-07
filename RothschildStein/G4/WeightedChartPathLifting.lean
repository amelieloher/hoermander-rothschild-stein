-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.ChartLiftSupremum
public import Mathlib.Topology.Order.IntermediateValue

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace RothschildStein.G4

/-- Uniform weighted variation closes the local-inverse
continuation argument through time 1. The actual set of lift lifetimes
is used; neither a global inverse nor a covering map is assumed
(BB Prop 9.52, p. 449). -/
theorem exists_chartPathLift_of_weighted_variation {n s : ℕ} (w : Fin n → ℕ+)
    (hw : ∀ i, (w i : ℕ) ≤ s) {a r C b : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hr : 0 < r) (hr1 : r ≤ 1)
    (hCb : 0 ≤ C * b) (hmargin : C * b < (a / 2) ^ s / 4)
    (F : (Fin n → ℝ) → (Fin n → ℝ)) (γ : ℝ → (Fin n → ℝ))
    (hF : ContDiffOn ℝ (⊤ : ℕ∞) F (weightedBox w (a * r)))
    (hjac : ∀ u ∈ weightedBox w (a * r),
      Matrix.det (coordinateDerivativeMatrix (fderiv ℝ F u)) ≠ 0)
    (hγ : ContinuousOn γ (Icc (0 : ℝ) 1)) (hstart : F 0 = γ 0)
    (hvariation : ∀ T : ℝ, T ≤ 1 → ∀ θ : ℝ → (Fin n → ℝ),
      IsChartPathLift F γ θ (weightedBox w (a * r)) T →
      ∀ σ ∈ Icc (0 : ℝ) T, ∀ τ ∈ Icc (0 : ℝ) T, ∀ i,
        |θ τ i - θ σ i| ≤ C * b * r ^ (w i : ℕ) * |τ - σ|) :
    ∃ θ, IsChartPathLift F γ θ (weightedBox w (a * r)) 1 := by
  classical
  let S : Set ℝ := {T | 0 ≤ T ∧ T ≤ 1 ∧
    ∃ θ, IsChartPathLift F γ θ (weightedBox w (a * r)) T}
  have hzero : (0 : Fin n → ℝ) ∈ weightedBox w (a * r) := by
    intro i
    simpa only [Pi.zero_apply, abs_zero] using pow_pos (mul_pos ha hr) (w i : ℕ)
  have h0 : (0 : ℝ) ∈ S := ⟨le_rfl, zero_le_one,
    ⟨fun _ => 0, chartPathLift_initial F γ hzero hstart⟩⟩
  have hSne : S.Nonempty := ⟨0, h0⟩
  have hS1 : S ⊆ Icc (0 : ℝ) 1 := fun T hT => ⟨hT.1, hT.2.1⟩
  have hbdd : BddAbove S := ⟨1, fun T hT => hT.2.1⟩
  have hgrow : ∀ T ∈ S ∩ Ico (0 : ℝ) 1, (S ∩ Ioc T 1).Nonempty := by
    intro T hT
    obtain ⟨θ, hθ⟩ := hT.1.2.2
    obtain ⟨T', hTT', hT'1, θ', hθ'⟩ := chartPathLift_extend F γ
      (isOpen_weightedBox w (a * r)) hF hjac hγ hT.2.1 hT.2.2 hθ
    exact ⟨T', ⟨hT.2.1.trans hTT'.le, hT'1, θ', hθ'⟩, hTT', hT'1⟩
  obtain ⟨T₀, hT₀S, hT₀pos, _hT₀1⟩ := hgrow 0 ⟨h0, le_rfl, zero_lt_one⟩
  have hSup : 0 < sSup S := hT₀pos.trans_le (le_csSup hbdd hT₀S)
  have hSup1 : sSup S ≤ 1 := csSup_le hSne (fun T hT => hT.2.1)
  choose θ hθ using fun T : S => T.property.2.2
  obtain ⟨Θ, hΘ⟩ := exists_chartPathLift_at_supremum w hw ha ha1 hr hr1 hCb hmargin F γ
    hF.continuousOn (isLocalHomeomorphOn_of_actual_jacobian
      (isOpen_weightedBox w (a * r)) F hF hjac) hγ S hSne hS1 hSup θ hθ
    (fun T => hvariation T (T.property.2.1) (θ T) (hθ T))
  have hcs : sSup (S ∩ Icc (0 : ℝ) 1) ∈ S := by
    rw [inter_eq_left.mpr hS1]
    exact ⟨hSup.le, hSup1, Θ, hΘ⟩
  have h1 : (1 : ℝ) ∈ S :=
    mem_of_csSup_mem_of_forall_exists_gt hcs h0 zero_le_one hgrow
  exact h1.2.2

end RothschildStein.G4
