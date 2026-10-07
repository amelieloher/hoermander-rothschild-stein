-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G4.AuxiliaryOrdinaryComparison
public import RothschildStein.G4.CompactControlBallBuffer
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
open scoped ENNReal
namespace RothschildStein.G4
open G3 G1

/-- Original-domain ordinary balls are sandwiched between two auxiliary
balls under the local comparison of Euclidean and control topologies. -/
theorem exists_ordinary_auxiliary_ball_sandwich_of_local_comparison {k n s : ℕ}
    (hn : 0 < n) (hs : 1 ≤ s) (w : Fin (k+1) → ℕ+)
    (D : FreeModelData (k+1) s w) (hw : ∀ i, (w i : ℕ) ≤ s)
    {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω)
    (X : Fin (k+1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (hstep : bracketStepOn Ω w X s)
    (hcomparison : LocalControlComparison Ω w X s)
    {z : Fin n → ℝ} (hz : z ∈ Ω) :
    ∃ R A ε : ℝ, 0 < R ∧ closedBall z R ⊆ Ω ∧ 1 ≤ A ∧ 0 < ε ∧
      ∀ x ∈ closedBall z (R/4), ∀ r : ℝ, 0 < r → r ≤ ε →
      {y | auxiliaryDistance (s := s) Ω w X x y < ENNReal.ofReal (r/A)} ⊆
        {y | controlDistance Ω w X x y < ENNReal.ofReal r} ∧
      {y | controlDistance Ω w X x y < ENNReal.ofReal r} ⊆
        {y | auxiliaryDistance (s := s) Ω w X x y < ENNReal.ofReal r} := by
  obtain ⟨R, C, η, hR, hRΩ, hC, hη, hc⟩ :=
    exists_local_auxiliary_ordinary_comparison_of_local_comparison
      hn hs w D hw hΩ X hX hstep hcomparison hz
  obtain ⟨β, hβ, hb⟩ := exists_compact_controlBall_buffer (Ω := Ω)
    (fun j => shortWeight w (shortIndex (s := s) w j))
    (fun j => shortField w X (shortIndex (s := s) w j)) hR
    (fun j => (shortField_contDiffOn hΩ hX _).continuousOn.mono hRΩ)
  let A := max 1 (2*C)
  have hAone : 1 ≤ A := le_max_left _ _
  have hA : 0 < A := zero_lt_one.trans_le hAone
  have hAC : 2*C ≤ A := le_max_right _ _
  let ε := min η β / 2
  have hε : 0 < ε := half_pos (lt_min hη hβ)
  refine ⟨R, A, ε, hR, hRΩ, hAone, hε, ?_⟩
  intro x hx r hr hrε
  have hrη : r < η := hrε.trans_lt ((half_lt_self (lt_min hη hβ)).trans_le (min_le_left _ _))
  have hrβ : r < β := hrε.trans_lt ((half_lt_self (lt_min hη hβ)).trans_le (min_le_right _ _))
  have hδ : 0 < r/A := div_pos hr hA
  have hδr : r/A ≤ r := (div_le_self hr.le hAone)
  constructor
  · intro y hy
    have hyβ : auxiliaryDistance (s := s) Ω w X x y < ENNReal.ofReal β :=
      hy.trans_le (ENNReal.ofReal_le_ofReal (hδr.trans hrβ.le))
    have hyR := hb x hx hyβ
    have hbound := hc x (closedBall_subset_closedBall (by linarith) hx) y hyR
      (r/A) hδ (hδr.trans_lt hrη) hy
    have hCr : C*(r/A) < r := by
      have he : A*(r/A) = r := by field_simp
      have hh := mul_le_mul_of_nonneg_right hAC hδ.le
      nlinarith
    exact hbound.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hr).mpr hCr)
  · intro y hy
    exact (auxiliaryDistance_le Ω w X hw x y).trans_lt hy
end RothschildStein.G4
