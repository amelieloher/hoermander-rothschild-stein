-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G4.SmoothAuxiliaryHalving
public import RothschildStein.G4.GeometricCorrectionConvergence
public import RothschildStein.G4.ControlGeometricCorrection
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric Filter
open scoped ENNReal Topology
namespace RothschildStein.G4
open G3 G1

/-- Constructed primitive corrections give the local ordinary-cost
comparison. The local ordinary-cost comparison follows from the local topology
comparison alone; no ball comparison or primitive approximation is assumed. -/
theorem exists_local_auxiliary_ordinary_comparison_of_local_comparison {k n s : ℕ}
    (hn : 0 < n) (hs : 1 ≤ s) (w : Fin (k+1) → ℕ+)
    (D : FreeModelData (k+1) s w) (hw : ∀ i, (w i : ℕ) ≤ s)
    {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω)
    (X : Fin (k+1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (hstep : bracketStepOn Ω w X s)
    (hcomparison : LocalControlComparison Ω w X s)
    {z : Fin n → ℝ} (hz : z ∈ Ω) :
    ∃ R C η : ℝ, 0 < R ∧ closedBall z R ⊆ Ω ∧ 0 < C ∧ 0 < η ∧
      ∀ x ∈ closedBall z R, ∀ y ∈ closedBall z (R/2),
      ∀ δ : ℝ, 0 < δ → δ < η →
        auxiliaryDistance (s := s) Ω w X x y < ENNReal.ofReal δ →
        controlDistance Ω w X x y ≤ ENNReal.ofReal (C*δ) := by
  obtain ⟨R, C, η, M, hR, hRΩ, hC, hη, _hM, hhalve⟩ :=
    exists_smooth_auxiliary_halving hn hs w D hw hΩ X hX hstep hz
  refine ⟨R, 2*C, η, hR, hRΩ, by positivity, hη, ?_⟩
  intro x hx y hy δ hδ hδη hxy
  obtain ⟨a, ha0, haK, hacost, haerror⟩ :=
    exists_geometric_correction_sequence_of_halving
      (controlDistance Ω w X) (auxiliaryDistance (s := s) Ω w X)
      hδ hδη hx hxy (fun v hv r hr hrη hd => hhalve v hv y hy r hr hrη hd)
  let aΩ : ℕ → Ω := fun j => ⟨a j, hRΩ (haK j)⟩
  let yΩ : Ω := ⟨y, hRΩ (closedBall_subset_closedBall (by linarith) hy)⟩
  have ht : Tendsto aΩ atTop (𝓝 yΩ) :=
    tendsto_subtype_rng.mpr (tendsto_geometric_correction_of_error a y M δ haerror)
  have hc : ∀ j, controlDistance Ω w X (aΩ j).val (aΩ (j+1)).val ≤
      ENNReal.ofReal (C*δ) / (2 : ℝ≥0∞)^j := by
    intro j
    have he : C*(δ*(1/2:ℝ)^j) = (C*δ)/(2:ℝ)^j := by
      rw [one_div_pow]
      ring
    have hh := hacost j
    rw [he, ENNReal.ofReal_div_of_pos (by positivity),
      ENNReal.ofReal_pow (by norm_num : (0:ℝ) ≤ 2), ENNReal.ofReal_ofNat] at hh
    exact hh
  have hh := controlDistance_geometric_correction_of_local_comparison hΩ w X
    (fun i => (hX i).continuousOn) (by omega) hcomparison aΩ yΩ (C*δ) hc ht
  simpa only [aΩ, yΩ, ha0, mul_assoc] using hh
end RothschildStein.G4
