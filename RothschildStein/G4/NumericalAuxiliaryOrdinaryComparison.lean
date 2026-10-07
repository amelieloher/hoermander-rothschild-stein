-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G4.NumericalAuxiliaryHalving
public import RothschildStein.G4.GeometricCorrectionConvergence
public import RothschildStein.G4.ControlGeometricCorrection
public import RothschildStein.G1.ActualControlComparison
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric Filter
open scoped ENNReal Topology
namespace RothschildStein.G4
open G3 G1

/-- The ordinary-to-auxiliary cost constant depends only on numerical data.
Local topology comparison passes the constructed correction sequence to its limit. -/
theorem exists_numerical_auxiliary_ordinary_comparison (k n s h q : ℕ)
    (hn : 0 < n) (hs : 0 < s) (horder : q+1 = n*s+s) (hq : q+1 ≤ h)
    (w : Fin (k+1) → ℕ+) (D : G3.FreeModelData (k+1) s w)
    (hw : ∀ i, (w i : ℕ) ≤ s) (M Δ R₀ : ℝ) (hM : 0 ≤ M) (hΔ : 0 < Δ) (hR₀ : 0 < R₀) :
    ∃ R C η : ℝ, 0 < R ∧ 0 < C ∧ 0 < η ∧
      ∀ (Ω : Set (Fin n → ℝ)), IsOpen Ω →
      ∀ (X : Fin (k+1) → (Fin n → ℝ) → (Fin n → ℝ)),
      (∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (X j) Ω) → bracketStepOn Ω w X s →
      ∀ x₀ : Fin n → ℝ, closedBall x₀ R₀ ⊆ Ω →
      (∀ j, HasJetBound Ω (closedBall x₀ R₀) (X j)
        (max (max (2*(n*s)+2*s) (max ((q+1)*s) (h+1+s)))
          (max (4*(s+1)^3) (1+s))) M) →
      (∀ y ∈ closedBall x₀ R₀, ∃ B : Fin n → ShortWord w s,
        Δ ≤ |frameDet (shortField w X) B y|) →
      closedBall x₀ R ⊆ Ω ∧
      ∀ x ∈ closedBall x₀ R, ∀ y ∈ closedBall x₀ (R/2),
      ∀ δ : ℝ, 0 < δ → δ < η →
        auxiliaryDistance (s := s) Ω w X x y < ENNReal.ofReal δ →
        controlDistance Ω w X x y ≤ ENNReal.ofReal (C*δ) := by
  obtain ⟨R,C,η,E,hR,hC,hη,_hE,hprovider⟩ :=
    exists_numerical_auxiliary_halving k n s h q hn hs horder hq w D hw M Δ R₀ hM hΔ hR₀
  refine ⟨R,2*C,η,hR,by positivity,hη,?_⟩
  intro Ω hΩ X hX hstep z hRΩ hjets hmax
  obtain ⟨hRΩ',hhalve⟩ := hprovider Ω hΩ X hX hstep z hRΩ hjets hmax
  have hcomparison := G1.localControlComparison_of_smooth_bracketStep hΩ w X hX
    (by omega : 1 ≤ s) hw hstep
  refine ⟨hRΩ',?_⟩
  intro x hx y hy δ hδ hδη hxy
  obtain ⟨a, ha0, haK, hacost, haerror⟩ :=
    exists_geometric_correction_sequence_of_halving
      (controlDistance Ω w X) (auxiliaryDistance (s := s) Ω w X)
      hδ hδη hx hxy (fun v hv r hr hrη hd => hhalve v hv y hy r hr hrη hd)
  let aΩ : ℕ → Ω := fun j => ⟨a j, hRΩ' (haK j)⟩
  let yΩ : Ω := ⟨y, hRΩ' (closedBall_subset_closedBall (by linarith) hy)⟩
  have ht : Tendsto aΩ atTop (𝓝 yΩ) :=
    tendsto_subtype_rng.mpr (tendsto_geometric_correction_of_error a y E δ haerror)
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
