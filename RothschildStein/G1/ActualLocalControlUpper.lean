-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.LocalQuasiFlowCosts
public import RothschildStein.G1.BracketCoordinateDerivative
public import RothschildStein.G1.CoordinateEndpointCost
public import RothschildStein.G1.LocalUpperFromJointEndpoint
public import RothschildStein.G4.ShortFields

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Metric
open scoped Topology ENNReal
namespace RothschildStein.G1
open G3

/-- Smooth bracket-generating coefficients give genuine local
upper-comparison constants, uniform over nearby centers. The signed
coordinate chart, its inverse radius, and its primitive-curve costs are
all constructed from the coefficients (BB Theorem 1.53, p. 35). -/
theorem exists_actual_local_control_upper {a s n : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (hs : 1 ≤ s) (hw : ∀ i, (p i : ℕ) ≤ s) (hn : 0 < n)
    {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω)
    (X : Fin a → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (hstep : bracketStepOn Ω p X s) (z : Fin n → ℝ) (hz : z ∈ Ω) :
    ∃ ρ C : ℝ, 0 < ρ ∧ 0 < C ∧ ∀ x ∈ ball z ρ, ∀ y : Fin n → ℝ,
      ‖y - x‖ < ρ → controlDistance Ω p X x y ≤
        ENNReal.ofReal (C * ‖y - x‖ ^ (1 / (s : ℝ))) := by
  classical
  obtain ⟨P⟩ := exists_local_quasi_flow_data D hs hw hΩ X hX z hz
  obtain ⟨B, hB⟩ := G4.exists_short_frame hstep hz
  let H : Fin n → ℝ × (Fin n → ℝ) → (Fin n → ℝ) := fun i => P.signedMap (B i).val
  let F := coordinateEndpointChart H (List.finRange n)
  let A := frameCoordinateEquiv (G4.shortField p X) B z hB
  have hword : ∀ i, (B i).val ≠ [] ∧ wordWeight p (B i).val ≤ s :=
    fun i => (G4.mem_shortWordFamily_iff p _).mp (B i).property
  have hzero : ∀ i x, H i (0, x) = x := fun i x => P.signedMap_zero (B i).val x
  have hreg : ∀ i, ContDiffAt ℝ 1 (H i) (0, z) := fun i =>
    (P.signedMap_regular hΩ hX hs (B i).val (hword i).1 (hword i).2 P.center).1
  have hder : ∀ i, HasFDerivAt (H i)
      ((ContinuousLinearMap.snd ℝ ℝ (Fin n → ℝ)) +
        (ContinuousLinearMap.toSpanSingleton ℝ (G4.shortField p X (B i) z)).comp
          (ContinuousLinearMap.fst ℝ ℝ (Fin n → ℝ))) (0, z) := fun i =>
    (P.signedMap_regular hΩ hX hs (B i).val (hword i).1 (hword i).2 P.center).2
  have hF : ContDiffAt ℝ 1 F (0, z) :=
    coordinateEndpointChart_contDiffAt_zero H hzero (List.finRange n) z hreg
  have hFzero : ∀ x, F (0, x) = x :=
    fun x => coordinateEndpointChart_zero H hzero (List.finRange n) x
  have hAeq : (fderiv ℝ F (0, z)).comp
      (ContinuousLinearMap.inl ℝ (Fin n → ℝ) (Fin n → ℝ)) = (A : _ →L[ℝ] _) :=
    bracketCoordinateChart_coefficient_derivative (G4.shortField p X) B z hB H hzero hder
  let L : ℝ := (3 * 2 ^ (s - 1) : ℕ)
  have hL : 0 < L := by dsimp [L]; positivity
  have hα : 0 ≤ 1 / (s : ℝ) := by positivity
  have hcost := coordinateEndpointChart_eventually_control_cost hΩ p X H hzero
    (List.finRange n) z hz hreg hL.le hα
    (fun i => P.signedMap_eventually_cost hs (B i).val (hword i).1 (hword i).2)
  have hcost' : ∀ᶠ q : (Fin n → ℝ) × (Fin n → ℝ) in 𝓝 (0, z),
      controlDistance Ω p X q.2 (F q) ≤ ENNReal.ofReal (((n : ℝ) * L) * ‖q.1‖ ^ (1 / (s : ℝ))) := by
    simpa only [List.length_finRange] using hcost
  exact exists_local_control_upper_of_joint_endpoint Ω p X F z hF hFzero A hAeq
    (mul_pos (by exact_mod_cast hn) hL) hα hcost'

end RothschildStein.G1
