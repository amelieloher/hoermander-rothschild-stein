-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.LocalCoordinatePowerFactor
public import RothschildStein.G1.LocalPowerFactorLowerJets
public import RothschildStein.G3.LocalScalarTaylor

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter
open scoped Topology
namespace RothschildStein.G1

/-- Actual smooth displacement factors inherit their leading
coefficient from a model with error of order s+1. Lower jets and the
leading value are consequences of the error estimate, not premises
(BB Lemma 1.52, pp. 30–31; Lemma 9.26, pp. 417–419). -/
theorem exists_local_factor_of_model_error {E : Type} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [FiniteDimensional ℝ E] {n k s : ℕ}
    (hks : k ≤ s) {U : Set (E × ℝ)} (hU : IsOpen U)
    (G R : E × ℝ → (Fin n → ℝ))
    (hG : ContDiffOn ℝ (⊤ : ℕ∞) G U) (hR : ContDiffOn ℝ (⊤ : ℕ∞) R U)
    (M : ℝ) (herr : ∀ q ∈ U, ‖G q - q.2 ^ k • R q‖ ≤ M * |q.2| ^ (s + 1))
    (x₀ : E) (hx₀ : (x₀, 0) ∈ U) :
    ∃ V : Set (E × ℝ), IsOpen V ∧ (x₀, 0) ∈ V ∧ V ⊆ U ∧
      ∃ H : E × ℝ → (Fin n → ℝ), ContDiffOn ℝ (⊤ : ℕ∞) H V ∧
        (∀ q ∈ V, G q = q.2 ^ k • H q) ∧ (∀ x, (x, 0) ∈ V → H (x, 0) = R (x, 0)) := by
  have hslices : ∀ x, (x, 0) ∈ U → ∀ i : Fin n,
      (∀ j < k, iteratedDeriv j (fun t => G (x, t) i) 0 = 0) ∧
      iteratedDeriv k (fun t => G (x, t) i) 0 = (k.factorial : ℝ) * R (x, 0) i := by
    intro x hx i
    have hinc : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => (x, t)) :=
      contDiff_const.prodMk contDiff_id
    have hg : ContDiffAt ℝ (⊤ : ℕ∞) (fun t => G (x, t) i) 0 :=
      (contDiffAt_apply ℝ ℝ i (G (x, 0))).comp (g := fun z : Fin n → ℝ => z i) (f := fun t : ℝ => G (x, t)) (0 : ℝ)
        ((hG.contDiffAt (hU.mem_nhds hx)).comp (f := fun t : ℝ => (x, t)) (0 : ℝ) hinc.contDiffAt)
    have hr : ContDiffAt ℝ (⊤ : ℕ∞) (fun t => R (x, t) i) 0 :=
      (contDiffAt_apply ℝ ℝ i (R (x, 0))).comp (g := fun z : Fin n → ℝ => z i) (f := fun t : ℝ => R (x, t)) (0 : ℝ)
        ((hR.contDiffAt (hU.mem_nhds hx)).comp (f := fun t : ℝ => (x, t)) (0 : ℝ) hinc.contDiffAt)
    have hmodel : ContDiffAt ℝ (⊤ : ℕ∞) (fun t => t ^ k * R (x, t) i) 0 :=
      (contDiff_id.pow k).contDiffAt.mul hr
    have hbound : ∀ᶠ t : ℝ in 𝓝 0,
        ‖G (x, t) i - t ^ k * R (x, t) i‖ ≤ M * |t| ^ (s + 1) := by
      have hm := hinc.continuous.continuousAt.preimage_mem_nhds (hU.mem_nhds hx)
      filter_upwards [hm] with t ht
      exact (norm_le_pi_norm (G (x, t) - t ^ k • R (x, t)) i).trans (herr (x, t) ht)
    have hjets := G3.scalar_jets_eq_of_power_error_at
      (hg.of_le (m := s) (by simp)) (hmodel.of_le (m := s) (by simp)) hbound
    constructor
    · intro j hj
      rw [hjets j (by omega)]
      exact local_power_factor_lower_jets (hr.of_le (m := j) (by simp)) hj
        (Filter.EventuallyEq.rfl)
    · rw [hjets k hks]
      exact local_power_factor_leading_jet (hr.of_le (m := k) (by simp))
        (Filter.EventuallyEq.rfl)
  obtain ⟨V, hV, hV₀, hVU, H, hH, he⟩ := exists_local_coordinate_power_factor k hU G hG
    (fun x hx j hj i => (hslices x hx i).1 j hj) x₀ hx₀
  refine ⟨V, hV, hV₀, hVU, H, hH, he, ?_⟩
  intro x hx
  ext i
  have hinc : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => (x, t)) :=
    contDiff_const.prodMk contDiff_id
  have hh : ContDiffAt ℝ k (fun t => H (x, t) i) 0 :=
    ((contDiffAt_apply ℝ ℝ i (H (x, 0))).comp (g := fun z : Fin n → ℝ => z i) (f := fun t : ℝ => H (x, t)) (0 : ℝ)
      ((hH.contDiffAt (hV.mem_nhds hx)).comp (f := fun t : ℝ => (x, t)) (0 : ℝ) hinc.contDiffAt)).of_le (by simp)
  have hfactor : (fun t => G (x, t) i) =ᶠ[𝓝 0] (fun t => t ^ k * H (x, t) i) := by
    have hm := hinc.continuous.continuousAt.preimage_mem_nhds (hV.mem_nhds hx)
    filter_upwards [hm] with t ht
    exact congrArg (fun z : Fin n → ℝ => z i) (he (x, t) ht)
  have hj := (hslices x (hVU hx) i).2
  rw [local_power_factor_leading_jet hh hfactor] at hj
  exact mul_left_cancel₀ (by positivity : (k.factorial : ℝ) ≠ 0) hj

end RothschildStein.G1
