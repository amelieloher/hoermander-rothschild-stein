-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.SpatialJetBounds

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology

namespace RothschildStein.G1

/-- A stationary-parameter lift preserves all finite coefficient-jet
bounds in the product norm (BB Prop 1.2, p. 3). -/
theorem stationaryLift_jet_norm_le {P E : Type*} [NormedAddCommGroup P]
    [NormedSpace ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Z : P × E → E} {p : P × E} (hZ : ContDiffAt ℝ (⊤ : ℕ∞) Z p) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (fun q => ((0 : P), Z q)) p‖ ≤ ‖iteratedFDeriv ℝ n Z p‖ := by
  have h := (ContinuousLinearMap.inr ℝ P E).norm_iteratedFDeriv_comp_left hZ (n := n) (by simp)
  exact h.trans (mul_le_of_le_one_left (norm_nonneg _) (ContinuousLinearMap.norm_inr_le_one (𝕜 := ℝ) (E := P) (F := E)))

/-- Higher parameter and initial-point derivatives are bounded together
by the finite mixed coefficient jets, assuming joint smooth dependence.
The additional smaller cylinder is explicit and uniform in the initial point:
spatialJetRate r B * |t| < 1 (BB Prop 1.2, pp. 3–4). -/
theorem parameterFlow_spatialJets_bound_of_joint_contDiff {P E : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A : Set P} {Ω : Set E} {U : Set (P × E)}
    (hA : IsOpen A) (hΩ : IsOpen Ω) (hU : IsOpen U) (hUA : U ⊆ A ×ˢ Ω)
    {Z : P × E → E} (hZ : ContDiffOn ℝ (⊤ : ℕ∞) Z (A ×ˢ Ω))
    {τ : ℝ} (hτ : 0 < τ) (Φ : (P × E) × ℝ → E)
    (hjoint : ContDiffOn ℝ (⊤ : ℕ∞) Φ (U ×ˢ Ioo (-τ) τ))
    (hΦ : ∀ p ∈ U, Φ (p, 0) = p.2 ∧ ∀ v ∈ Ioo (-τ) τ,
      HasDerivAt (fun w => Φ (p, w)) (Z (p.1, Φ (p, v))) v ∧ Φ (p, v) ∈ Ω)
    (r : ℕ) {p : P × E} (hp : p ∈ U) {t B : ℝ} (ht : t ∈ Ioo (-τ) τ)
    (hB : 0 ≤ B)
    (hbound : ∀ v ∈ uIcc 0 t, ∀ j ≤ r,
      ‖iteratedFDeriv ℝ j Z (p.1, Φ (p, v))‖ ≤ B)
    (hsmall : spatialJetRate r B * |t| < 1) :
    ∀ n, 1 ≤ n → n ≤ r → ‖iteratedFDeriv ℝ n (fun q => Φ (q, t)) p‖ < 2 := by
  let Ψ : (P × E) × ℝ → P × E := fun q => (q.1.1, Φ q)
  let F : P × E → P × E := fun q => (0, Z q)
  have hF : ContDiffOn ℝ (⊤ : ℕ∞) F (A ×ˢ Ω) := contDiffOn_const.prodMk hZ
  have hΨ : ContDiffOn ℝ (⊤ : ℕ∞) Ψ (U ×ˢ Ioo (-τ) τ) :=
    (contDiffOn_fst.fst).prodMk hjoint
  have hflow : ∀ q ∈ U, Ψ (q, 0) = q ∧ ∀ v ∈ Ioo (-τ) τ,
      HasDerivAt (fun w => Ψ (q, w)) (F (Ψ (q, v))) v ∧ Ψ (q, v) ∈ A ×ˢ Ω := by
    intro q hq
    refine ⟨?_, ?_⟩
    · exact Prod.ext rfl (hΦ q hq).1
    · intro v hv
      exact ⟨(hasDerivAt_const v q.1).prodMk ((hΦ q hq).2 v hv).1,
        (hUA hq).1, ((hΦ q hq).2 v hv).2⟩
  have hcoeff : ∀ v ∈ uIcc 0 t, ∀ j ≤ r, ‖iteratedFDeriv ℝ j F (Ψ (p, v))‖ ≤ B := by
    intro v hv j hj
    have hsub := ordConnected_Ioo.uIcc_subset (show (0 : ℝ) ∈ Ioo (-τ) τ from ⟨by linarith, hτ⟩) ht
    exact (stationaryLift_jet_norm_le
      (hZ.contDiffAt ((hA.prod hΩ).mem_nhds ((hflow p hp).2 v (hsub hv)).2)) j).trans
      (hbound v hv j hj)
  have hmain := localFlow_spatialJets_bound_of_joint_contDiff (hA.prod hΩ) hU hF hτ
    Ψ hΨ hflow r hp ht hB hcoeff hsmall
  intro n hn hnr
  have hs : ContDiffAt ℝ (⊤ : ℕ∞) (fun q => Ψ (q, t)) p :=
    (hΨ.comp (contDiffOn_id.prodMk contDiffOn_const) (fun q hq => ⟨hq, ht⟩)).contDiffAt
      (hU.mem_nhds hp)
  have hh := (ContinuousLinearMap.snd ℝ P E).norm_iteratedFDeriv_comp_left hs (n := n) (by simp)
  exact (hh.trans (mul_le_of_le_one_left (norm_nonneg _)
    (ContinuousLinearMap.norm_snd_le ℝ P E))).trans_lt (hmain n hn hnr)

end RothschildStein.G1
