-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.SpatialJets
public import RothschildStein.G1.JetBarrier

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology BigOperators

namespace RothschildStein.G1

/-- Finite coefficient-jet constant for a simultaneous spatial-jet
bootstrap (BB Prop 1.2, p. 3). -/
def spatialJetRate (r : ℕ) (B : ℝ) : ℝ :=
  ∑ i : Fin r, ((i.val + 1).factorial : ℝ) * B * 2 ^ (i.val + 1)

/-- Positive-order jets of the initial identity map have norm at most
one, including the zero-dimensional space (BB Prop 1.2, p. 3). -/
theorem norm_iteratedFDeriv_id_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (n : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ (n + 1) (id : E → E) x‖ ≤ 1 := by
  rw [iteratedFDeriv_succ_eq_comp_right, Function.comp_apply, LinearIsometryEquiv.norm_map]
  simp only [fderiv_id]
  cases n with
  | zero => simpa only [norm_iteratedFDeriv_zero] using ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := E)
  | succ n => simp only [iteratedFDeriv_succ_const]; norm_num

/-- Quantitative bounds for every positive-order spatial jet through
order r under joint smoothness and the flow equation.
The coefficient jets determine the additional smaller time cylinder explicitly:
spatialJetRate r B * |t| < 1. Stationary parameter coordinates may be included
in E, so the bound also applies to their mixed initial derivatives
(BB Prop 1.2, pp. 3–4). -/
theorem localFlow_spatialJets_bound_of_joint_contDiff {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω U : Set E}
    (hΩ : IsOpen Ω) (hU : IsOpen U) {Z : E → E}
    (hZ : ContDiffOn ℝ (⊤ : ℕ∞) Z Ω) {τ : ℝ} (hτ : 0 < τ)
    (Φ : E × ℝ → E)
    (hjoint : ContDiffOn ℝ (⊤ : ℕ∞) Φ (U ×ˢ Ioo (-τ) τ))
    (hΦ : ∀ x ∈ U, Φ (x, 0) = x ∧ ∀ v ∈ Ioo (-τ) τ,
      HasDerivAt (fun w => Φ (x, w)) (Z (Φ (x, v))) v ∧ Φ (x, v) ∈ Ω)
    (r : ℕ) {x : E} (hx : x ∈ U) {t B : ℝ} (ht : t ∈ Ioo (-τ) τ)
    (hB : 0 ≤ B)
    (hbound : ∀ v ∈ uIcc 0 t, ∀ j ≤ r, ‖iteratedFDeriv ℝ j Z (Φ (x, v))‖ ≤ B)
    (hsmall : spatialJetRate r B * |t| < 1) :
    ∀ n, 1 ≤ n → n ≤ r → ‖iteratedFDeriv ℝ n (fun y => Φ (y, t)) x‖ < 2 := by
  let W : ℝ → (i : Fin r) → E [×(i.val + 1)]→L[ℝ] E :=
    fun v i => spatialJet (i.val + 1) Φ (x, v)
  let V : ℝ → (i : Fin r) → E [×(i.val + 1)]→L[ℝ] E :=
    fun v i => iteratedFDeriv ℝ (i.val + 1) (fun y => Z (Φ (y, v))) x
  have hzero : (0 : ℝ) ∈ Ioo (-τ) τ := ⟨by linarith, hτ⟩
  have hsub : uIcc 0 t ⊆ Ioo (-τ) τ := ordConnected_Ioo.uIcc_subset hzero ht
  have hd : ∀ v ∈ uIcc 0 t, HasDerivAt W (V v) v := by
    intro v hv
    exact hasDerivAt_pi.mpr (fun i => localFlow_spatialJet_hasDerivAt_of_joint_contDiff
      hU hZ Φ hjoint (fun y hy => (hΦ y hy).2) (i.val + 1) hx (hsub hv))
  have hinit : ‖W 0‖ ≤ 1 := by
    apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
    intro i
    have heq : (fun y => Φ (y, 0)) =ᶠ[𝓝 x] id := by
      filter_upwards [hU.mem_nhds hx] with y hy
      exact (hΦ y hy).1
    change ‖iteratedFDeriv ℝ (i.val + 1) (fun y => Φ (y, 0)) x‖ ≤ 1
    rw [(heq.iteratedFDeriv ℝ (i.val + 1)).eq_of_nhds]
    exact norm_iteratedFDeriv_id_le i.val x
  have hrate : 0 ≤ spatialJetRate r B := Finset.sum_nonneg (fun i _ => by positivity)
  have hvbound : ∀ v ∈ uIcc 0 t, ‖W v‖ ≤ 2 → ‖V v‖ ≤ spatialJetRate r B := by
    intro v hv hw
    apply (pi_norm_le_iff_of_nonneg hrate).mpr
    intro i
    have hs : ContDiffOn ℝ (⊤ : ℕ∞) (fun y => Φ (y, v)) U :=
      hjoint.comp (contDiffOn_id.prodMk contDiffOn_const) (fun y hy => ⟨hy, hsub hv⟩)
    have hC : ∀ j, j ≤ i.val + 1 → ‖iteratedFDerivWithin ℝ j Z Ω (Φ (x, v))‖ ≤ B := by
      intro j hj
      rw [iteratedFDerivWithin_eq_iteratedFDeriv hΩ.uniqueDiffOn
        ((hZ.contDiffAt (hΩ.mem_nhds ((hΦ x hx).2 v (hsub hv)).2)).of_le (by simp))
        ((hΦ x hx).2 v (hsub hv)).2]
      exact hbound v hv j (by omega)
    have hD : ∀ j, 1 ≤ j → j ≤ i.val + 1 →
        ‖iteratedFDerivWithin ℝ j (fun y => Φ (y, v)) U x‖ ≤ (2 : ℝ) ^ j := by
      intro j hj hjn
      rw [iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn
        ((hs.contDiffAt (hU.mem_nhds hx)).of_le (by simp)) hx]
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
      have hk : k < r := by omega
      have hjet := (norm_le_pi_norm (W v) ⟨k, hk⟩).trans hw
      exact hjet.trans (le_self_pow₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega))
    have hm := norm_iteratedFDerivWithin_comp_le hZ hs (n := i.val + 1) (by simp)
      hΩ.uniqueDiffOn hU.uniqueDiffOn (fun y hy => ((hΦ y hy).2 v (hsub hv)).2) hx hC hD
    rw [iteratedFDerivWithin_eq_iteratedFDeriv hU.uniqueDiffOn
      (((hZ.comp hs (fun y hy => ((hΦ y hy).2 v (hsub hv)).2)).contDiffAt
        (hU.mem_nhds hx)).of_le (by simp)) hx] at hm
    apply hm.trans
    unfold spatialJetRate
    exact Finset.single_le_sum (f := fun j : Fin r => ((j.val + 1).factorial : ℝ) * B * 2 ^ (j.val + 1))
      (fun j _ => by positivity) (Finset.mem_univ i)
  have hW := norm_lt_two_of_deriv_bound_uIcc hrate hd hvbound hinit hsmall
  intro n hn hnr
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  exact (norm_le_pi_norm (W t) ⟨k, by omega⟩).trans_lt hW

end RothschildStein.G1
