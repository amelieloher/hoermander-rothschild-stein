-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.LinearReparametrizedJets

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace RothschildStein.G4

/-- A normalized full joint coefficient/initial-point jet bound
converts to an unscaled bound with precisely the inverse scale to the
jet order. This uses the exact derivative under linear reparametrization,
not differentiation of an inequality (BB Lemma 9.48, pp. 441–443). -/
theorem norm_unscaled_coefficient_jet_le {P E F : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {S : Set (P × E)} (hS : IsOpen S) {f : P × E → F}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f S) (z : P) {x : E} (hx : (z, x) ∈ S)
    {δ M : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hM : 0 ≤ M) (n : ℕ)
    (hjet : ‖iteratedFDeriv ℝ n
      (fun p : P × E => f (z + δ • p.1, p.2)) (0, x)‖ ≤ M) :
    ‖iteratedFDeriv ℝ n f (z, x)‖ ≤ M * δ⁻¹ ^ n := by
  let A : P × E → P × E := fun p => (z + δ • p.1, p.2)
  let T := A ⁻¹' S
  have hAc : Continuous A := by dsimp [A]; fun_prop
  have hT : IsOpen T := hS.preimage hAc
  let g : P × E → F := fun p => f (A p)
  have hg : ContDiffOn ℝ (⊤ : ℕ∞) g T :=
    hf.comp (by fun_prop) (fun p hp => hp)
  let L : (P × E) →L[ℝ] (P × E) :=
    (δ⁻¹ • ContinuousLinearMap.fst ℝ P E).prod (ContinuousLinearMap.snd ℝ P E)
  have hLzero : L (0, x) = (0, x) := by simp [L]
  have hp : L (0, x) ∈ T := by
    rw [hLzero]
    change (z + δ • 0, x) ∈ S
    simpa only [smul_zero, add_zero] using hx
  have hj : ‖iteratedFDeriv ℝ n g (L (0, x))‖ ≤ M := by
    rw [hLzero]
    exact hjet
  have hinv : 1 ≤ δ⁻¹ := (one_le_inv₀ hδ).mpr hδ1
  have hL : ‖L‖ ≤ δ⁻¹ := by
    apply ContinuousLinearMap.opNorm_le_bound L (inv_nonneg.mpr hδ.le)
    intro p
    change ‖(δ⁻¹ • p.1, p.2)‖ ≤ δ⁻¹ * ‖p‖
    rw [Prod.norm_def, max_le_iff]
    constructor
    · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hδ)]
      exact mul_le_mul_of_nonneg_left (norm_fst_le p) (inv_nonneg.mpr hδ.le)
    · exact (norm_snd_le p).trans (le_mul_of_one_le_left (norm_nonneg p) hinv)
  have hh := RothschildStein.G1.norm_local_linear_reparametrized_jet_le hT hg L
    (x := (0, x)) hp n hM hj hL
  have heq : g ∘ L = (fun p : P × E => f ((z, 0) + p)) := by
    funext p
    rcases p with ⟨p, y⟩
    simp [g, A, L, smul_smul, hδ.ne']
  rw [heq, iteratedFDeriv_comp_add_left] at hh
  simpa only [Prod.mk_add_mk, add_zero, zero_add] using hh

end RothschildStein.G4
