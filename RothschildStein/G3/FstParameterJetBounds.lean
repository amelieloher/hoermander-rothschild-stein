-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.ParameterProjectionJets
public import RothschildStein.G3.FixedStateInputJets
@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace RothschildStein.G3

theorem norm_fst_pullback_jet_le
    {P E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Ω : Set P} (hΩ : IsOpen Ω) {Y : P → F}
    (hY : ContDiffOn ℝ (⊤ : ℕ∞) Y Ω) (n : ℕ)
    (q : P × E) (hq : q.1 ∈ Ω) :
    ‖iteratedFDeriv ℝ n (fun z : P × E => Y z.1) q‖ ≤ ‖iteratedFDeriv ℝ n Y q.1‖ := by
  let L := ContinuousLinearMap.fst ℝ P E
  have hpre : IsOpen (L ⁻¹' Ω) := hΩ.preimage L.continuous
  have he := L.iteratedFDerivWithin_comp_right hY hΩ.uniqueDiffOn hpre.uniqueDiffOn hq (i := n) (by simp)
  rw [iteratedFDerivWithin_of_isOpen n hpre hq] at he
  change iteratedFDeriv ℝ n (Y ∘ L) q =
    (iteratedFDerivWithin ℝ n Y Ω q.1).compContinuousLinearMap (fun _ => L) at he
  rw [iteratedFDerivWithin_of_isOpen n hΩ hq] at he
  change ‖iteratedFDeriv ℝ n (Y ∘ L) q‖ ≤ _
  rw [he]
  apply ((iteratedFDeriv ℝ n Y q.1).norm_compContinuousLinearMap_le (fun _ => L)).trans
  have hp : (∏ _ : Fin n, ‖L‖) ≤ 1 :=
    Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => ContinuousLinearMap.norm_fst_le ℝ P E)
  exact mul_le_of_le_one_right (norm_nonneg _) hp

theorem norm_variable_state_parameter_jet_le {P E F : Type*}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : P → F) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (q : P × E)
    {n : ℕ} (hn : 1 ≤ n) {A : ℝ} (hA : 1 ≤ A)
    (hjet : ‖iteratedFDeriv ℝ n f q.1‖ ≤ A) :
    ‖iteratedFDeriv ℝ n (fun w : P × E => (f w.1,w.2)) q‖ ≤ A := by
  have hs : ContDiffAt ℝ (⊤ : ℕ∞) (fun w : P × E => f w.1) q :=
    (hf.comp contDiff_fst).contDiffAt
  rw [iteratedFDeriv_prodMk hs
    (contDiffAt_snd (n := (⊤ : ℕ∞))) (by simp),ContinuousMultilinearMap.opNorm_prod]
  apply max_le
  · exact (norm_fst_pullback_jet_le isOpen_univ hf.contDiffOn n q (mem_univ _)).trans hjet
  · obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [Nat.add_comm 1 k]
    exact ((G4.norm_positive_jet_clm_le (ContinuousLinearMap.snd ℝ P E) q k).trans
      (ContinuousLinearMap.norm_snd_le ℝ P E)).trans hA
end RothschildStein.G3
