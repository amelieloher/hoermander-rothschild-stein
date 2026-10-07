-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.Frames
public import Mathlib.Topology.Instances.Real.Lemmas

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators

namespace RothschildStein.L1

/-- The determinants of finitely many continuous frames have
common bounds on a compact patch; frames nonzero throughout that patch
have a common positive lower bound (BB pp. 514–516, Proposition 10.35). -/
theorem exists_compact_frame_bounds {ι : Type*} [Fintype ι] {n : ℕ}
    {K : Set (Fin n → ℝ)} (hK : IsCompact K)
    (Z : ι → (Fin n → ℝ) → (Fin n → ℝ))
    (hZ : ∀ i, ContinuousOn (Z i) K) (F : Finset (Fin n → ι))
    (hnonzero : ∀ B ∈ F, ∀ x ∈ K, G4.frameDet Z B x ≠ 0) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧
      (∀ B x, x ∈ K → |G4.frameDet Z B x| ≤ b) ∧
      (∀ B ∈ F, ∀ x ∈ K, a ≤ |G4.frameDet Z B x|) := by
  classical
  have hd : ∀ B : Fin n → ι, ContinuousOn (G4.frameDet Z B) K := by
    intro B
    unfold G4.frameDet
    simp only [Matrix.det_apply']
    apply continuousOn_finsetSum
    intro σ hσ
    apply continuousOn_const.mul
    apply continuousOn_finsetProd
    intro j hj
    exact (continuousOn_pi.mp (hZ (B j))) (σ j)
  let f := fun (B : Fin n → ι) (x : Fin n → ℝ) =>
    if B ∈ F then (G4.frameDet Z B x)⁻¹ else 0
  have hf : ∀ B, ContinuousOn (f B) K := by
    intro B
    by_cases hB : B ∈ F
    · simp only [f, ite_eq_left hB]
      exact (hd B).inv₀ (hnonzero B hB)
    · simp only [f, ite_eq_right hB]
      exact continuousOn_const
  have hb : ∀ B : Fin n → ι, ∃ P : ℝ, 0 ≤ P ∧ ∀ x ∈ K,
      ‖G4.frameDet Z B x‖ ≤ P ∧ ‖f B x‖ ≤ P := by
    intro B
    obtain ⟨C, hC⟩ := (hK.image_of_continuousOn (hd B)).isBounded.exists_norm_le
    obtain ⟨D, hD⟩ := (hK.image_of_continuousOn (hf B)).isBounded.exists_norm_le
    refine ⟨|C| + |D|, by positivity, ?_⟩
    intro x hx
    constructor
    · exact (hC _ (mem_image_of_mem _ hx)).trans (by linarith [le_abs_self C, abs_nonneg D])
    · exact (hD _ (mem_image_of_mem _ hx)).trans (by linarith [le_abs_self D, abs_nonneg C])
  choose P hP hPb using hb
  let b := 1 + ∑ B, P B
  have hsum : 0 ≤ ∑ B, P B := Finset.sum_nonneg (fun B _ => hP B)
  have hbp : 0 < b := by dsimp [b]; linarith
  have hPb' : ∀ B, P B ≤ b := by
    intro B
    have hh := Finset.single_le_sum (fun C _ => hP C) (Finset.mem_univ B)
    dsimp [b]
    linarith
  refine ⟨b⁻¹, b, inv_pos.mpr hbp, hbp, ?_, ?_⟩
  · intro B x hx
    simpa only [Real.norm_eq_abs] using ((hPb B x hx).1.trans (hPb' B))
  · intro B hB x hx
    have hp : 0 < |G4.frameDet Z B x| := abs_pos.mpr (hnonzero B hB x hx)
    have hi : |G4.frameDet Z B x|⁻¹ ≤ b := by
      have hh := (hPb B x hx).2.trans (hPb' B)
      simpa only [f, ite_eq_left hB, norm_inv, Real.norm_eq_abs] using hh
    exact (inv_le_comm₀ hp hbp).mp hi

end RothschildStein.L1
