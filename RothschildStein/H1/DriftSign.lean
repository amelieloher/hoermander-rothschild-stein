-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.Standing

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

@[expose] public section
noncomputable section
namespace RothschildStein.H1
open Hormander.Interface
variable {N q : ℕ} (G : HomogeneousGroup N)

/-- The coefficient acquired by scaling the generators of a Lie word (BB p. 254). -/
def wordScale (c : Fin (q + 1) → ℝ) : LieWord q → ℝ
  | .generator i => c i
  | .bracket a b => wordScale c a * wordScale c b

/-- Generator scalings by nonzero numbers never kill a word coefficient. -/
theorem wordScale_ne_zero (c : Fin (q + 1) → ℝ) (hc : ∀ i, c i ≠ 0) (w : LieWord q) :
    wordScale c w ≠ 0 := by
  induction w with
  | generator i => exact hc i
  | bracket a b iha ihb => exact mul_ne_zero iha ihb

/-- Rescaling invariant generators multiplies each bracket word by its word coefficient
(BB p. 254; sign accounting for every bracketing). -/
theorem invariant_lieWord_scaled
    (X : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, G2.IsLeftInvariantField G (X i)) (c : Fin (q + 1) → ℝ) (w : LieWord q) :
    LieWord.eval (fun i => c i • X i) w = wordScale c w • LieWord.eval X w := by
  induction w with
  | generator i => rfl
  | bracket a b iha ihb =>
    simp only [LieWord.eval, iha, ihb, wordScale]
    have hsa : ContDiff ℝ (⊤ : ℕ∞) (LieWord.eval X a) := by
      rw [(G2.lieWord_invariant G X hX a).eq_leftField G]; exact G2.contDiff_leftField G _
    have hsb : ContDiff ℝ (⊤ : ℕ∞) (LieWord.eval X b) := by
      rw [(G2.lieWord_invariant G X hX b).eq_leftField G]; exact G2.contDiff_leftField G _
    funext x
    rw [VectorField.lieBracket_const_smul_left (hsa.differentiable (by simp)).differentiableAt,
      VectorField.lieBracket_const_smul_right (hsb.differentiable (by simp)).differentiableAt]
    simp [smul_smul]

/-- Nonzero generator rescaling preserves the origin bracket-span condition (BB p. 254). -/
theorem origin_spanning_scaled
    (X : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, G2.IsLeftInvariantField G (X i)) (c : Fin (q + 1) → ℝ)
    (hc : ∀ i, c i ≠ 0)
    (hspan : Submodule.span ℝ (Set.range (fun w : LieWord q => LieWord.eval X w 0)) = ⊤) :
    Submodule.span ℝ (Set.range (fun w : LieWord q => LieWord.eval (fun i => c i • X i) w 0)) = ⊤ := by
  let S := Submodule.span ℝ (Set.range (fun w : LieWord q => LieWord.eval (fun i => c i • X i) w 0))
  apply top_unique
  rw [← hspan]
  apply Submodule.span_le.mpr
  rintro v ⟨w, rfl⟩
  apply SetLike.mem_coe.mpr
  change LieWord.eval X w 0 ∈ S
  have hs : LieWord.eval (fun i => c i • X i) w 0 ∈ S := Submodule.subset_span ⟨w, rfl⟩
  have hscaled := S.smul_mem (wordScale c w)⁻¹ hs
  rw [invariant_lieWord_scaled G X hX c w] at hscaled
  simpa only [Pi.smul_apply, smul_smul, inv_mul_cancel₀ (wordScale_ne_zero c hc w), one_smul] using hscaled

/-- Negate just the index-zero drift. -/
def driftSign (i : Fin (q + 1)) : ℝ := if i = 0 then -1 else 1

/-- The standing class is closed under reversing the drift (BB p. 254). -/
def StandingHypotheses.reverseDrift (H : StandingHypotheses G q) : StandingHypotheses G q where
  q_pos := H.q_pos
  norm := H.norm
  fields i := driftSign i • H.fields i
  invariant i := (G2.leftInvariantSubmodule G).smul_mem _ (H.invariant i)
  homogeneous i := by
    intro t ht x
    change G.dilate t (driftSign i • H.fields i x) = _
    rw [← G2.dilationDifferential_apply G, map_smul, G2.dilationDifferential_apply G,
      H.homogeneous i t ht x]
    simp [smul_smul, mul_comm]
  horizontal_nonzero := by
    obtain ⟨i, hi⟩ := H.horizontal_nonzero
    exact ⟨i, by simpa [driftSign] using hi⟩
  span_origin := origin_spanning_scaled G H.fields H.invariant driftSign
    (by intro i; unfold driftSign; split_ifs <;> norm_num) H.span_origin

end RothschildStein.H1
