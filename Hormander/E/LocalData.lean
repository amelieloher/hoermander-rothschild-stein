-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.Defs.LieWordLength
public import Hormander.Interface.LieWord
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Data.Finset.Max
public import Mathlib.Tactic

@[expose] public section

namespace Hormander.E

open Hormander.Interface

noncomputable section

/-- The ordinary word-length bound for a finite frame family, with a positive
default for the empty family. The drift generator contributes one leaf through `lieWordLength`. -/
def frame_step {k N : ℕ} (w : Fin N → LieWord k) : ℕ :=
  max 1 (Finset.univ.sup fun a => lieWordLength (w a))

/-- The gain associated with the ordinary frame step. -/
def frame_gain {k N : ℕ} (w : Fin N → LieWord k) : ℝ :=
  (2 : ℝ) / 4 ^ frame_step w

/-- The maximum frame step is positive and bounds every frame word. -/
theorem frame_step_spec {k N : ℕ} (w : Fin N → LieWord k) :
    1 ≤ frame_step w ∧ ∀ a, lieWordLength (w a) ≤ frame_step w := by
  constructor
  · exact Nat.le_max_left 1 _
  · intro a
    change lieWordLength (w a) ≤ max 1 (Finset.univ.sup fun b => lieWordLength (w b))
    exact (Finset.le_sup (f := fun b => lieWordLength (w b)) (Finset.mem_univ a)).trans
      (Nat.le_max_right _ _)

/-- The gain attached to the frame is positive. -/
theorem frame_gain_pos {k N : ℕ} (w : Fin N → LieWord k) : 0 < frame_gain w := by
  unfold frame_gain
  exact div_pos (by norm_num) (by positivity)

/-- Choose a finite number of equal intermediate gains whose sum is
`m + σ`, each at most the available gain `ε`. -/
theorem iteration_parameters {m σ ε : ℝ} (hm : 0 < m) (hσ : 0 < σ) (hε : 0 < ε) :
    ∃ n : ℕ, (m + σ) / ε ≤ (n : ℝ) ∧
      0 < (m + σ) / (n : ℝ) ∧
      (m + σ) / (n : ℝ) ≤ ε ∧
      -m + (n : ℝ) * ((m + σ) / (n : ℝ)) = σ := by
  obtain ⟨n, hn⟩ := exists_nat_gt ((m + σ) / ε)
  have hsum : 0 < m + σ := add_pos hm hσ
  have hr : 0 < (m + σ) / ε := div_pos hsum hε
  have hn0 : 0 < (n : ℝ) := lt_trans hr hn
  have hmul : m + σ < (n : ℝ) * ε := (div_lt_iff₀ hε).mp hn
  refine ⟨n, le_of_lt hn, div_pos hsum hn0, ?_, ?_⟩
  · rw [div_le_iff₀ hn0]
    nlinarith
  · field_simp
    ring

/-- A positive Sobolev order above the target, leaving room for the frame gain. -/
def target_order (t : ℝ) : ℝ := max 0 t + 1

/-- The selected order is positive and its gain exceeds the requested target. -/
theorem target_order_spec {k N : ℕ} (w : Fin N → LieWord k) (t : ℝ) :
    0 < target_order t ∧ t < target_order t + frame_gain w := by
  have hε := frame_gain_pos w
  constructor
  · unfold target_order
    positivity
  · have ht : t ≤ max 0 t := le_max_right _ _
    unfold target_order
    linarith

end

end Hormander.E
