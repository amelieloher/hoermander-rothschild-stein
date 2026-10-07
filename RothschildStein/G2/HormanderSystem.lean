-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.InvariantSpanning
public import RothschildStein.G2.HomogeneousBracket

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

@[expose] public section
noncomputable section
namespace RothschildStein.G2
open Hormander.Interface
variable {N q : ℕ} (G : HomogeneousGroup N)

/-- Weighted length of a bracket word; drift is assigned two and squared fields one
(BB Definitions 1.17, 3.64, pp. 10, 135). -/
def lieWordWeight (p : Fin (q + 1) → ℕ) : LieWord q → ℕ
  | .generator i => p i
  | .bracket a b => lieWordWeight p a + lieWordWeight p b

/-- Lie words of homogeneous invariant generators have the sum of their weights as degree
(BB Proposition 3.35, p. 114; all bracketings). -/
theorem lieWord_homogeneous (X : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ))
    (p : Fin (q + 1) → ℕ) (hXi : ∀ i, IsLeftInvariantField G (X i))
    (hXh : ∀ i, IsHomogeneousField G (X i) (p i)) (w : LieWord q) :
    IsHomogeneousField G (LieWord.eval X w) (lieWordWeight p w) := by
  induction w with
  | generator i => exact hXh i
  | bracket a b iha ihb =>
    have ha := lieWord_invariant G X hXi a
    have hb := lieWord_invariant G X hXi b
    have hsa : ContDiff ℝ (⊤ : ℕ∞) (LieWord.eval X a) := by
      rw [ha.eq_leftField G]; exact contDiff_leftField G _
    have hsb : ContDiff ℝ (⊤ : ℕ∞) (LieWord.eval X b) := by
      rw [hb.eq_leftField G]; exact contDiff_leftField G _
    simpa only [lieWordWeight, LieWord.eval, Nat.cast_add] using iha.lieBracket G ihb hsa hsb

/-- A homogeneous Hörmander system with a finite weighted bracket-span condition
(BB pp. 124–125, 135–136). Index zero is the possibly zero drift. -/
structure HomogeneousHormanderSystem (q : ℕ) where
  q_pos : 0 < q
  fields : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ)
  invariant : ∀ i, IsLeftInvariantField G (fields i)
  homogeneous : ∀ i, IsHomogeneousField G (fields i) (if i = 0 then 2 else 1)
  step : ℕ
  span_origin : Submodule.span ℝ (Set.range (fun w :
      {w : LieWord q // lieWordWeight (fun i => if i = 0 then 2 else 1) w ≤ step} =>
      LieWord.eval fields w.1 0)) = ⊤

end RothschildStein.G2
