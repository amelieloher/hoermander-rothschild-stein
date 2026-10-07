-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.SubstitutionDifference
@[expose] public section
noncomputable section
namespace RothschildStein.G3

/-- A top-order element annihilates every positive-order element on both
sides in the cutoff quotient (BB p. 472). -/
theorem commute_of_top_order {a n : ℕ} {p : Fin a → ℕ+}
    {h g : FiniteWordAlgebra a n p} (hh : FiniteOrderAtLeast n h) (hg : FiniteOrderAtLeast 1 g) :
    Commute h g := by
  have hl : h * g = 0 := eq_zero_of_finiteOrderAtLeast_gt (finiteOrderAtLeast_mul hh hg) (by omega)
  have hr : g * h = 0 := eq_zero_of_finiteOrderAtLeast_gt (finiteOrderAtLeast_mul hg hh) (by omega)
  exact hl.trans hr.symm

/-- Changing the first positive input by a top-order term changes BCH
only by that term (BB coefficient comparison (9.80), p. 472). -/
theorem finiteBCH_top_shift_left {a n : ℕ} {p : Fin a → ℕ+} (hn : 1 ≤ n)
    {f g h : FiniteWordAlgebra a n p} (hf : FiniteOrderAtLeast 1 f)
    (hg : FiniteOrderAtLeast 1 g) (hh : FiniteOrderAtLeast n h) :
    finiteBCH (f + h) g = finiteBCH f g + h := by
  have hp := finiteOrderAtLeast_mono hh hn
  have hfh := finiteBCH_eq_add_of_commute hf hp (commute_of_top_order hh hf).symm
  have hhg := finiteBCH_eq_add_of_commute hp hg (commute_of_top_order hh hg)
  have hgh := finiteBCH_eq_add_of_commute hg hp (commute_of_top_order hh hg).symm
  have hrh := finiteBCH_eq_add_of_commute (finiteBCH_order hf hg) hp
    (commute_of_top_order hh (finiteBCH_order hf hg)).symm
  rw [← hfh, finiteBCH_assoc hf hp hg, hhg, add_comm h g, ← hgh,
    ← finiteBCH_assoc hf hg hp, hrh]

/-- The same top-order correction law holds in the second BCH input
(BB coefficient comparison (9.80), p. 472). -/
theorem finiteBCH_top_shift_right {a n : ℕ} {p : Fin a → ℕ+} (hn : 1 ≤ n)
    {f g h : FiniteWordAlgebra a n p} (hf : FiniteOrderAtLeast 1 f)
    (hg : FiniteOrderAtLeast 1 g) (hh : FiniteOrderAtLeast n h) :
    finiteBCH f (g + h) = finiteBCH f g + h := by
  have hp := finiteOrderAtLeast_mono hh hn
  rw [← finiteBCH_eq_add_of_commute hg hp (commute_of_top_order hh hg).symm,
    ← finiteBCH_assoc hf hg hp]
  exact finiteBCH_eq_add_of_commute (finiteBCH_order hf hg) hp
    (commute_of_top_order hh (finiteBCH_order hf hg)).symm
end RothschildStein.G3
