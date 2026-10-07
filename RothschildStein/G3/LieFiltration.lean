-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.LieSpan
@[expose] public section
noncomputable section
namespace RothschildStein.G3

/-- The associative commutator adds weighted lower orders (BB p. 525). -/
theorem finiteOrderAtLeast_lie {a s : ℕ} {p : Fin a → ℕ+} {k l : ℕ}
    {f g : FiniteWordAlgebra a s p} (hf : FiniteOrderAtLeast k f)
    (hg : FiniteOrderAtLeast l g) : FiniteOrderAtLeast (k + l) ⁅f, g⁆ := by
  rw [Ring.lie_def]
  exact finiteOrderAtLeast_sub (finiteOrderAtLeast_mul hf hg)
    (by simpa only [Nat.add_comm] using finiteOrderAtLeast_mul hg hf)

end RothschildStein.G3
