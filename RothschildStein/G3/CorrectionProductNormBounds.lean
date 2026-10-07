-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.FiniteBCHNormBounds
public import RothschildStein.G3.CorrectionProductAlgebra
@[expose] public section
noncomputable section
namespace RothschildStein.G3

/-- Each fixed factor count has a numerical norm bound on bounded inputs. -/
theorem exists_correctionProduct_norm_bound {a s : ℕ} {p : Fin a → ℕ+}
    (B : ℝ) (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ AS : List (FiniteWordAlgebra a s p),
      AS.length ≤ n → (∀ A ∈ AS, ‖A‖ ≤ B) → ‖correctionProduct AS‖ ≤ C := by
  induction n with
  | zero =>
    refine ⟨1,by norm_num,?_⟩
    intro AS hlen _
    have he : AS = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst AS
    simp [correctionProduct]
  | succ n ih =>
    obtain ⟨C,hC,hbound⟩ := ih
    obtain ⟨D,hD,hBCH⟩ := exists_finiteBCH_norm_bound (a := a) (s := s) (p := p) (max B C)
    refine ⟨D,hD,?_⟩
    intro AS hlen hAS
    cases AS with
    | nil => simpa only [correctionProduct,norm_zero] using hD.le
    | cons A AS =>
      have ht := hbound AS (by simpa using Nat.le_of_succ_le_succ hlen)
        (fun Z hZ => hAS Z (List.mem_cons_of_mem A hZ))
      exact hBCH A (correctionProduct AS)
        ((hAS A (List.mem_cons_self ..)).trans (le_max_left _ _))
        (ht.trans (le_max_right _ _))
end RothschildStein.G3
