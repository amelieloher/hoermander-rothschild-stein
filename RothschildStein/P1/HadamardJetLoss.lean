-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.WeightedTaylorParameters

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory
namespace RothschildStein.P1

/-- A Hadamard coordinate factor preserves all
vanishing weighted jets after losing precisely that coordinate's weight.
This is the coefficient construction used by the weighted Taylor proof. -/
theorem hadamardFactor_weighted_jets_vanish {N : ℕ} {P : Type}
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    (G : HomogeneousGroup N) (a : ℕ)
    (F : P × (Fin N → ℝ) → ℝ) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hjet : ∀ p : P, ∀ I : List (Fin N), (I.map G.weight).sum < a →
      rsPartial I (fun u => F (p, u)) 0 = 0)
    (j : Fin N) :
    ∀ p : P, ∀ I : List (Fin N), (I.map G.weight).sum < a - G.weight j →
      rsPartial I (fun u => ∫ t in Icc (0 : ℝ) 1,
        fderiv ℝ F (p, t • u) (0, Pi.single j 1)) 0 = 0 := by
  intro p I hI
  have hg : ContDiff ℝ (⊤ : ℕ∞) (fun u : Fin N → ℝ => F (p, u)) :=
    hF.comp (contDiff_const.prodMk contDiff_id)
  have heq : (fun u => ∫ t in Icc (0 : ℝ) 1,
      fderiv ℝ F (p, t • u) (0, Pi.single j 1)) =
      (fun u : Fin N → ℝ => ∫ t in Icc (0 : ℝ) 1,
        rsPartial [j] (fun v => F (p, v)) (t • u)) := by
    funext u
    apply setIntegral_congr_fun measurableSet_Icc
    intro t ht
    exact (rsPartial_single_generic_parameter F hF p _ j).symm
  rw [heq]
  apply rsPartial_scaledIntegral_eq_zero _ (rsPartial_contDiff [j] hg)
  rw [rsPartial_append_single]
  apply hjet p
  simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero]
  omega

end RothschildStein.P1
