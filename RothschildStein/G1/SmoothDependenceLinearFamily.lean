-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.SmoothDependenceLinearContinuity

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric Filter
open scoped Topology NNReal

namespace RothschildStein.G1

variable {P E : Type*} [NormedAddCommGroup P]
  [LocallyCompactSpace P] [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Joint continuity of bounded linear solution families.
Uniform time Lipschitz control combines with the Grönwall parameter comparison
(BB Proposition 1.2, p. 3). -/
theorem linear_solutions_continuousOn
    {U : Set P} (hU : IsOpen U) {A : (P × ℝ) → E →L[ℝ] E}
    {W : P → ℝ → E} {T K R : ℝ} (hT : 0 < T) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hA : ContinuousOn A (U ×ˢ Icc (-T) T))
    (hAb : ∀ x ∈ U, ∀ t ∈ Icc (-T) T, ‖A (x, t)‖ ≤ K)
    (hW : ∀ x ∈ U, ∀ t ∈ Icc (-T) T,
      HasDerivWithinAt (W x) (A (x, t) (W x t)) (Icc (-T) T) t)
    (hWb : ∀ x ∈ U, ∀ t ∈ Icc (-T) T, ‖W x t‖ ≤ R)
    (hinit : ∀ x ∈ U, ∀ y ∈ U, W x 0 = W y 0) :
    ContinuousOn (fun p : P × ℝ => W p.1 p.2) (U ×ˢ Ioo (-T) T) := by
  let C : ℝ≥0 := ⟨K * R, mul_nonneg hK hR⟩
  apply continuousOn_prod_of_continuousOn_lipschitzOnWith' _ C
  · intro x hx
    apply LipschitzOnWith.mono _ Ioo_subset_Icc_self
    apply (convex_Icc (-T) T).lipschitzOnWith_of_nnnorm_hasDerivWithin_le (hW x hx)
    intro t ht
    change ‖A (x, t) (W x t)‖ ≤ K * R
    exact ((A (x, t)).le_opNorm _).trans
      (mul_le_mul (hAb x hx t ht) (hWb x hx t ht) (norm_nonneg _) hK)
  · intro t ht
    exact linear_solutions_parameter_continuousOn hU hT hR hA hAb hW hWb hinit ht

end RothschildStein.G1
