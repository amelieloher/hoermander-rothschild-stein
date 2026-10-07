-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.HomogeneousBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace RothschildStein.H1
variable {N : ℕ} (G : HomogeneousGroup N)

/-- A single constant bounds any finite family of punctured
homogeneous kernels, with the individual degrees retained
(BB Theorem 11.5(b), printed p. 538). -/
theorem finite_homogeneous_family_bound {I : Type*} [Fintype I]
    (ν : G2.HomogeneousNorm G) (f : I → (Fin N → ℝ) → ℝ) (a : I → ℝ)
    (hc : ∀ i, ContinuousOn (f i) ({(0 : Fin N → ℝ)}ᶜ))
    (hh : ∀ i, ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 → f i (G.dilate t x) = t ^ (a i) * f i x) :
    ∃ C > 0, ∀ i x, x ≠ 0 → |f i x| ≤ C * (ν x) ^ (a i) := by
  classical
  have hb (i : I) := homogeneous_bound G ν (a i) (hc i) (hh i)
  choose c hc' hb' using hb
  let C := 1 + ∑ i : I, c i
  have hsum : 0 ≤ ∑ i : I, c i := Finset.sum_nonneg (fun i _ => (hc' i).le)
  refine ⟨C, by dsimp only [C]; linarith, fun i x hx => ?_⟩
  have hi : c i ≤ ∑ j : I, c j :=
    Finset.single_le_sum (fun j _ => (hc' j).le) (Finset.mem_univ i)
  have hci : c i ≤ C := by dsimp only [C]; linarith
  exact (hb' i x hx).trans (mul_le_mul_of_nonneg_right hci
    (Real.rpow_nonneg (ν.gauge.2.1 x) _))

end RothschildStein.H1
