-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.KernelDerivativeSeminorm

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set
open scoped BigOperators
namespace RothschildStein.H3
variable {N : ℕ}

private theorem coordinate_single_word (i : Fin N) (l : List (Fin N))
    (hl : l.Nodup) (hi : i ∈ l) :
    l.flatMap (fun j => List.replicate ((Pi.single i 1 : Fin N → ℕ) j) j) = [i] := by
  induction l with
  | nil => simp at hi
  | cons j l ih =>
    rcases List.nodup_cons.mp hl with ⟨hjl, hnl⟩
    by_cases hji : j = i
    · subst j
      have he : l.flatMap (fun j =>
          List.replicate ((Pi.single i 1 : Fin N → ℕ) j) j) = [] := by
        apply List.flatMap_eq_nil_iff.mpr
        intro j hj
        have hne : j ≠ i := by intro he; subst j; exact hjl hj
        simp only [Pi.single_eq_of_ne hne, List.replicate_zero]
      simp only [List.flatMap_cons, Pi.single_eq_same, List.replicate_one, he,
        List.append_nil]
    · have hij : i ≠ j := fun he => hji he.symm
      have hil : i ∈ l := by simpa only [List.mem_cons, hij, false_or] using hi
      simp only [List.flatMap_cons, Pi.single_eq_of_ne hji, List.replicate_zero,
        List.nil_append, ih hnl hil]

/-- The order-one multiindex is exactly the corresponding raw
coordinate derivative in the fixed finite-word encoding. -/
theorem euclideanPartial_single_one (i : Fin N) (f : (Fin N → ℝ) → ℝ) :
    euclideanPartial (Pi.single i 1) f =
      fun x => fderiv ℝ f x (Hormander.Interface.basisVec i) := by
  have he := coordinate_single_word i (List.finRange N) (List.nodup_finRange N)
    (List.mem_finRange i)
  simp only [euclideanPartial, he, List.foldr_cons, List.foldr_nil]

/-- Every coordinate of the gradient on the unit sphere is
bounded by the shared actual finite derivative maximum Λ₁. -/
theorem coordinate_derivative_le_kernelDerivativeBound
    {G : HomogeneousGroup N} {ν T : (Fin N → ℝ) → ℝ}
    (hν : G.IsHomogeneousGauge ν) (hT : ContDiffOn ℝ (⊤ : ℕ∞) T {0}ᶜ)
    (i : Fin N) {x : Fin N → ℝ} (hx : ν x = 1) :
    |fderiv ℝ T x (Hormander.Interface.basisVec i)| ≤ kernelDerivativeBound ν T 1 := by
  have hp := (kernelDerivativeBound_properties hν hT 1).2 (Pi.single i 1)
    (by simp : (∑ j : Fin N, (Pi.single i 1 : Fin N → ℕ) j) ≤ 1) x hx
  simpa only [euclideanPartial_single_one] using hp

end RothschildStein.H3
