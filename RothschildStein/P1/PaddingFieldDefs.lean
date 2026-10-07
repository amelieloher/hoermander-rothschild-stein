-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PaddingCoordinates
public import Hormander.Interface.BasisVec

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.P1

/-- Extend an original field independently of the added
coordinates, with zero components in those coordinates. -/
def paddingBaseField {n d : ℕ} (X : (Fin n → ℝ) → (Fin n → ℝ)) :
    (Fin (n + d) → ℝ) → (Fin (n + d) → ℝ) :=
  fun ξ => joinPoint (X (paddingBaseCLM n d ξ)) 0

/-- Each appended field is an actual diffusion direction,
not a zero generator or padding of an existing group. -/
def paddingDiffusionField {n d : ℕ} (j : Fin d) :
    (Fin (n + d) → ℝ) → (Fin (n + d) → ℝ) :=
  fun _ => Hormander.Interface.basisVec (Fin.natAdd n j)

/-- The drift stays at index zero. Original diffusions come
next, followed by the added diffusion fields. -/
def paddingVectorFields {q n d : ℕ}
    (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ)) :
    Fin (q + d + 1) → (Fin (n + d) → ℝ) → (Fin (n + d) → ℝ) :=
  Fin.cases (paddingBaseField (d := d) (X 0))
    (Fin.addCases (fun i => paddingBaseField (d := d) (X i.succ))
      (fun j => paddingDiffusionField (n := n) j))

/-- The padded drift is exactly the original lifted drift. -/
theorem paddingVectorFields_zero {q n d : ℕ}
    (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ)) :
    paddingVectorFields (d := d) X 0 = paddingBaseField (d := d) (X 0) := rfl

/-- Original diffusion indices retain their relative order. -/
theorem paddingVectorFields_original {q n d : ℕ}
    (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ)) (i : Fin q) :
    paddingVectorFields (d := d) X (Fin.castAdd d i).succ =
      paddingBaseField (d := d) (X i.succ) := by simp [paddingVectorFields]

/-- Each final diffusion index is the corresponding nonzero
coordinate direction in the added block. -/
theorem paddingVectorFields_added {q n d : ℕ}
    (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ)) (j : Fin d) :
    paddingVectorFields (d := d) X (Fin.natAdd q j).succ =
      paddingDiffusionField (n := n) j := by simp [paddingVectorFields]

end RothschildStein.P1
