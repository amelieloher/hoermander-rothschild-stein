-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PaddingFieldDefs
public import RothschildStein.P2.Hypoellipticity

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.P1

/-- Diffusion padding without drift: original diffusions are
extended independently of the added coordinates, then actual coordinate
diffusions are appended. No generator is assigned a drift role. -/
def paddingNoDriftVectorFields {q n d : ℕ}
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)) :
    Fin (q + d) → (Fin (n + d) → ℝ) → (Fin (n + d) → ℝ) :=
  Fin.addCases (fun i => paddingBaseField (d := d) (X i))
    (fun j => paddingDiffusionField (n := n) j)

/-- Original no-drift weights are preserved and every appended
diffusion has weight one. In the no-drift theorem all weights are one. -/
def paddingNoDriftWeights {q d : ℕ} (w : Fin q → ℕ+) : Fin (q + d) → ℕ+ :=
  Fin.addCases w (fun _ => 1)

/-- Each original no-drift diffusion retains its position. -/
theorem paddingNoDriftVectorFields_original {q n d : ℕ}
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)) (i : Fin q) :
    paddingNoDriftVectorFields (d := d) X (Fin.castAdd d i) =
      paddingBaseField (d := d) (X i) := by simp [paddingNoDriftVectorFields]

/-- Each new no-drift diffusion is the corresponding fiber direction. -/
theorem paddingNoDriftVectorFields_added {q n d : ℕ}
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)) (j : Fin d) :
    paddingNoDriftVectorFields (d := d) X (Fin.natAdd q j) =
      paddingDiffusionField (n := n) j := by simp [paddingNoDriftVectorFields]

/-- The no-drift padded family is precisely the diffusion part
of padding the temporary zero-drift adapter. This is a proof adapter;
its zero drift does not enter the no-drift free model. -/
theorem paddingNoDriftVectorFields_eq_zeroDrift_tail {q n d : ℕ}
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)) :
    paddingNoDriftVectorFields (d := d) X =
      fun i => paddingVectorFields (d := d) (P2.zeroDrift X) i.succ := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp [paddingNoDriftVectorFields, paddingVectorFields_original, P2.zeroDrift]
  · intro j
    simp [paddingNoDriftVectorFields, paddingVectorFields_added]

end RothschildStein.P1
