-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.SignedPrimitiveCoordinates
public import RothschildStein.G3.RootTimedPrimitiveSchedules
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace RothschildStein.G3

/-- A normalized real primitive time is a retained homogeneous Lie input. -/
def timedPrimitiveLieInput {a s : ℕ} {p : Fin a → ℕ+} (b : Fin a × ℝ) :
    formalSpan a s p := b.2 • (wordLieElement [b.1] : formalSpan a s p)

theorem dilatedInputCoordinates_smul {a s : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (c t : ℝ) (f : formalSpan a s p) :
    dilatedInputCoordinates D (c • f) t = c • dilatedInputCoordinates D f t := by
  funext j
  simp only [dilatedInputCoordinates,coordinateDilation,map_smul,Pi.smul_apply,smul_eq_mul]
  ring

theorem dilatedInputCoordinates_timedPrimitive {a s : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (b : Fin a × ℝ) (t : ℝ) :
    dilatedInputCoordinates D (timedPrimitiveLieInput b) t =
      D.basis.equivFun ((t^(p b.1 : ℕ)*b.2) • (wordLieElement [b.1] : formalSpan a s p)) := by
  rw [timedPrimitiveLieInput,dilatedInputCoordinates_smul,dilatedInputCoordinates_singleton]
  rw [← map_smul,smul_smul,mul_comm b.2]
end RothschildStein.G3
