-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.FiniteLieFieldDilation
public import RothschildStein.G3.ExponentialFlowSmoothBase
@[expose] public section
noncomputable section
namespace RothschildStein.G3

def dilatedInputCoordinates {a s : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (f : formalSpan a s p) (δ : ℝ) :
    Fin (freeDimension a s p) → ℝ :=
  coordinateDilation D.weight δ (D.basis.equivFun f)

theorem dilatedInputCoordinates_contDiff {a s : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (f : formalSpan a s p) :
    ContDiff ℝ (⊤ : ℕ∞) (dilatedInputCoordinates D f) := by
  apply contDiff_pi.mpr
  intro j
  exact (contDiff_id.pow (D.weight j)).mul contDiff_const

theorem dilatedInputCoordinates_zero {a s : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (f : formalSpan a s p) :
    dilatedInputCoordinates D f 0 = 0 := by
  funext j
  simp only [dilatedInputCoordinates,coordinateDilation,
    zero_pow (Nat.ne_of_gt (D.weight_pos j)),zero_mul,Pi.zero_apply]

theorem dilatedInputCoordinates_eq {a s : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (f : formalSpan a s p) (δ : ℝ) :
    dilatedInputCoordinates D f δ = D.basis.equivFun
      ⟨finiteDilate δ f.val, finiteDilate_mem_formalSpan δ f.property⟩ :=
  (basis_equivFun_dilated D δ f).symm
end RothschildStein.G3
