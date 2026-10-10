-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Semigroup.ComplexL2Extension

/-! # Real L² as a closed subspace of complex L²

The kernel of the imaginary projection is canonically equivalent to real L² and is
preserved by the componentwise extension of every real operator.
-/

@[expose] public section
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace HeatKernel
variable {α : Type*} [MeasurableSpace α] (μ : Measure α)

/-- Complex L² vectors with zero imaginary part. -/
def realL2Subspace : Submodule ℝ (Lp ℂ 2 μ) := (l2ImaginaryPart μ).ker

theorem isClosed_realL2Subspace : IsClosed (realL2Subspace μ : Set (Lp ℂ 2 μ)) :=
  (l2ImaginaryPart μ).isClosed_ker

theorem l2OfReal_realPart_of_mem {f : Lp ℂ 2 μ} (hf : f ∈ realL2Subspace μ) :
    l2OfReal μ (l2RealPart μ f) = f := by
  have hz : l2ImaginaryPart μ f = 0 := hf
  simpa only [hz, map_zero, smul_zero, add_zero] using
    l2OfReal_realPart_add_I_imaginaryPart μ f

/-- The canonical identification with the closed real subspace. -/
def realL2SubspaceEquiv : Lp ℝ 2 μ ≃L[ℝ] realL2Subspace μ where
  toFun f := ⟨l2OfReal μ f, l2ImaginaryPart_ofReal μ f⟩
  invFun f := l2RealPart μ (f : Lp ℂ 2 μ)
  map_add' f g := Subtype.ext ((l2OfReal μ).map_add f g)
  map_smul' c f := Subtype.ext ((l2OfReal μ).map_smul c f)
  left_inv f := l2RealPart_ofReal μ f
  right_inv f := Subtype.ext (l2OfReal_realPart_of_mem μ f.property)
  continuous_toFun := (l2OfReal μ).continuous.subtype_mk _
  continuous_invFun := (l2RealPart μ).continuous.comp continuous_subtype_val

theorem norm_realL2SubspaceEquiv (f : Lp ℝ 2 μ) :
    ‖realL2SubspaceEquiv μ f‖ = ‖f‖ := norm_l2OfReal μ f

theorem mapsTo_complexL2Extension_realL2Subspace (R : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ) :
    MapsTo (complexL2Extension μ R) (realL2Subspace μ) (realL2Subspace μ) := by
  intro f hf
  rw [← l2OfReal_realPart_of_mem μ hf, complexL2Extension_ofReal]
  exact l2ImaginaryPart_ofReal μ _

end HeatKernel
