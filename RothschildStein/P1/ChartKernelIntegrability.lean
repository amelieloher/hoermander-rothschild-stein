-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.SingularSplitCancellation
public import RothschildStein.P1.SingularSplitEstimatesFactors
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory

namespace RothschildStein.P1

variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}

/-- Pullback of a locally integrable model kernel through the actual
input chart is integrable on every compact subset of the coordinate domain.
The proof uses the chart Jacobian and its continuous positive density factor. -/
theorem LiftedChart.integrableOn_modelKernel_comp_theta
    (C : LiftedChart w s Ω hΩ X x₀ m) (f : (Fin (n + m) → ℝ) → ℝ)
    (hf : LocallyIntegrable f volume) (ξ : Fin (n + m) → ℝ) (hξ : ξ ∈ C.U)
    (K : Set (Fin (n + m) → ℝ)) (hK : IsCompact K) (hKU : K ⊆ C.U) :
    IntegrableOn (fun η => f (C.Θ η ξ)) K := by
  have himage : IsCompact ((fun η => C.Θ η ξ) '' K) :=
    hK.image_of_continuousOn ((C.contDiffOn_Θ_fst hξ).continuousOn.mono hKU)
  have himageInt := hf.integrableOn_isCompact himage
  have hder : ∀ η ∈ K, HasFDerivWithinAt (fun η => C.Θ η ξ)
      (fderiv ℝ (fun η => C.Θ η ξ) η) K η :=
    fun η hη => (C.hasFDerivAt_Θ_fst hξ (hKU hη)).hasFDerivWithinAt
  have hweighted := (integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
    hK.measurableSet hder ((C.injOn_Θ_fst hξ).mono hKU) f).mp himageInt
  let δ : (Fin (n + m) → ℝ) → ℝ :=
    fun η => C.c ξ * (1 + C.ωm ξ (C.Θ η ξ))
  have hω : ContinuousOn (fun η => C.ωm ξ (C.Θ η ξ)) C.U :=
    C.contDiffOn_omegaMinus_theta.continuousOn.comp
      (continuousOn_const.prodMk continuousOn_id) (fun η hη => ⟨hξ, hη⟩)
  have hδ : ContinuousOn δ K :=
    (continuousOn_const.mul (continuousOn_const.add hω)).mono hKU
  have hprod := hweighted.mul_continuousOn hδ hK
  apply hprod.congr_fun _ hK.measurableSet
  intro η hη
  have hj := (C.jacobian η (hKU hη) ξ hξ).2.2.2
  rw [LiftedChart.absoluteJacobian_eq_abs_det] at hj
  have hc : C.c ξ ≠ 0 := (C.density_pos ξ hξ).ne'
  have hωne : 1 + C.ωm ξ (C.Θ η ξ) ≠ 0 :=
    (C.jacobian η (hKU hη) ξ hξ).2.1.ne'
  simp only [smul_eq_mul, hj, δ]
  field_simp [hc, hωne]

end RothschildStein.P1
