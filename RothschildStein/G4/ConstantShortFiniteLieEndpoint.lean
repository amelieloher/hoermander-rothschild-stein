-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.ShortCombinationCoordinates
public import RothschildStein.G4.ACFlowUniqueness
public import RothschildStein.G3.ExponentialFlowMaps

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped BigOperators NNReal
namespace RothschildStein.G4
open G3

/-- The finite Lie target corresponding to actual finite-coordinate
constant short-field controls. -/
def shortCoordinateFormalTarget {m s : ℕ} {w : Fin m → ℕ+}
    (a : Fin (Fintype.card (ShortWord w s)) → ℝ) : formalSpan m s w :=
  normalizedWordTarget (shortWordCoefficients
    (fun I => a (Fintype.equivFin (ShortWord w s) I)))

/-- A genuine AC constant short-control curve and the actual
finite Lie flow have the same endpoint on a common compact buffer.
The Lipschitz bound is derived from smoothness on that buffer, and the
formal target is identified with the actual short fields pointwise
(BB pp. 459–460). -/
theorem constant_short_curve_finiteLie_endpoint {m n s : ℕ} {w : Fin m → ℕ+}
    (D : FreeModelData m s w) {Ω U : Set (Fin n → ℝ)} (hΩ : IsOpen Ω)
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (a : Fin (Fintype.card (ShortWord w s)) → ℝ)
    {z : Fin n → ℝ} {R σ : ℝ} (hRΩ : closedBall z R ⊆ Ω)
    (γ : ℝ → (Fin n → ℝ)) (hac : AbsolutelyContinuousOnInterval γ 0 1)
    (hγ : MapsTo γ (Icc 0 1) (closedBall z R))
    (hd : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) 1)),
      HasDerivAt γ (∑ j, a j • shortField w X (shortIndex w j) (γ t)) t)
    (Φ : (((Fin (freeDimension m s w) → ℝ) × (Fin n → ℝ)) × ℝ) → (Fin n → ℝ))
    (hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ ((ball 0 σ ×ˢ U) ×ˢ Ioo (-2) 2))
    (hcoords : D.basis.equivFun (shortCoordinateFormalTarget a) ∈ ball 0 σ)
    (hx : γ 0 ∈ U)
    (hinit : Φ ((D.basis.equivFun (shortCoordinateFormalTarget a), γ 0), 0) = γ 0)
    (hODE : ∀ t ∈ Ioo (-2 : ℝ) 2,
      Φ ((D.basis.equivFun (shortCoordinateFormalTarget a), γ 0), t) ∈ closedBall z R ∧
      HasDerivAt (fun v => Φ ((D.basis.equivFun (shortCoordinateFormalTarget a), γ 0), v))
        (finiteLieField D X (shortCoordinateFormalTarget a)
          (Φ ((D.basis.equivFun (shortCoordinateFormalTarget a), γ 0), t))) t) :
    γ 1 = finiteLieTimeOneMap Φ (D.basis.equivFun (shortCoordinateFormalTarget a), γ 0) := by
  let W := fun y : Fin n → ℝ => ∑ j, a j • shortField w X (shortIndex w j) y
  have hW : ContDiffOn ℝ (⊤ : ℕ∞) W Ω := by
    apply ContDiffOn.sum
    intro j _hj
    exact (shortField_contDiffOn hΩ hX (shortIndex w j)).const_smul (a j)
  have hW1 : ContDiffOn ℝ 1 W (closedBall z R) := (hW.of_le (by simp)).mono hRΩ
  obtain ⟨L, hLip⟩ := hW1.exists_lipschitzOnWith one_ne_zero
    (convex_closedBall z R) (isCompact_closedBall z R)
  have hsub : Icc (0 : ℝ) 1 ⊆ Ioo (-2) 2 := by
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hsmooth : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun t => Φ ((D.basis.equivFun (shortCoordinateFormalTarget a), γ 0), t)) (Ioo (-2) 2) :=
    hΦ.comp (contDiffOn_const.prodMk contDiffOn_id) (fun t ht => ⟨⟨hcoords, hx⟩, ht⟩)
  have hderiv : ∀ t ∈ Ico (0 : ℝ) 1,
      HasDerivAt (fun v => Φ ((D.basis.equivFun (shortCoordinateFormalTarget a), γ 0), v))
        (W (Φ ((D.basis.equivFun (shortCoordinateFormalTarget a), γ 0), t))) t := by
    intro t ht
    have htime := hsub ⟨ht.1, ht.2.le⟩
    have hfield := finiteLieField_short_coordinate_combination D ⟨Ω, hΩ⟩ X hX a
      (hRΩ (hODE t htime).1)
    have hh := (hODE t htime).2
    rw [show finiteLieField D X (shortCoordinateFormalTarget a)
      (Φ ((D.basis.equivFun (shortCoordinateFormalTarget a), γ 0), t)) =
      W (Φ ((D.basis.equivFun (shortCoordinateFormalTarget a), γ 0), t)) from hfield] at hh
    exact hh
  have he := ac_integralCurve_eqOn hLip (hW.continuousOn.mono hRΩ) hac hγ hd
    (hsmooth.continuousOn.mono hsub) (fun t ht => (hODE t (hsub ht)).1) hderiv hinit.symm
  exact he ⟨zero_le_one, le_rfl⟩

end RothschildStein.G4
