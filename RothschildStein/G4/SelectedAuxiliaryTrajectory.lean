-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.FrameReindex
public import RothschildStein.G4.TimeOneFlow

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric MeasureTheory Filter
open scoped BigOperators

namespace RothschildStein.G4

/-- The actual smooth selected-plus-auxiliary flow gives the
trajectory premises of the shifted ball inclusions, with the original
path domain and the enumerated short fields (BB Prop 9.52, p. 449). -/
theorem selectedAuxiliary_timeOneTrajectory {k n s : ℕ}
    (w : Fin k → ℕ+) (B : Fin n → ShortWord w s)
    (Z : ShortWord w s → (Fin n → ℝ) → (Fin n → ℝ))
    {Ω U : Set (Fin n → ℝ)} {δ : ℝ}
    (Φ : (((Fin (n + Fintype.card (ShortWord w s)) → ℝ) × (Fin n → ℝ)) × ℝ) →
      (Fin n → ℝ))
    (hsmooth : ContDiffOn ℝ (⊤ : ℕ∞) Φ ((ball 0 δ ×ˢ U) ×ˢ Ioo (-2) 2))
    (u : Fin n → ℝ) (v : Fin (Fintype.card (ShortWord w s)) → ℝ)
    {x : Fin n → ℝ} (hp : Fin.append u v ∈ ball 0 δ) (hx : x ∈ U)
    (hflow : Φ ((Fin.append u v, x), 0) = x ∧
      ∀ τ ∈ Ioo (-2 : ℝ) 2, Φ ((Fin.append u v, x), τ) ∈ Ω ∧
        HasDerivAt (fun t => Φ ((Fin.append u v, x), t))
          (∑ j, Fin.append u v j • Z (selectedAuxiliaryIndex w B j)
            (Φ ((Fin.append u v, x), τ))) τ) :
    let Γ := fun t => Φ ((Fin.append u v, x), t)
    AbsolutelyContinuousOnInterval Γ 0 1 ∧ MapsTo Γ (Icc (0 : ℝ) 1) Ω ∧
      Γ 0 = x ∧ Γ 1 = Φ ((Fin.append u v, x), 1) ∧
      ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) 1)), HasDerivAt Γ
        (∑ j : Fin (n + Fintype.card (ShortWord w s)), Fin.append u v j •
          Z (shortIndex w (Fin.addCases ((Fintype.equivFin (ShortWord w s)) ∘ B) id j))
            (Γ t)) t := by
  intro Γ
  have hsub : uIcc (0 : ℝ) 1 ⊆ Ioo (-2) 2 := by
    rw [uIcc_of_le zero_le_one]
    intro t ht
    constructor <;> linarith [ht.1, ht.2]
  have hcurve : ContDiffOn ℝ (⊤ : ℕ∞) Γ (Ioo (-2) 2) :=
    hsmooth.comp (contDiffOn_const.prodMk contDiffOn_id) (fun t ht => ⟨⟨hp, hx⟩, ht⟩)
  refine ⟨((hcurve.of_le (by simp)).mono hsub).absolutelyContinuousOnInterval, ?_,
    hflow.1, rfl, ?_⟩
  · intro t ht
    exact (hflow.2 t (hsub (by simpa only [uIcc_of_le zero_le_one] using ht))).1
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    simpa only [shortIndex_selectedAuxiliaryIndex] using
      (hflow.2 t (hsub (by simpa only [uIcc_of_le zero_le_one] using ht))).2

end RothschildStein.G4
