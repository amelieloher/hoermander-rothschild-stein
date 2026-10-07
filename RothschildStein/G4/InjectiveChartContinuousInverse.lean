-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.ActualChartLocalHomeomorph
public import Mathlib.Topology.OpenPartialHomeomorph.Basic

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Function Topology

namespace RothschildStein.G4

/-- An injective actual nonsingular chart has a continuous inverse
on its image, with both inverse identities and range proved. -/
theorem exists_continuous_inverse_of_actual_chart_injective {n : ℕ}
    {U : Set (Fin n → ℝ)} (hU : IsOpen U) (hne : U.Nonempty)
    (G : (Fin n → ℝ) → (Fin n → ℝ))
    (hG : ContDiffOn ℝ (⊤ : ℕ∞) G U)
    (hjac : ∀ u ∈ U, Matrix.det (coordinateDerivativeMatrix (fderiv ℝ G u)) ≠ 0)
    (hinj : InjOn G U) :
    ∃ Ψ : (Fin n → ℝ) → (Fin n → ℝ), ContinuousOn Ψ (G '' U) ∧
      (∀ y ∈ G '' U, Ψ y ∈ U ∧ G (Ψ y) = y) ∧
      ∀ u ∈ U, Ψ (G u) = u := by
  let chartDomainNonempty : Nonempty U := hne.to_subtype
  let p : U → (Fin n → ℝ) := fun u => G u.val
  have hlocal := isLocalHomeomorphOn_of_actual_jacobian hU G hG hjac
  have hp : IsLocalHomeomorph p :=
    isLocalHomeomorph_iff_isLocalHomeomorphOn_univ.mpr
      (hlocal.comp hU.isOpenEmbedding_subtypeVal.isLocalHomeomorph.isLocalHomeomorphOn
        (fun u _ => u.property))
  have hpinj : Injective p := fun u v huv => Subtype.ext (hinj u.property v.property huv)
  have hopen := hp.isOpenEmbedding_of_injective hpinj
  let e := hopen.toOpenPartialHomeomorph p
  let Ψ : (Fin n → ℝ) → (Fin n → ℝ) := fun y => (e.symm y).val
  have himage : G '' U = range p := by
    ext y
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨⟨u, hu⟩, rfl⟩
    · rintro ⟨u, rfl⟩
      exact ⟨u.val, u.property, rfl⟩
  refine ⟨Ψ, ?_, ?_, ?_⟩
  · have hcont : ContinuousOn Ψ e.target :=
      continuous_subtype_val.comp_continuousOn e.symm.continuousOn
    simpa only [e, hopen.toOpenPartialHomeomorph_target, ← himage] using hcont
  · intro y hy
    exact ⟨(e.symm y).property, hopen.toOpenPartialHomeomorph_right_inv p (himage ▸ hy)⟩
  · intro u hu
    exact congrArg Subtype.val (hopen.toOpenPartialHomeomorph_left_inv (f := p) (x := ⟨u, hu⟩))

end RothschildStein.G4
