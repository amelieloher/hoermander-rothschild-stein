-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.SelectedCoefficientDerivative
public import Mathlib.Topology.Homeomorph.Lemmas

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace RothschildStein.G4

/-- Restrict the actual full state derivative to selected
coefficient coordinates, holding the initial point and auxiliary coefficients
fixed. Joint continuity uses only a topology on the external parameter
(BB Props 9.53–9.54, p. 452). -/
theorem selected_chart_fderiv_joint_continuousOn {P E : Type*} {n m : ℕ}
    [TopologicalSpace P] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : P → ((Fin (n + m) → ℝ) × E) → E)
    {S : Set (P × ((Fin (n + m) → ℝ) × E))}
    {T : Set (P × (((Fin n → ℝ) × (Fin m → ℝ)) × E))}
    (hD : ContinuousOn (fun q => fderiv ℝ (F q.1) q.2) S)
    (hF : ∀ q ∈ S, DifferentiableAt ℝ (F q.1) q.2)
    (hmap : ∀ q ∈ T, (q.1, (Fin.append q.2.1.1 q.2.1.2, q.2.2)) ∈ S) :
    ContinuousOn
      (fun q => fderiv ℝ (fun u => F q.1 (Fin.append u q.2.1.2, q.2.2)) q.2.1.1) T := by
  let R : (Fin n → ℝ) →L[ℝ] ((Fin (n + m) → ℝ) × E) :=
    (ContinuousLinearMap.inl ℝ (Fin (n + m) → ℝ) E).comp
      (selectedCoefficientInclusion n m)
  let L := (ContinuousLinearMap.compL ℝ (Fin n → ℝ)
    ((Fin (n + m) → ℝ) × E) E).flip R
  have hinput : Continuous
      (fun q : P × (((Fin n → ℝ) × (Fin m → ℝ)) × E) =>
        (q.1, (Fin.append q.2.1.1 q.2.1.2, q.2.2))) :=
    continuous_fst.prodMk (((Fin.continuous_append n m).comp continuous_snd.fst).prodMk
      continuous_snd.snd)
  have hfull := hD.comp hinput.continuousOn hmap
  have hc := L.continuous.comp_continuousOn hfull
  apply hc.congr
  intro q hq
  have hdiff := hF _ (hmap q hq)
  have hcoef : DifferentiableAt ℝ
      (fun a : Fin (n + m) → ℝ => F q.1 (a, q.2.2)) (Fin.append q.2.1.1 q.2.1.2) :=
    (hdiff.hasFDerivAt.comp (Fin.append q.2.1.1 q.2.1.2)
      (hasFDerivAt_prodMk_left (𝕜 := ℝ) (Fin.append q.2.1.1 q.2.1.2) q.2.2)).differentiableAt
  have hslice := fderiv_parameter_slice_eq_full_comp hdiff
  change fderiv ℝ (fun u => F q.1 (Fin.append u q.2.1.2, q.2.2)) q.2.1.1 =
    (fderiv ℝ (F q.1) (Fin.append q.2.1.1 q.2.1.2, q.2.2)).comp R
  rw [fderiv_selected_coefficients q.2.1.2 hcoef, hslice]
  exact ContinuousLinearMap.comp_assoc _ _ _

end RothschildStein.G4
