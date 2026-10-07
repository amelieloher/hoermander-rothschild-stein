-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.SelectedAuxiliaryFamily
public import RothschildStein.G4.PartialParameterJets

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open scoped BigOperators

namespace RothschildStein.G4

/-- Inclusion of the selected coefficients into the full selected
plus auxiliary coefficient vector (BB p. 444). -/
def selectedCoefficientInclusion (n m : ℕ) :
    (Fin n → ℝ) →L[ℝ] (Fin (n + m) → ℝ) :=
  ContinuousLinearMap.pi (Fin.addCases (fun i => ContinuousLinearMap.proj i) (fun _ => 0))

/-- Holding auxiliary coefficients fixed makes the full coefficient
map affine with the exact selected inclusion as its linear part. -/
theorem selectedCoefficient_append_affine {n m : ℕ} (u : Fin n → ℝ) (v : Fin m → ℝ) :
    Fin.append u v = selectedCoefficientInclusion n m u + Fin.append 0 v := by
  ext j
  refine Fin.addCases ?_ ?_ j
  · intro i; simp [selectedCoefficientInclusion, Fin.append]
  · intro i; simp [selectedCoefficientInclusion, Fin.append]

/-- A selected coordinate unit vector is the corresponding full
coefficient unit vector, with no contribution in the auxiliary block. -/
theorem selectedCoefficientInclusion_single {n m : ℕ} (i : Fin n) :
    selectedCoefficientInclusion n m (Pi.single i 1) =
      Pi.single (Fin.castAdd m i) 1 := by
  ext j
  refine Fin.addCases ?_ ?_ j
  · intro k
    simp [selectedCoefficientInclusion, Pi.single_apply]
  · intro k
    have hk : Fin.natAdd n k ≠ Fin.castAdd m i := by
      intro he
      have hv := congrArg Fin.val he
      change n + k.val = i.val at hv
      omega
    simp [selectedCoefficientInclusion, hk]

/-- The actual selected-coordinate derivative is the actual full
coefficient derivative restricted to the selected inclusion. -/
theorem fderiv_selected_coefficients {n m : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : (Fin (n + m) → ℝ) → E} {u : Fin n → ℝ} (v : Fin m → ℝ)
    (hF : DifferentiableAt ℝ F (Fin.append u v)) :
    fderiv ℝ (fun a => F (Fin.append a v)) u =
      (fderiv ℝ F (Fin.append u v)).comp (selectedCoefficientInclusion n m) := by
  have ha : HasFDerivAt (fun a => Fin.append a v) (selectedCoefficientInclusion n m) u := by
    have hb := (selectedCoefficientInclusion n m).hasFDerivAt (x := u)
    simpa only [← selectedCoefficient_append_affine] using hb.add_const (Fin.append 0 v)
  exact (hF.hasFDerivAt.comp u ha).fderiv

/-- In a selected direction, the chart derivative equals the full
coefficient derivative in the matching selected-plus-auxiliary slot. -/
theorem fderiv_selected_coefficient_direction {n m : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : (Fin (n + m) → ℝ) → E} {u : Fin n → ℝ} (v : Fin m → ℝ)
    (hF : DifferentiableAt ℝ F (Fin.append u v)) (i : Fin n) :
    fderiv ℝ (fun a => F (Fin.append a v)) u (Pi.single i 1) =
      fderiv ℝ F (Fin.append u v) (Pi.single (Fin.castAdd m i) 1) := by
  rw [fderiv_selected_coefficients v hF]
  change (fderiv ℝ F (Fin.append u v))
    (selectedCoefficientInclusion n m (Pi.single i 1)) = _
  rw [selectedCoefficientInclusion_single]

end RothschildStein.G4
