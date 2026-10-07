-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.SelectedCoefficientDerivative
public import RothschildStein.G4.Frames

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric

namespace RothschildStein.G4

/-- The unit-time coefficient slice retains joint smoothness
on the actual open flow patch (BB pp. 441–444). -/
theorem timeOne_coefficient_slice_contDiffAt {m n : ℕ}
    {U : Set (Fin n → ℝ)} (hU : IsOpen U) {δ : ℝ}
    (Φ : (((Fin m → ℝ) × (Fin n → ℝ)) × ℝ) → (Fin n → ℝ))
    (hsmooth : ContDiffOn ℝ (⊤ : ℕ∞) Φ ((ball 0 δ ×ˢ U) ×ˢ Ioo (-2) 2))
    {z : Fin m → ℝ} (hz : z ∈ ball 0 δ) {x : Fin n → ℝ} (hx : x ∈ U) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun a => Φ ((a, x), 1)) z := by
  have htime : (1 : ℝ) ∈ Ioo (-2 : ℝ) 2 := by constructor <;> norm_num
  exact (hsmooth.contDiffAt (((isOpen_ball.prod hU).prod isOpen_Ioo).mem_nhds
    ⟨⟨hz, hx⟩, htime⟩)).comp z
      ((contDiffAt_id.prodMk contDiffAt_const).prodMk contDiffAt_const)

/-- Joint smoothness supplies the ambient coefficient derivative
of the actual unit-time slice (BB pp. 441–444). -/
theorem timeOne_coefficient_slice_differentiableAt {m n : ℕ}
    {U : Set (Fin n → ℝ)} (hU : IsOpen U) {δ : ℝ}
    (Φ : (((Fin m → ℝ) × (Fin n → ℝ)) × ℝ) → (Fin n → ℝ))
    (hsmooth : ContDiffOn ℝ (⊤ : ℕ∞) Φ ((ball 0 δ ×ˢ U) ×ˢ Ioo (-2) 2))
    {z : Fin m → ℝ} (hz : z ∈ ball 0 δ) {x : Fin n → ℝ} (hx : x ∈ U) :
    DifferentiableAt ℝ (fun a => Φ ((a, x), 1)) z :=
  (timeOne_coefficient_slice_contDiffAt hU Φ hsmooth hz hx).differentiableAt (by simp)

/-- Holding auxiliary coefficients fixed preserves smoothness
of the actual selected-coordinate chart (BB Lemma 9.49, p. 444). -/
theorem timeOne_selected_slice_contDiffAt {m n : ℕ}
    {U : Set (Fin n → ℝ)} (hU : IsOpen U) {δ : ℝ}
    (Φ : (((Fin (n + m) → ℝ) × (Fin n → ℝ)) × ℝ) → (Fin n → ℝ))
    (hsmooth : ContDiffOn ℝ (⊤ : ℕ∞) Φ ((ball 0 δ ×ˢ U) ×ˢ Ioo (-2) 2))
    (u : Fin n → ℝ) (v : Fin m → ℝ) (hz : Fin.append u v ∈ ball 0 δ)
    {x : Fin n → ℝ} (hx : x ∈ U) :
    ContDiffAt ℝ (⊤ : ℕ∞) (fun a => Φ ((Fin.append a v, x), 1)) u := by
  have happend : ContDiff ℝ (⊤ : ℕ∞) (fun a : Fin n → ℝ => Fin.append a v) := by
    have hh : ContDiff ℝ (⊤ : ℕ∞) (fun a : Fin n → ℝ =>
        selectedCoefficientInclusion n m a + Fin.append 0 v) :=
      (selectedCoefficientInclusion n m).contDiff.add contDiff_const
    simpa only [← selectedCoefficient_append_affine] using hh
  exact (timeOne_coefficient_slice_contDiffAt hU Φ hsmooth hz hx).comp
    (g := fun a => Φ ((a, x), 1)) (f := fun a => Fin.append a v) u happend.contDiffAt

/-- Actual full-coefficient errors restrict to selected-coordinate
errors with the same weight and constant (BB Lemma 9.49, p. 444). -/
theorem selected_timeOne_derivative_frame_bound {ι : Type*} {n m : ℕ}
    (Z : ι → (Fin n → ℝ) → (Fin n → ℝ)) (w : ι → ℕ+) (B : Fin n → ι)
    (I : Fin (n + m) → ι) (hI : ∀ j, I (Fin.castAdd m j) = B j)
    (Φ : (((Fin (n + m) → ℝ) × (Fin n → ℝ)) × ℝ) → (Fin n → ℝ))
    (u : Fin n → ℝ) (v : Fin m → ℝ) (x : Fin n → ℝ)
    (hcoef : DifferentiableAt ℝ (fun a => Φ ((a, x), 1)) (Fin.append u v))
    {κ r : ℝ}
    (hfull : ∀ (i : Fin (n + m)) (ℓ : Fin n),
      |frameCoefficient Z B (fun y =>
        fderiv ℝ (fun a => Φ ((a, x), 1)) (Fin.append u v) (Pi.single i 1) - Z (I i) y)
          ℓ (Φ ((Fin.append u v, x), 1))| ≤
        κ * r ^ (((w (B ℓ) : ℕ) : ℤ) - ((w (I i) : ℕ) : ℤ))) :
    ∀ i ℓ, |frameCoefficient Z B (fun y =>
      fderiv ℝ (fun a => Φ ((Fin.append a v, x), 1)) u (Pi.single i 1) - Z (B i) y)
        ℓ (Φ ((Fin.append u v, x), 1))| ≤
      κ * r ^ (((w (B ℓ) : ℕ) : ℤ) - ((w (B i) : ℕ) : ℤ)) := by
  intro i ℓ
  have hb := hfull (Fin.castAdd m i) ℓ
  have hdir := fderiv_selected_coefficient_direction v hcoef i
  simpa only [hI, ← hdir] using hb

end RothschildStein.G4
