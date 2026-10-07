-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.DriftSign
public import RothschildStein.H1.OperatorHomogeneity
public import RothschildStein.H1.InterfaceDictionary
public import RothschildStein.H1.FirstCoordinate

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

@[expose] public section
noncomputable section
namespace RothschildStein.H1
variable {N q : ℕ} (G : HomogeneousGroup N)

/-- Drift reversal leaves every squared field unchanged (BB p. 254). -/
theorem StandingHypotheses.reverseDrift_horizontal (H : StandingHypotheses G q) (i : Fin q) :
    (H.reverseDrift G).fields i.succ = H.fields i.succ := by
  simp [StandingHypotheses.reverseDrift, driftSign]

/-- Drift reversal preserves the positive first-coordinate square sum (BB p. 254). -/
theorem StandingHypotheses.reverseDrift_squareSum (H : StandingHypotheses G q) :
    horizontalFirstSquareSum G (H.reverseDrift G) = horizontalFirstSquareSum G H := by
  simp only [horizontalFirstSquareSum, H.reverseDrift_horizontal G]

/-- The drift-reversed operator is the transpose of the original operator
(BB Definition 6.5, p. 254). -/
theorem StandingHypotheses.reverseDrift_operator (H : StandingHypotheses G q)
    (φ : (Fin N → ℝ) → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (x : Fin N → ℝ) :
    sumSquaresWithDrift (H.reverseDrift G).fields φ x = sumSquaresWithDriftTranspose H.fields φ x := by
  rw [H.sumSquaresTranspose_formula G φ hφ x]
  simp [sumSquaresWithDrift, StandingHypotheses.reverseDrift, driftSign, fieldDerivative]

/-- The transpose operator also has degree two (BB p. 254). -/
theorem StandingHypotheses.transpose_homogeneous (H : StandingHypotheses G q) :
    G2.IsHomogeneousOperator G (sumSquaresWithDriftTranspose H.fields) 2 := by
  intro f hf t ht x
  have h := (H.reverseDrift G).operator_homogeneous G f hf t ht x
  rw [H.reverseDrift_operator G _ (hf.comp (G2.contDiff_dilate G t)) x,
    H.reverseDrift_operator G f hf (G.dilate t x)] at h
  exact h

end RothschildStein.H1
