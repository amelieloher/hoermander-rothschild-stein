-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.FrameFlowDerivative
public import RothschildStein.L1.FrameValueEquiv
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace RothschildStein.L1

/-- The coefficient/time rescaling of an actual local frame flow. The
arguments are the base point followed by the canonical coefficients. -/
def canonicalFrameMap {N : ℕ} (a : ℝ)
    (Φ : (((Fin N → ℝ) × (Fin N → ℝ)) × ℝ) → (Fin N → ℝ))
    (q : (Fin N → ℝ) × (Fin N → ℝ)) : Fin N → ℝ :=
  Φ ((a⁻¹ • q.2,q.1),a)

/-- Time rescaling cancels the flow time in the coefficient
Jacobian, leaving the actual tangent frame as in BB (10.16). -/
theorem canonicalFrameMap_hasFDerivAt {N : ℕ} {a : ℝ} (ha : a ≠ 0)
    (Φ : (((Fin N → ℝ) × (Fin N → ℝ)) × ℝ) → (Fin N → ℝ))
    (x : Fin N → ℝ) (B : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ))
    (hd : HasFDerivAt (fun q => Φ (q,a))
      ((a • B).coprod (ContinuousLinearMap.id ℝ _)) (0,x)) :
    HasFDerivAt (canonicalFrameMap a Φ)
      ((ContinuousLinearMap.id ℝ _).coprod B) (x,0) := by
  let T : ((Fin N → ℝ) × (Fin N → ℝ)) →L[ℝ]
      ((Fin N → ℝ) × (Fin N → ℝ)) :=
    (a⁻¹ • ContinuousLinearMap.snd ℝ _ _).prod (ContinuousLinearMap.fst ℝ _ _)
  have ht : T (x,0) = (0,x) := by simp [T]
  have hdT : HasFDerivAt (fun q => Φ (q,a))
      ((a • B).coprod (ContinuousLinearMap.id ℝ _)) (T (x,0)) := by
    rw [ht]; exact hd
  have hh := hdT.comp (x,0) T.hasFDerivAt
  have he : ((a • B).coprod (ContinuousLinearMap.id ℝ _)).comp T =
      (ContinuousLinearMap.id ℝ _).coprod B := by
    apply ContinuousLinearMap.ext
    intro q
    simp [T,smul_smul,ha,add_comm]
  rw [he] at hh
  exact hh
end RothschildStein.L1
