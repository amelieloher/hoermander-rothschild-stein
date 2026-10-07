-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PaddingCoordinates
public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.Analysis.Calculus.ContDiff.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.P1

/-- The product-coordinate version of a joined-coordinate
open set, using the actual continuous linear coordinate equivalence. -/
def paddingProductOpen {n d : ℕ} (U : Opens (Fin (n + d) → ℝ)) :
    Opens ((Fin n → ℝ) × (Fin d → ℝ)) :=
  Opens.comap ⟨(paddingCoordinates n d).symm,
    (paddingCoordinates n d).symm.continuous⟩ U

/-- Pull an actual joined-coordinate test back to the product
carrier. Smoothness and compact support are preserved by the coordinate
equivalence, without extending coefficients or enlarging the domain. -/
def paddingTestToProduct {n d : ℕ} {B : Type*}
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    (U : Opens (Fin (n + d) → ℝ)) (φ : _root_.TestFunction U B ⊤) :
    _root_.TestFunction (paddingProductOpen U) B ⊤ where
  toFun p := φ ((paddingCoordinates n d).symm p)
  contDiff' := φ.contDiff.comp (paddingCoordinates n d).symm.contDiff
  hasCompactSupport' := φ.hasCompactSupport.comp_homeomorph
    (paddingCoordinates n d).symm.toHomeomorph
  tsupport_subset' := by
    intro p hp
    exact φ.tsupport_subset (tsupport_comp_subset_preimage (φ : (Fin (n + d) → ℝ) → B)
      (paddingCoordinates n d).symm.continuous hp)

/-- The transported test is evaluated at `joinPoint`. -/
theorem paddingTestToProduct_apply {n d : ℕ} {B : Type*}
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    (U : Opens (Fin (n + d) → ℝ)) (φ : _root_.TestFunction U B ⊤)
    (x : Fin n → ℝ) (z : Fin d → ℝ) :
    paddingTestToProduct U φ (x, z) = φ (joinPoint x z) := by
  change φ (paddingJoinCLM n d (x, z)) = _
  rw [paddingJoinCLM_apply]

/-- Quantitative control of every derivative under the same
coordinate transport. -/
theorem norm_iteratedFDeriv_paddingJoin_le {n d : ℕ} {B : Type*}
    [NormedAddCommGroup B] [NormedSpace ℝ B]
    {φ : (Fin (n + d) → ℝ) → B}
    (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (i : ℕ)
    (p : (Fin n → ℝ) × (Fin d → ℝ)) :
    ‖iteratedFDeriv ℝ i (φ ∘ paddingJoinCLM n d) p‖ ≤
      ‖iteratedFDeriv ℝ i φ (paddingJoinCLM n d p)‖ * ‖paddingJoinCLM n d‖ ^ i := by
  rw [(paddingJoinCLM n d).iteratedFDeriv_comp_right hφ p (by simp)]
  simpa using (iteratedFDeriv ℝ i φ (paddingJoinCLM n d p)).norm_compContinuousLinearMap_le
    (fun _ : Fin i => paddingJoinCLM n d)

end RothschildStein.P1
