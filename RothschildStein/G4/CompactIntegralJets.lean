-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.CompactParameterIntegral
public import Mathlib.Analysis.Calculus.ContDiff.Bounds

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory

namespace RothschildStein.G4

universe u

/-- A full jet of a smooth compact parameter integral is bounded
by the uniform corresponding jets of its actual integrand. Differentiation
uses the proved compact-parameter derivative theorem (BB pp. 441–443). -/
theorem norm_compact_parameter_integral_jet_le {E F : Type u}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [LocallyCompactSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (n : ℕ) (G : E × ℝ → F) (hG : ContDiff ℝ (⊤ : ℕ∞) G)
    (x : E) {M : ℝ}
    (hbound : ∀ t ∈ Icc (0 : ℝ) 1,
      ‖iteratedFDeriv ℝ n (fun y => G (y, t)) x‖ ≤ M) :
    ‖iteratedFDeriv ℝ n (fun y => ∫ t in Icc (0 : ℝ) 1, G (y, t)) x‖ ≤ M := by
  induction n generalizing F with
  | zero =>
    simp only [norm_iteratedFDeriv_zero] at hbound ⊢
    simpa using norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Icc (0 : ℝ) 1)
      isCompact_Icc.measure_lt_top hbound
  | succ n ih =>
    let D : E × ℝ → E →L[ℝ] F := fun p =>
      (fderiv ℝ G p).comp (ContinuousLinearMap.inl ℝ E ℝ)
    have hfull : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ G) := hG.fderiv_right (by simp)
    have hD : ContDiff ℝ (⊤ : ℕ∞) D := hfull.clm_comp contDiff_const
    have hd : ∀ y t, HasFDerivAt (fun z => G (z, t)) (D (y, t)) y := by
      intro y t
      exact (hG.differentiable (by simp) (y, t)).hasFDerivAt.comp y
        (hasFDerivAt_prodMk_left y t)
    have hI : fderiv ℝ (fun y => ∫ t in Icc (0 : ℝ) 1, G (y, t)) =
        (fun y => ∫ t in Icc (0 : ℝ) 1, D (y, t)) := by
      funext y
      exact (RothschildStein.G1.compactParameterIntegral_hasFDerivAt
        G D hG.continuous hD.continuous hd y).fderiv
    rw [← norm_iteratedFDeriv_fderiv, hI]
    apply ih D hD
    intro t ht
    have he : (fun y => D (y, t)) = fderiv ℝ (fun y => G (y, t)) :=
      funext (fun y => (hd y t).fderiv.symm)
    rw [he, norm_iteratedFDeriv_fderiv]
    exact hbound t ht

end RothschildStein.G4
