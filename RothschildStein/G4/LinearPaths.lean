-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.LocalFrame
public import RothschildStein.G4.AuxiliaryControl
public import Mathlib.Analysis.Calculus.Deriv.AffineMap
public import Mathlib.Analysis.Calculus.AddTorsor.AffineMap

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped BigOperators Topology ENNReal

namespace RothschildStein.G4

/-- Linear paths in a controlled frame buffer give actual measurable
short-field controls with the weighted scale bound. This is the local
Euclidean-to-auxiliary topology construction (BB Proposition 9.7, p. 403). -/
theorem controlDistance_lineMap_le {m n s : ℕ} {Ω K : Set (Fin n → ℝ)}
    {Z : Fin m → (Fin n → ℝ) → (Fin n → ℝ)}
    (hZ : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (Z j) Ω)
    (w : Fin m → ℕ+) (hw : ∀ j, (w j : ℕ) ≤ s)
    (B : Fin n → Fin m) (hK : Convex ℝ K) (hKΩ : K ⊆ Ω)
    (hB : ∀ z ∈ K, frameDet Z B z ≠ 0) {C : ℝ}
    (hbound : ∀ z ∈ K, ∀ i (v : Fin n → ℝ),
      |frameCoefficient Z B (fun _ => v) i z| ≤ C * ‖v‖)
    {x y : Fin n → ℝ} (hx : x ∈ K) (hy : y ∈ K)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (hcost : C * ‖y - x‖ ≤ r ^ s) :
    controlDistance Ω w Z x y ≤ ENNReal.ofReal r := by
  let γ : ℝ → (Fin n → ℝ) := AffineMap.lineMap x y
  have hγK : MapsTo γ (Icc 0 1) K := hK.mapsTo_lineMap hx hy
  let a := fun i t => frameCoefficient Z B (fun _ => y - x) i (γ t)
  have hc : ∀ i, ContinuousOn (a i) (Icc 0 1) := by
    intro i
    exact (frameCoefficient_contDiffOn hZ contDiffOn_const B i).continuousOn.comp
      (AffineMap.contDiff_lineMap x y (n := 1)).continuous.continuousOn
      (fun t ht => ⟨hKΩ (hγK ht), hB (γ t) (hγK ht)⟩)
  obtain ⟨L, hL⟩ := (AffineMap.contDiff_lineMap x y (n := 1)).contDiffOn.exists_lipschitzOnWith
    one_ne_zero (convex_Icc (0 : ℝ) 1) isCompact_Icc
  have hac : AbsolutelyContinuousOnInterval γ 0 1 :=
    (show LipschitzOnWith L γ (uIcc 0 1) by simpa only [uIcc_of_le zero_le_one] using hL).absolutelyContinuousOnInterval
  have hcurve : isControlledCurve Ω (fun i => w (B i)) (fun i => Z (B i)) r γ := by
    refine ⟨hr, hac, fun t ht => hKΩ (hγK ht), a,
      fun i => (hc i).aemeasurable measurableSet_Icc, ?_⟩
    apply ae_restrict_of_forall_mem measurableSet_Icc
    intro t ht
    refine ⟨fun i => ?_, ?_⟩
    · have hz := zpow_le_zpow_right_of_le_one₀ hr hr1
        (show (((w (B i) : ℕ) : ℤ)) ≤ (s : ℤ) by exact_mod_cast hw (B i))
      exact ((hbound (γ t) (hγK ht) i (y - x)).trans hcost).trans (by
        simpa only [zpow_natCast] using hz)
    · have hrep := frame_representation Z B (fun _ => y - x) (hB (γ t) (hγK ht))
      rw [← hrep]
      exact AffineMap.hasDerivAt_lineMap
  have he : Function.Injective B := by
    have hunit : IsUnit (frameMatrix Z B x) :=
      (Matrix.isUnit_iff_isUnit_det (frameMatrix Z B x)).mpr (isUnit_iff_ne_zero.mpr (hB x hx))
    have hli : LinearIndependent ℝ (fun i => Z (B i) x) :=
      Matrix.linearIndependent_cols_of_isUnit hunit
    intro i j hij
    exact hli.injective (congrArg (fun k => Z k x) hij)
  have hext := isControlledCurve_extend B he (fun _ => rfl) (fun _ => rfl) hcurve
  have hd := G1.controlDistance_le_of_curve hext
  simpa only [γ, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one] using hd

end RothschildStein.G4
