-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Bridge.ParabolicValueIntegrability
public import HeatKernel.Geometry.CoordinateBall
public import HeatKernel.Poincare.LocalIntegrability
public import HeatKernel.Poincare.BallExhaustion
public import HeatKernel.Moser.BombieriGiustiCylinders
public import HeatKernel.Moser.WeakSolutionAffine
import Mathlib.Tactic
import all Mathlib.Basic.Real.Basic

/-! # Finite earlier moments from local weak energy bounds

The earlier outer iteration cylinder has compact closure inside the full
Harnack cylinder. The defining local square-integrability bounds therefore
give every positive moment of order at most two, including after an affine
perturbation and exponential rescaling.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace RothschildStein
open scoped ENNReal
namespace HeatKernel
set_option backward.isDefEq.respectTransparency false

/-- Local L² bounds discharge the earlier finite-moment input for all positive
exponents at most two. No sign or coefficient regularity assumption is needed. -/
theorem IsLocalWeakSolution.lintegral_shifted_harnackEarlier_rpow_ne_top
    {N q : ℕ} (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    {a : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ}
    (x : Fin N → ℝ) (t : ℝ) {r p : ℝ} (hr : 0 < r) (hp : 0 < p) (hp2 : p ≤ 2)
    {u : ℝ → (Fin N → ℝ) → ℝ}
    (hu : IsLocalWeakSolution G hq hqpos hw hspan a
      ⟨Ioo (t - 4 * r ^ 2) t, isOpen_Ioo⟩
      ⟨horizontalBall (G.horizontalFields hq) x (2 * r),
        isOpen_horizontalBall G hq hqpos hspan x (2 * r)⟩ u)
    (ε c : ℝ) :
    (∫⁻ z in (harnackEarlierIterationCylinder (E := CarnotPoint G hq hqpos hspan)
      (x : CarnotPoint G hq hqpos hspan) t r 1 : Set (ℝ × (Fin N → ℝ))),
        ENNReal.ofReal (Real.exp (-c) * (u z.1 z.2 + ε)) ^ p
          ∂(volume : Measure (ℝ × (Fin N → ℝ)))) ≠ ⊤ := by
  let J : Set ℝ := Icc (t - 25 / 8 * r ^ 2) (t - 15 / 8 * r ^ 2)
  let K : Set (Fin N → ℝ) := closure (horizontalBall (G.horizontalFields hq) x (5 / 4 * r))
  have hJ : IsCompact J := isCompact_Icc
  have hJI : J ⊆ Ioo (t - 4 * r ^ 2) t := by
    intro s hs
    dsimp only [J] at hs
    constructor <;> nlinarith [hs.1, hs.2, sq_pos_of_pos hr]
  have hK : IsCompact K := isCompact_closure_horizontalBall G hq hqpos hspan hw x (by positivity)
  have hKU : K ⊆ horizontalBall (G.horizontalFields hq) x (2 * r) :=
    closure_horizontalBall_subset_of_radius_lt G hq hqpos hspan x (by linarith)
  have hshift := hu.affine G hq hqpos hw hspan 1 ε
  simp only [one_mul] at hshift
  have hscale := hshift.const_mul G hq hqpos hw hspan (Real.exp (-c))
  have hmem := hscale.memLp_two_on_compact_cylinder G hq hqpos hw hspan a _ _ hJ hJI hK hKU
  let : IsFiniteMeasure (volume.restrict (J ×ˢ K)) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact (hJ.prod hK).measure_lt_top⟩
  have hpexp : ENNReal.ofReal p ≤ 2 := by
    exact (ENNReal.ofReal_le_ofReal hp2).trans_eq (by norm_num)
  have hlp := hmem.mono_exponent hpexp
  have hlin := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
    (ENNReal.ofReal_pos.mpr hp).ne' ENNReal.ofReal_ne_top hlp.eLpNorm_lt_top
  simp only [ENNReal.toReal_ofReal hp.le] at hlin
  have hball (s : ℝ) :
      (@Metric.ball (CarnotPoint G hq hqpos hspan) _ x s : Set (Fin N → ℝ)) =
        horizontalBall (G.horizontalFields hq) x s :=
    CarnotPoint.coordinateBall_eq_horizontalBall G hq hqpos hspan x s
  have hsmall : (harnackEarlierIterationCylinder (E := CarnotPoint G hq hqpos hspan)
      (x : CarnotPoint G hq hqpos hspan) t r 1 : Set (ℝ × (Fin N → ℝ))) ⊆ J ×ˢ K := by
    dsimp only [harnackEarlierIterationCylinder]
    simp only [one_pow, mul_one, hball]
    apply Set.prod_mono ?_ subset_closure
    intro s hs
    exact ⟨hs.1.le, by nlinarith [hs.2]⟩
  apply ne_top_of_lt
  calc
    _ ≤ ∫⁻ z in (harnackEarlierIterationCylinder (E := CarnotPoint G hq hqpos hspan)
        (x : CarnotPoint G hq hqpos hspan) t r 1 : Set (ℝ × (Fin N → ℝ))),
          ‖Real.exp (-c) * (u z.1 z.2 + ε)‖ₑ ^ p
            ∂(volume : Measure (ℝ × (Fin N → ℝ))) :=
      lintegral_mono fun z => ENNReal.rpow_le_rpow (Real.ofReal_le_enorm _) hp.le
    _ ≤ ∫⁻ z in J ×ˢ K, ‖Real.exp (-c) * (u z.1 z.2 + ε)‖ₑ ^ p :=
      lintegral_mono_set hsmall
    _ < ⊤ := hlin

end HeatKernel
