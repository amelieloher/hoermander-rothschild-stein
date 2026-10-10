-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Sobolev.RealConcentricTentPoincare
public import HeatKernel.Sobolev.LocalQuadraticPoincare
public import HeatKernel.Form.LocalDomainOperations
public import HeatKernel.Poincare.FiniteGradientIntegrability
public import HeatKernel.Bridge.LocalWeakGradientWitness
import Mathlib.Tactic
import all HeatKernel.Geometry.CarnotPoint
import all Mathlib.Basic.Real.Basic

/-! # Uniform local energy tent estimates -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Set MeasureTheory Metric RothschildStein TopologicalSpace
open scoped ENNReal
namespace HeatKernel.CarnotPoint

/-- Both distance-tent estimates hold uniformly for local horizontal energy functions,
for every supplied weak gradient and without an additional Poincaré hypothesis. -/
theorem exists_uniform_local_energy_tent_constant {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    : ∃ P : ℝ, 0 < P ∧ ∀ (x : CarnotPoint G hq hqpos hspan) (r R : ℝ), 0 < r → r < R →
    ∀ f : (Fin N → ℝ) → ℝ,
    MemLocalEnergy
      ⟨horizontalBall (G.horizontalFields hq) x R, isOpen_horizontalBall G hq hqpos hspan x R⟩
      (G.horizontalFields hq) f →
    ∀ g : Fin q → (Fin N → ℝ) → ℝ,
    (∀ i, hasWeakWordDeriv (G.horizontalFields hq)
      ⟨horizontalBall (G.horizontalFields hq) x R, isOpen_horizontalBall G hq hqpos hspan x R⟩
      [i] f (g i)) → ∀ α : ℕ, α = 1 ∨ α = 2 →
    let w : CarnotPoint G hq hqpos hspan → ℝ := fun y => max (1 - dist x y / r) 0 ^ α
    let m := (∫ y in ball x r, w y * f y ∂volume G hq hqpos hspan) /
      (∫ y, w y ∂volume G hq hqpos hspan)
    (∫ y in ball x r, w y * (f y - m) ^ 2 ∂volume G hq hqpos hspan) ≤
      (P * ((2 : ℝ) ^ G.homogeneousDimension + 7 / 4)) * r ^ 2 *
        ∫ y in ball x r, w y * ∑ i, (g i y) ^ 2 ∂volume G hq hqpos hspan := by
  obtain ⟨P, hP, hPI⟩ := exists_uniform_local_energy_quadratic_poincare_constant
    G hq hqpos hspan hw
  refine ⟨P, hP, ?_⟩
  intro x r R hr hrR f hf g hg α hα
  apply integral_tent_pow_sub_mean_le_of_concentric_poincare
    G hq hqpos hspan hw x hr hrR f g hf hg hP α hα
  intro s hs hsr
  let U : Opens (Fin N → ℝ) :=
    ⟨horizontalBall (G.horizontalFields hq) x R, isOpen_horizontalBall G hq hqpos hspan x R⟩
  let B := horizontalBall (G.horizontalFields hq) x s
  let V : Opens (Fin N → ℝ) := ⟨B, isOpen_horizontalBall G hq hqpos hspan x s⟩
  let K : Set (Fin N → ℝ) :=
    {y | horizontalL2Distance (G.horizontalFields hq) x y ≤ ENNReal.ofReal s}
  have hK : IsCompact K := isCompact_horizontal_closedBall G hq hqpos hspan hw x hs.le
  have hKU : K ⊆ U := by
    intro y hy
    exact hy.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (hr.trans hrR)).mpr (hsr.trans_lt hrR))
  have hBK : B ⊆ K := by
    intro y hy
    exact (show horizontalL2Distance (G.horizontalFields hq) x y < ENNReal.ofReal s from hy).le
  have hVU : V ≤ U := hBK.trans hKU
  have hfp : MemLp f 2 (MeasureTheory.volume.restrict B) :=
    (hf.memLp_restrict_compact U (G.horizontalFields hq) hK hKU).mono_measure
      (Measure.restrict_mono hBK le_rfl)
  have hgp : ∀ i, MemLp (g i) 2 (MeasureTheory.volume.restrict B) := by
    intro i
    exact (hf.memLp_weak_gradient_restrict_compact U (G.horizontalFields hq)
      (G.horizontalFields_contDiff hq) i (hg i) hK hKU).mono_measure
        (Measure.restrict_mono hBK le_rfl)
  let _ : IsFiniteMeasure (MeasureTheory.volume.restrict B) := isFiniteMeasure_restrict.mpr
    (volume_horizontalBall_lt_top G hq hqpos hspan hw x hs.le).ne
  have hfi : IntegrableOn f B := hfp.integrable (by norm_num)
  have H := hPI x s hs f g (hf.restrict U (G.horizontalFields hq) V hVU) hfi
    (memLp_finite_gradient_length hgp)
    (fun i => S.hasWeakWordDeriv_restrict (G.horizontalFields hq) U V hVU (hg i))
  simp only [ball_eq_horizontalBall G hq hqpos hspan]
  simp only [volume, CarnotPoint,
    setAverage_eq, smul_eq_mul, div_eq_mul_inv, mul_comm] at H ⊢
  convert H using 1 <;> rfl

end HeatKernel.CarnotPoint
