-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.HomogeneousCutoffCancellation
public import RothschildStein.H1.SharpShellDominatedLimit
public import RothschildStein.H1.ShellRadialWeight

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter TopologicalSpace MeasureTheory
open scoped Topology BigOperators
namespace RothschildStein.H1
variable {N : ℕ}

/-- The finite differential operator has continuous output
under exactly the local regularity required by each multi-index. -/
theorem continuousOn_differentialOperator_finite (U : Opens (Fin N → ℝ))
    (P : SmoothDifferentialOperator N) {f : (Fin N → ℝ) → ℝ}
    (hf : ∀ a ∈ P.indices, ContDiffOn ℝ (∑ j, a j : ℕ) f (U : Set (Fin N → ℝ))) :
    ContinuousOn (P.apply f) (U : Set (Fin N → ℝ)) := by
  unfold SmoothDifferentialOperator.apply
  exact continuousOn_finsetSum P.indices fun a ha => (P.smooth_coefficient a ha).continuous.continuousOn.mul
    (contDiffOn_euclideanPartial_finite U a 0 f (by simpa using hf a ha)).continuousOn

/-- shell clause: every positive-degree homogeneous
smooth differential operator has vanishing shell integrals on a
kernel of the complementary degree. Finite local differentiability
suffices (BB Corollary 6.31, p. 280). -/
theorem vanishingShellIntegrals_homogeneousDerivative (G : HomogeneousGroup N)
    (P : SmoothDifferentialOperator N) {k : ℝ} (hk : 0 < k) (hP : P.IsHomogeneous G k)
    {f ν : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    (hf : ContinuousOn f {(0 : Fin N → ℝ)}ᶜ)
    (hreg : ∀ a ∈ P.indices, ContDiffOn ℝ (∑ j, a j : ℕ) f {(0 : Fin N → ℝ)}ᶜ)
    (hscale : ∀ s : ℝ, 0 < s → ∀ x, x ≠ 0 →
      f (G.dilate s x) = s ^ (k - (G.homogeneousDimension : ℝ)) * f x) :
    HasVanishingShellIntegrals ν (P.apply f) := by
  intro r R hr hrR
  obtain ⟨η, hη⟩ := exists_sharpShellCutoff_sequence G hν
  let U : Opens (Fin N → ℝ) := ⟨{0}ᶜ, isOpen_compl_singleton⟩
  have hDf : ContinuousOn (P.apply f) {(0 : Fin N → ℝ)}ᶜ :=
    continuousOn_differentialOperator_finite U P hreg
  have hzero (n : ℕ) : ∫ x, P.apply f x *
      (η n (G.dilate R⁻¹ x) - η n (G.dilate r⁻¹ x)) = 0 := by
    have hnear := gaugeCutoff_eventually_one G hν
      ((by norm_num : (0 : ℝ) < 1 / 2).trans_le (sharpShell_innerRadius_ge_half n))
      (hη n).2.2.2.1
    exact integral_homogeneous_cutoffDifference_zero G P hk hP hf hreg hscale
      (hη n).1 (hη n).2.1 hnear (inv_pos.mpr (hr.trans hrR)) (inv_pos.mpr hr)
  have ht := tendsto_integral_sharpShellCutoff_difference G hν hDf
    (fun n => (hη n).1.continuous) (fun n => (hη n).2.2.1)
    (fun n => (hη n).2.2.2.1) (fun n => (hη n).2.2.2.2) hr hrR
  have he : (fun n => ∫ x, P.apply f x *
      (η n (G.dilate R⁻¹ x) - η n (G.dilate r⁻¹ x))) = fun _ : ℕ => (0 : ℝ) := funext hzero
  rw [he] at ht
  exact tendsto_nhds_unique ht tendsto_const_nhds

/-- continuous radial weights preserve the cancellation
of the actual homogeneous derivative, at finite local regularity
(BB Corollary 6.31, p. 280). -/
theorem integral_homogeneousDerivative_radialWeight_zero (G : HomogeneousGroup N)
    (P : SmoothDifferentialOperator N) {k : ℝ} (hk : 0 < k) (hP : P.IsHomogeneous G k)
    {f ν : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    (hf : ContinuousOn f {(0 : Fin N → ℝ)}ᶜ)
    (hreg : ∀ a ∈ P.indices, ContDiffOn ℝ (∑ j, a j : ℕ) f {(0 : Fin N → ℝ)}ᶜ)
    (hscale : ∀ s : ℝ, 0 < s → ∀ x, x ≠ 0 →
      f (G.dilate s x) = s ^ (k - (G.homogeneousDimension : ℝ)) * f x)
    {r R : ℝ} (hr : 0 < r) (hrR : r < R) {Φ : ℝ → ℝ}
    (hΦ : ContinuousOn Φ (Icc r R)) :
    ∫ x in gaugeShell ν r R, P.apply f x * Φ (ν x) = 0 := by
  let U : Opens (Fin N → ℝ) := ⟨{0}ᶜ, isOpen_compl_singleton⟩
  exact integral_gaugeShell_radialWeight_zero G hν
    (continuousOn_differentialOperator_finite U P hreg)
    (vanishingShellIntegrals_homogeneousDerivative G P hk hP hν hf hreg hscale) hr hrR hΦ

end RothschildStein.H1
