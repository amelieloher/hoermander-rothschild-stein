-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Poincare.UniformTranslation
public import HeatKernel.Poincare.LocalMeasurableExtension

/-! Compact-ball integrability from local continuous differentiability. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory RothschildStein
open scoped ENNReal BigOperators

namespace HeatKernel

/-- Continuous differentiability makes the horizontal gradient norm continuous on an
open set whenever the horizontal fields are continuous. -/
theorem continuousOn_horizontalGradientNorm {N q : ℕ}
    {X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)} (hX : ∀ i, Continuous (X i))
    {u : (Fin N → ℝ) → ℝ} {U : Set (Fin N → ℝ)} (hU : IsOpen U)
    (hu : ContDiffOn ℝ 1 u U) : ContinuousOn (horizontalGradientNorm X u) U := by
  apply Real.continuous_sqrt.comp_continuousOn
  apply continuousOn_finsetSum
  intro i _
  exact ((hu.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply (hX i).continuousOn).pow 2

/-- The closure of a finite-radius horizontal ball is compact. -/
theorem isCompact_closure_horizontalBall {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (x : Fin N → ℝ) {r : ℝ} (hr : 0 ≤ r) :
    IsCompact (closure (horizontalBall (G.horizontalFields hq) x r)) := by
  have hc := isCompact_horizontal_closedBall G hq hqpos hspan hw x hr
  apply hc.of_isClosed_subset isClosed_closure
  apply closure_minimal _ hc.isClosed
  intro y hy
  exact (show horizontalL2Distance (G.horizontalFields hq) x y < ENNReal.ofReal r from hy).le

/-- A continuously differentiable function near a closed horizontal ball is integrable
on the ball, as is every pairwise absolute power with exponent at least one. -/
theorem integrableOn_and_pairwise_rpow_of_contDiffOn {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (x : Fin N → ℝ) {r p : ℝ} (hr : 0 ≤ r) (hp : 1 ≤ p)
    {u : (Fin N → ℝ) → ℝ} {U : Set (Fin N → ℝ)}
    (hsub : closure (horizontalBall (G.horizontalFields hq) x r) ⊆ U)
    (hu : ContDiffOn ℝ 1 u U) :
    IntegrableOn u (horizontalBall (G.horizontalFields hq) x r) ∧
      ∀ y, IntegrableOn (fun z => |u y - u z| ^ p) (horizontalBall (G.horizontalFields hq) x r) := by
  have hc := hu.continuousOn.mono hsub
  have hk := isCompact_closure_horizontalBall G hq hqpos hspan hw x hr
  refine ⟨(hc.integrableOn_compact hk).mono_set subset_closure, ?_⟩
  intro y
  have hcp := (Real.continuous_rpow_const (le_trans zero_le_one hp)).comp_continuousOn
    ((continuousOn_const : ContinuousOn (fun _ : Fin N → ℝ => u y)
      (closure (horizontalBall (G.horizontalFields hq) x r))).sub hc).abs
  exact (hcp.integrableOn_compact hk).mono_set subset_closure

end HeatKernel
