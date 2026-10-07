-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Prod
public import Mathlib.Analysis.Calculus.FDeriv.Linear
public import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Metric
open scoped Topology
namespace RothschildStein.G1

/-- Joint C¹ regularity supplies one coefficient-derivative
neighborhood for all nearby base points. This is the local uniformity
needed before the compact-center covering argument (BB pp. 34–35). -/
theorem exists_joint_chart_derivative_neighborhood {m n : ℕ}
    (F : ((Fin m → ℝ) × (Fin n → ℝ)) → (Fin n → ℝ))
    (x : Fin n → ℝ) (hF : ContDiffAt ℝ 1 F (0, x))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ u ∈ ball (0 : Fin m → ℝ) ρ, ∀ y ∈ ball x ρ,
      HasFDerivAt (fun v => F (v, y))
        ((fderiv ℝ F (u, y)).comp (ContinuousLinearMap.inl ℝ (Fin m → ℝ) (Fin n → ℝ))) u ∧
      ‖((fderiv ℝ F (u, y)).comp (ContinuousLinearMap.inl ℝ (Fin m → ℝ) (Fin n → ℝ))) -
        ((fderiv ℝ F (0, x)).comp (ContinuousLinearMap.inl ℝ (Fin m → ℝ) (Fin n → ℝ)))‖ < ε := by
  obtain ⟨U, hU, hFU⟩ := hF.contDiffOn (m := 1) le_rfl (by simp)
  obtain ⟨r, hr, hrU⟩ := Metric.mem_nhds_iff.mp hU
  have hFb : ContDiffOn ℝ 1 F (ball (0, x) r) := hFU.mono hrU
  let D := fun q : (Fin m → ℝ) × (Fin n → ℝ) =>
    (fderiv ℝ F q).comp (ContinuousLinearMap.inl ℝ (Fin m → ℝ) (Fin n → ℝ))
  have hDc : ContinuousAt D (0, x) :=
    ((hFb.continuousOn_fderiv_of_isOpen isOpen_ball le_rfl).continuousAt
      (ball_mem_nhds (0, x) hr)).clm_comp continuousAt_const
  have hclose : {q | ‖D q - D (0, x)‖ < ε} ∈ 𝓝 (0, x) :=
    (hDc.sub continuousAt_const).norm.preimage_mem_nhds (Iio_mem_nhds (by
      change ‖D (0, x) - D (0, x)‖ < ε
      simpa only [sub_self, norm_zero] using hε))
  obtain ⟨δ, hδ, hδsub⟩ := Metric.mem_nhds_iff.mp hclose
  refine ⟨min r δ / 2, by positivity, ?_⟩
  intro u hu y hy
  have hq : dist (u, y) (0, x) < min r δ := by
    rw [Prod.dist_eq]
    exact max_lt (hu.trans_le (by linarith [lt_min hr hδ]))
      (hy.trans_le (by linarith [lt_min hr hδ]))
  have hqr : (u, y) ∈ ball (0, x) r := hq.trans_le (min_le_left _ _)
  have hd := ((hFb.contDiffAt (isOpen_ball.mem_nhds hqr)).differentiableAt (by norm_num)).hasFDerivAt
  have hinc : HasFDerivAt (fun v : Fin m → ℝ => (v, y))
      (ContinuousLinearMap.inl ℝ (Fin m → ℝ) (Fin n → ℝ)) u := by
    convert (hasFDerivAt_id u).prodMk (hasFDerivAt_const y u) using 1 <;> try rfl
  refine ⟨hd.comp u hinc, ?_⟩
  exact hδsub (hq.trans_le (min_le_right _ _))

end RothschildStein.G1
