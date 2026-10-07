-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.LocalFlows

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric Function ODE
open scoped Topology NNReal

namespace RothschildStein.G1

/-- Picard flow with its spatial confinement retained. This strengthens
the Mathlib existence output by retaining the fixed-point curve's range bound
(BB Prop 1.2, p. 3). -/
theorem exists_continuous_flow_in_closedBall {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {Z : E → E} {x₀ : E} {τ : ℝ}
    {a r L K : ℝ≥0} (hτ : 0 < τ)
    (hf : IsPicardLindelof (fun _ => Z)
      (tmin := -τ) (tmax := τ) ⟨0, ⟨by linarith, hτ.le⟩⟩ x₀ a r L K) :
    ∃ Φ : (E × ℝ) → E,
      ContinuousOn Φ (closedBall x₀ r ×ˢ Icc (-τ) τ) ∧
      ∀ x ∈ closedBall x₀ r, Φ (x, 0) = x ∧ ∀ t ∈ Ioo (-τ) τ,
        Φ (x, t) ∈ closedBall x₀ a ∧ HasDerivAt (fun v => Φ (x, v)) (Z (Φ (x, t))) t := by
  classical
  have hfixed (x) (hx : x ∈ closedBall x₀ r) := FunSpace.exists_isFixedPt_next hf hx
  choose α hα using hfixed
  let φ := fun x : E => if hx : x ∈ closedBall x₀ r then (α x hx).compProj else fun _ => 0
  have hcurve : ∀ x ∈ closedBall x₀ r, φ x 0 = x ∧
      ∀ t ∈ Icc (-τ) τ, HasDerivWithinAt (φ x) (Z (φ x t)) (Icc (-τ) τ) t := by
    intro x hx
    simp only [φ, dite_eq_left hx]
    constructor
    · have hv := FunSpace.compProj_val (α := α x hx)
        (t := (⟨0, ⟨by linarith, hτ.le⟩⟩ : Icc (-τ) τ))
      exact hv.trans ((congrArg (fun γ : FunSpace
        (⟨0, ⟨by linarith, hτ.le⟩⟩ : Icc (-τ) τ) x₀ r L =>
          γ ⟨0, ⟨by linarith, hτ.le⟩⟩) (hα x hx)).symm.trans
            (FunSpace.next_apply₀ hf hx (α x hx)))
    · intro t ht
      apply hasDerivWithinAt_picard_Icc ⟨by linarith, hτ.le⟩ hf.continuousOn_uncurry
        (α x hx).continuous_compProj.continuousOn
        (fun _ _ => (α x hx).compProj_mem_closedBall hf.mul_max_le) x ht |>.congr_of_mem _ ht
      intro v hv
      nth_rw 1 [← hα]
      rw [FunSpace.compProj_of_mem hv, FunSpace.next_apply]
  obtain ⟨K', hK'⟩ := FunSpace.exists_forall_closedBall_funSpace_dist_le_mul hf
  have hLip : ∀ t ∈ Icc (-τ) τ, LipschitzOnWith K' (fun x => φ x t) (closedBall x₀ r) := by
    intro t ht
    apply LipschitzOnWith.of_dist_le_mul
    intro x hx y hy
    simp only [φ, dite_eq_left hx, dite_eq_left hy, FunSpace.compProj_apply,
      ← FunSpace.toContinuousMap_apply_eq_apply]
    have : Nonempty (Icc (-τ) τ) := ⟨⟨0, by constructor <;> linarith⟩⟩
    exact ContinuousMap.dist_le_iff_of_nonempty.mp
      (hK' x y hx hy (α x hx) (α y hy) (hα x hx) (hα y hy)) _
  refine ⟨uncurry φ,
    continuousOn_prod_of_continuousOn_lipschitzOnWith _ K'
      (fun x hx => HasDerivWithinAt.continuousOn (hcurve x hx).2) hLip, ?_⟩
  intro x hx
  refine ⟨(hcurve x hx).1, ?_⟩
  intro t ht
  refine ⟨?_, ((hcurve x hx).2 t ⟨ht.1.le, ht.2.le⟩).hasDerivAt
    (Icc_mem_nhds ht.1 ht.2)⟩
  simp only [uncurry, φ, dite_eq_left hx]
  exact (α x hx).compProj_mem_closedBall hf.mul_max_le

/-- A uniform existence time determined by the spatial clearance and
zeroth coefficient bound. Any finite Lipschitz constant suffices; the curve is
confined to the original ball (BB Prop 1.2, p. 3). -/
theorem exists_flow_with_explicit_time {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {Z : E → E} {x₀ : E}
    {a L K : ℝ≥0} (ha : 0 < a)
    (hbound : ∀ x ∈ closedBall x₀ a, ‖Z x‖ ≤ L)
    (hLip : LipschitzOnWith K Z (closedBall x₀ a)) :
    ∃ Φ : (E × ℝ) → E,
      ContinuousOn Φ (closedBall x₀ (a / 2 : ℝ≥0) ×ˢ Icc
        (-(a / (4 * (L + 1)) : ℝ)) (a / (4 * (L + 1)) : ℝ)) ∧
      ∀ x ∈ closedBall x₀ (a / 2 : ℝ≥0), Φ (x, 0) = x ∧
        ∀ t ∈ Ioo (-(a / (4 * (L + 1)) : ℝ)) (a / (4 * (L + 1)) : ℝ),
          Φ (x, t) ∈ closedBall x₀ a ∧ HasDerivAt (fun v => Φ (x, v)) (Z (Φ (x, t))) t := by
  let τ : ℝ := a / (4 * (L + 1))
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hτ : 0 < τ := by dsimp [τ]; positivity
  have hm : (L : ℝ) * max (τ - 0) (0 - (-τ)) ≤ a - (a / 2 : ℝ≥0) := by
    simp only [sub_zero, sub_neg_eq_add, zero_add, max_self, NNReal.coe_div, NNReal.coe_ofNat]
    dsimp [τ]
    have hd : (0 : ℝ) < 4 * (L + 1) := by positivity
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hd).mpr
    ring_nf
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ a from ha'.le) (show (0 : ℝ) ≤ L from L.2)]
  exact exists_continuous_flow_in_closedBall hτ
    (IsPicardLindelof.of_time_independent hbound hLip hm)

end RothschildStein.G1
