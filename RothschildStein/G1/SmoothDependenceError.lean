-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.LocalFlows
public import Mathlib.Analysis.ODE.Gronwall

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology

namespace RothschildStein.G1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The linearized trajectory error satisfies a Grönwall bound.
The comparison curve is constructed independently of differentiability in the
initial condition (BB Proposition 1.2, p. 3). -/
theorem first_variation_error_bound
    {Z : E → E} {α β W : ℝ → E} {A : ℝ → E →L[ℝ] E}
    {a b K ε : ℝ}
    (hα : ContinuousOn α (Icc a b))
    (hβ : ContinuousOn β (Icc a b))
    (hW : ContinuousOn W (Icc a b))
    (hα' : ∀ t ∈ Ico a b, HasDerivAt α (Z (α t)) t)
    (hβ' : ∀ t ∈ Ico a b, HasDerivAt β (Z (β t)) t)
    (hW' : ∀ t ∈ Ico a b, HasDerivAt W (A t (W t)) t)
    (hinit : W a = β a - α a)
    (hA : ∀ t ∈ Ico a b, ‖A t‖ ≤ K)
    (hr : ∀ t ∈ Ico a b,
      ‖Z (β t) - Z (α t) - A t (β t - α t)‖ ≤ ε) :
    ∀ t ∈ Icc a b,
      ‖β t - α t - W t‖ ≤ gronwallBound 0 K ε (t - a) := by
  apply norm_le_gronwallBound_of_norm_deriv_right_le
    ((hβ.sub hα).sub hW)
    (fun t ht => ((hβ' t ht).sub (hα' t ht)).sub (hW' t ht) |>.hasDerivWithinAt)
    (by simp [hinit])
  intro t ht
  have heq : Z (β t) - Z (α t) - A t (W t) =
      A t (β t - α t - W t) + (Z (β t) - Z (α t) - A t (β t - α t)) := by
    rw [map_sub]
    abel
  rw [heq]
  calc
    _ ≤ ‖A t (β t - α t - W t)‖ +
        ‖Z (β t) - Z (α t) - A t (β t - α t)‖ := norm_add_le _ _
    _ ≤ ‖A t‖ * ‖β t - α t - W t‖ + ε :=
      add_le_add ((A t).le_opNorm _) (hr t ht)
    _ ≤ K * ‖β t - α t - W t‖ + ε := by gcongr; exact hA t ht

/-- Scaling the forcing scales the zero-initial-value
Grönwall bound. This makes the trajectory error an arbitrarily small multiple
of the initial increment (BB Proposition 1.2, p. 3). -/
theorem gronwallBound_zero_scale (K ε c t : ℝ) :
    gronwallBound 0 K (ε * c) t = ε * gronwallBound 0 K 1 t * c := by
  unfold gronwallBound
  split_ifs <;> ring

/-- A uniform linearized residual estimate identifies the
initial-data derivative. The hypotheses concern the field's Taylor residual
and an independently given fundamental solution, without assuming initial-data
differentiability (BB Proposition 1.2, p. 3). -/
theorem hasFDerivAt_flow_of_linearized_residual
    {Z : E → E} {Φ : E → ℝ → E} {x : E}
    {J : ℝ → E →L[ℝ] E} {A : ℝ → E →L[ℝ] E}
    {a b t K : ℝ} (ht : t ∈ Icc a b)
    (hc : ∀ᶠ y in 𝓝 x, ContinuousOn (Φ y) (Icc a b))
    (hsol : ∀ᶠ y in 𝓝 x, ∀ v ∈ Ico a b,
      HasDerivAt (Φ y) (Z (Φ y v)) v)
    (hinit : ∀ᶠ y in 𝓝 x, Φ y a = y)
    (hJ : ContinuousOn J (Icc a b))
    (hJ' : ∀ v ∈ Ico a b, HasDerivAt J ((A v).comp (J v)) v)
    (hJinit : J a = ContinuousLinearMap.id ℝ E)
    (hA : ∀ v ∈ Ico a b, ‖A v‖ ≤ K)
    (hr : ∀ ε : ℝ, 0 < ε → ∀ᶠ y in 𝓝 x, ∀ v ∈ Ico a b,
      ‖Z (Φ y v) - Z (Φ x v) - A v (Φ y v - Φ x v)‖ ≤ ε * ‖y - x‖) :
    HasFDerivAt (fun y => Φ y t) (J t) x := by
  rw [hasFDerivAt_iff_isLittleO]
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  let C := |gronwallBound 0 K 1 (t - a)| + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hδ : 0 < ε / C := div_pos hε hC
  filter_upwards [hc, hsol, hinit, hr (ε / C) hδ] with y hyc hys hyi hyr
  have hW : ContinuousOn (fun v => J v (y - x)) (Icc a b) :=
    hJ.clm_apply continuousOn_const
  have hW' : ∀ v ∈ Ico a b,
      HasDerivAt (fun v => J v (y - x)) (A v (J v (y - x))) v := by
    intro v hv
    simpa using (hJ' v hv).clm_apply (hasDerivAt_const v (y - x))
  have hi : J a (y - x) = Φ y a - Φ x a := by
    simp [hJinit, hyi, hinit.self_of_nhds]
  have hb := first_variation_error_bound hc.self_of_nhds hyc hW
    hsol.self_of_nhds hys hW' hi hA hyr t ht
  rw [gronwallBound_zero_scale] at hb
  have hg : gronwallBound 0 K 1 (t - a) ≤ C := by
    dsimp [C]
    exact (le_abs_self _).trans (le_add_of_nonneg_right zero_le_one)
  calc
    ‖Φ y t - Φ x t - J t (y - x)‖ ≤
        ε / C * gronwallBound 0 K 1 (t - a) * ‖y - x‖ := hb
    _ ≤ ε / C * C * ‖y - x‖ := by gcongr
    _ = ε * ‖y - x‖ := by rw [div_mul_cancel₀ _ (ne_of_gt hC)]

end RothschildStein.G1
