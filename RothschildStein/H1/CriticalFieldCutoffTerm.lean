-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.WeightedFieldCutoffScaling
public import RothschildStein.H1.CompactFieldCutoffTransport
public import RothschildStein.H1.IntegralSubtractConstant
public import Mathlib.Topology.MetricSpace.Pseudo.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
attribute [local irreducible] RothschildStein.HomogeneousGroup.inv RothschildStein.HomogeneousGroup.mul
open Set MeasureTheory Filter Topology
namespace RothschildStein.H1
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Step 3 at the critical degree: the actual scaled
compact-cutoff derivative term differs from its scalar multiple of
the test by at most Cε, uniformly in the base point. -/
theorem exists_criticalFieldCutoffTerm_error_bound
    {V : (Fin N → ℝ) → (Fin N → ℝ)} {k : ℝ}
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hhV : G2.IsHomogeneousField G V k)
    {f η ψ ν : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    (hf : ContinuousOn f {(0 : Fin N → ℝ)}ᶜ)
    (hhom : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 →
      f (G.dilate t x) = t ^ (k - (G.homogeneousDimension : ℝ)) * f x)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hsη : HasCompactSupport η)
    (heη : η =ᶠ[𝓝 (0 : Fin N → ℝ)] fun _ => 1)
    (hcψ : ContDiff ℝ 1 ψ) (hsψ : HasCompactSupport ψ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ x,
      ‖(∫ w, f w * fieldDerivative V (η ∘ G.dilate ε⁻¹) w * ψ (G.mul x (G.inv w))) -
        ψ x * (∫ v, f v * fieldDerivative V η v)‖ ≤ C * ε := by
  obtain ⟨C, hC, hb⟩ := exists_fieldCutoff_transport_bound G hV hν hf hη hsη heη hcψ hsψ
  have ha := integrable_mul_fieldDerivative_cutoff V hV hf hη hsη heη
  obtain ⟨B, hB⟩ := hsψ.exists_bound_of_continuous hcψ.continuous
  refine ⟨C, hC, ?_⟩
  intro ε hε hε1 x
  have ht := integral_weightedFieldCutoff_dilate G hhV hhom hη
    (φ := fun w => ψ (G.mul x (G.inv w))) hε
  have hd : (k - (G.homogeneousDimension : ℝ)) + (G.homogeneousDimension : ℝ) - k = 0 := by ring
  rw [hd, Real.rpow_zero, one_mul] at ht
  rw [ht]
  have hg : Continuous (fun v => ψ (G.mul x (G.inv (G.dilate ε v)))) :=
    hcψ.continuous.comp ((G2.continuous_mul G).comp
      (continuous_const.prodMk ((G2.continuous_inv G).comp (G2.continuous_dilate G ε))))
  rw [integral_mul_sub_constant ha hg.aestronglyMeasurable (fun v => hB _) (ψ x)]
  exact hb ε hε hε1 x

/-- The critical cutoff term converges
uniformly to the test times its cutoff coefficient. -/
theorem tendstoUniformly_criticalFieldCutoffTerm
    {V : (Fin N → ℝ) → (Fin N → ℝ)} {k : ℝ}
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hhV : G2.IsHomogeneousField G V k)
    {f η ψ ν : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    (hf : ContinuousOn f {(0 : Fin N → ℝ)}ᶜ)
    (hhom : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 →
      f (G.dilate t x) = t ^ (k - (G.homogeneousDimension : ℝ)) * f x)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hsη : HasCompactSupport η)
    (heη : η =ᶠ[𝓝 (0 : Fin N → ℝ)] fun _ => 1)
    (hcψ : ContDiff ℝ 1 ψ) (hsψ : HasCompactSupport ψ) :
    TendstoUniformly (fun ε x => ∫ w, f w * fieldDerivative V (η ∘ G.dilate ε⁻¹) w * ψ (G.mul x (G.inv w)))
      (fun x => ψ x * (∫ v, f v * fieldDerivative V η v)) (nhdsWithin 0 (Ioi 0)) := by
  obtain ⟨C, hC, hb⟩ := exists_criticalFieldCutoffTerm_error_bound G hV hhV hν hf hhom hη hsη heη hcψ hsψ
  have hid : Tendsto (fun ε : ℝ => ε) (nhdsWithin 0 (Ioi 0)) (𝓝 (0 : ℝ)) := tendsto_id.mono_left nhdsWithin_le_nhds
  have ht : Tendsto (fun ε : ℝ => C * ε) (nhdsWithin 0 (Ioi 0)) (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hid
  have hsmall : ∀ᶠ ε : ℝ in nhdsWithin 0 (Ioi 0), ε < 1 :=
    nhdsWithin_le_nhds (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  apply Metric.tendstoUniformly_iff.mpr
  intro δ hδ
  filter_upwards [self_mem_nhdsWithin, hsmall, ht.eventually (gt_mem_nhds hδ)] with ε hε hε1 he
  intro x
  rw [dist_comm, dist_eq_norm]
  exact (hb ε hε hε1.le x).trans_lt he

end RothschildStein.H1
