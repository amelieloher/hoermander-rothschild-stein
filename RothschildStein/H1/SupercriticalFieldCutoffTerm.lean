-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.WeightedFieldCutoffScaling
public import RothschildStein.H1.FieldCutoffSupport
public import Mathlib.Topology.MetricSpace.Pseudo.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
attribute [local irreducible] RothschildStein.HomogeneousGroup.inv RothschildStein.HomogeneousGroup.mul
open Set MeasureTheory Filter Topology
namespace RothschildStein.H1
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Step 3: above the critical degree, the scaled cutoff
term is uniformly bounded by Cε^(β+Q−k). -/
theorem exists_supercriticalFieldCutoffTerm_bound
    {V : (Fin N → ℝ) → (Fin N → ℝ)} {k β : ℝ}
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hhV : G2.IsHomogeneousField G V k)
    {f η ψ : (Fin N → ℝ) → ℝ}
    (hf : ContinuousOn f {(0 : Fin N → ℝ)}ᶜ)
    (hhom : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 → f (G.dilate t x) = t ^ β * f x)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hsη : HasCompactSupport η)
    (heη : η =ᶠ[𝓝 (0 : Fin N → ℝ)] fun _ => 1)
    (hcψ : Continuous ψ) (hsψ : HasCompactSupport ψ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ∀ x,
      ‖∫ w, f w * fieldDerivative V (η ∘ G.dilate ε⁻¹) w * ψ (G.mul x (G.inv w))‖ ≤
        C * ε ^ (β + (G.homogeneousDimension : ℝ) - k) := by
  have ha := integrable_mul_fieldDerivative_cutoff V hV hf hη hsη heη
  obtain ⟨B, hB⟩ := hsψ.exists_bound_of_continuous hcψ
  let M := max B 0
  have hM : 0 ≤ M := le_max_right _ _
  have hψ (v : Fin N → ℝ) : ‖ψ v‖ ≤ M := (hB v).trans (le_max_left _ _)
  refine ⟨(∫ v, ‖f v * fieldDerivative V η v‖) * M,
    mul_nonneg (integral_nonneg fun _ => norm_nonneg _) hM, ?_⟩
  intro ε hε x
  rw [integral_weightedFieldCutoff_dilate G hhV hhom hη
    (φ := fun w => ψ (G.mul x (G.inv w))) hε, norm_mul,
    Real.norm_of_nonneg (Real.rpow_nonneg hε.le _)]
  have hi : ‖∫ v, (f v * fieldDerivative V η v) * ψ (G.mul x (G.inv (G.dilate ε v)))‖ ≤
      (∫ v, ‖f v * fieldDerivative V η v‖) * M := by
    calc
      _ ≤ ∫ v, ‖f v * fieldDerivative V η v‖ * M := by
        apply norm_integral_le_of_norm_le (ha.norm.mul_const M)
        apply Eventually.of_forall
        intro v
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hψ _) (norm_nonneg _)
      _ = _ := integral_mul_const M _
  exact (mul_le_mul_of_nonneg_left hi (Real.rpow_nonneg hε.le _)).trans_eq (mul_comm _ _)

/-- The cutoff derivative term vanishes
uniformly on the whole group above the critical degree. -/
theorem tendstoUniformly_supercriticalFieldCutoffTerm
    {V : (Fin N → ℝ) → (Fin N → ℝ)} {k β : ℝ}
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) (hhV : G2.IsHomogeneousField G V k)
    {f η ψ : (Fin N → ℝ) → ℝ}
    (hf : ContinuousOn f {(0 : Fin N → ℝ)}ᶜ)
    (hhom : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 → f (G.dilate t x) = t ^ β * f x)
    (hβ : k - (G.homogeneousDimension : ℝ) < β)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hsη : HasCompactSupport η)
    (heη : η =ᶠ[𝓝 (0 : Fin N → ℝ)] fun _ => 1)
    (hcψ : Continuous ψ) (hsψ : HasCompactSupport ψ) :
    TendstoUniformly (fun ε x => ∫ w, f w * fieldDerivative V (η ∘ G.dilate ε⁻¹) w * ψ (G.mul x (G.inv w)))
      (fun _ => 0) (nhdsWithin 0 (Ioi 0)) := by
  obtain ⟨C, hC, hb⟩ := exists_supercriticalFieldCutoffTerm_bound G hV hhV hf hhom hη hsη heη hcψ hsψ
  have hid : Tendsto (fun ε : ℝ => ε) (nhdsWithin 0 (Ioi 0)) (𝓝 (0 : ℝ)) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hp : 0 < β + (G.homogeneousDimension : ℝ) - k := by linarith
  have ht : Tendsto (fun ε : ℝ => C * ε ^ (β + (G.homogeneousDimension : ℝ) - k))
      (nhdsWithin 0 (Ioi 0)) (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul (hid.rpow_const_nhds_zero hp)
  apply Metric.tendstoUniformly_iff.mpr
  intro δ hδ
  filter_upwards [self_mem_nhdsWithin, ht.eventually (gt_mem_nhds hδ)] with ε hε he
  intro x
  rw [dist_comm, dist_eq_norm, sub_zero]
  exact (hb ε hε x).trans_lt he

end RothschildStein.H1
