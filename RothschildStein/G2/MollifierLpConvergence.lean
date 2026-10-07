-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.MollifierCompactLp
public import RothschildStein.G2.MollifierContraction
public import RothschildStein.G2.MollifierLinearity
public import Mathlib.MeasureTheory.Function.ContinuousMapDense
public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal
namespace RothschildStein.G2
variable {N : ℕ} (G : HomogeneousGroup N) {ν : HomogeneousNorm G}

/-- Group mollification converges to every Lp input for
1 ≤ p < infinity (BB Prop 3.48 proof, p. 122; density and contraction). -/
theorem tendsto_groupRegularize_eLpNorm (φ : GroupMollifier G ν)
    {p : ℝ} (hp : 1 ≤ p) {f : (Fin N → ℝ) → ℝ}
    (hf : MemLp f (ENNReal.ofReal p) volume) :
    Tendsto (fun ε : ℝ => eLpNorm (groupRegularize G φ f ε - f) (ENNReal.ofReal p) volume)
      (𝓝[>] 0) (𝓝 0) := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hpE : 1 ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp
  apply ENNReal.tendsto_nhds_zero.mpr
  intro η hη
  let δ : ℝ≥0∞ := η / 3
  have hδ : 0 < δ := ENNReal.div_pos hη.ne' (by norm_num)
  obtain ⟨g, hcg, hfg, hg, hgp⟩ := hf.exists_hasCompactSupport_eLpNorm_sub_le
    ENNReal.ofReal_ne_top hδ.ne'
  have H := ENNReal.tendsto_nhds_zero.mp
    (tendsto_groupRegularize_compact_eLpNorm G φ hg hcg hp0) δ hδ
  filter_upwards [H, self_mem_nhdsWithin] with ε hε hεpos
  have hreg := eLpNorm_groupRegularize_le_finite G φ hεpos hp
    (hf.aestronglyMeasurable.sub hgp.aestronglyMeasurable)
  have hlin := groupRegularize_sub G φ hεpos hpE hf hgp
  have he : groupRegularize G φ f ε - f =
      (groupRegularize G φ (f - g) ε + (groupRegularize G φ g ε - g)) + (g - f) := by
    rw [hlin]
    funext x
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  rw [he]
  calc
    _ ≤ (eLpNorm (groupRegularize G φ (f - g) ε) (ENNReal.ofReal p) volume +
        eLpNorm (groupRegularize G φ g ε - g) (ENNReal.ofReal p) volume) +
        eLpNorm (g - f) (ENNReal.ofReal p) volume :=
      (eLpNorm_add_le hpE).trans (add_le_add (eLpNorm_add_le hpE) le_rfl)
    _ ≤ (δ + δ) + δ := by
      rw [eLpNorm_sub_comm g f]
      exact add_le_add (add_le_add (hreg.trans hfg) hε) hfg
    _ = η := by
      change η / 3 + η / 3 + η / 3 = η
      calc
        _ = η / 3 * (1 + 1 + 1) := by rw [mul_add, mul_add, mul_one]
        _ = η := by
          norm_num
          exact ENNReal.div_mul_cancel (by norm_num) (by norm_num)

end RothschildStein.G2
