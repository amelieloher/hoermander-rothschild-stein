-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.MollifierBound
public import Mathlib.Topology.UniformSpace.HeineCantor
public import Mathlib.Analysis.Normed.Group.Bounded

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open MeasureTheory Filter Set Function
open scoped Topology
namespace RothschildStein.G2
variable {N : ℕ} (G : HomogeneousGroup N) {ν : HomogeneousNorm G}

/-- Group regularizations of a compact continuous input converge
uniformly on the whole coordinate space (BB Prop 3.48 proof, p. 122). -/
theorem tendstoUniformly_groupRegularize (φ : GroupMollifier G ν)
    {f : (Fin N → ℝ) → ℝ} (hf : Continuous f) (hcf : HasCompactSupport f) :
    TendstoUniformly (fun ε : ℝ => groupRegularize G φ f ε) f (𝓝[>] 0) := by
  obtain ⟨C, hC⟩ := hf.bounded_above_of_compact_support hcf
  obtain ⟨K, hK, hfK, hregK⟩ := exists_common_compact_support_groupRegularize G φ hcf
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let : CompactSpace (tsupport φ) := isCompact_iff_compactSpace.mp φ.compact.isCompact
  let F : ℝ → K × (tsupport φ) → ℝ :=
    fun ε b => f (G.mul (G.inv (G.dilate ε b.2)) b.1)
  have hd : Continuous (fun p : ℝ × (K × (tsupport φ)) => G.dilate p.1 p.2.2) := by
    apply continuous_pi
    intro j
    exact (continuous_fst.pow (G.weight j)).mul
      ((continuous_apply j).comp (continuous_subtype_val.comp (continuous_snd.comp continuous_snd)))
  have hx : Continuous (fun p : ℝ × (K × (tsupport φ)) => (p.2.1 : Fin N → ℝ)) :=
    continuous_subtype_val.comp (continuous_fst.comp continuous_snd)
  have hi := (continuous_inv G).comp hd
  have hF : Continuous (uncurry F) := by
    apply hf.comp
    apply continuous_pi
    intro j
    apply (MvPolynomial.continuous_eval (p := G.productPolynomial j)).comp
    apply continuous_pi
    intro i
    cases i with
    | inl k => exact (continuous_apply k).comp hi
    | inr k => exact (continuous_apply k).comp hx
  have H := Continuous.tendstoUniformly F hF 0
  apply Metric.tendstoUniformly_iff.mpr
  intro η hη
  have Hu := (Metric.tendstoUniformly_iff.mp H (η / 2) (half_pos hη)).filter_mono (nhdsWithin_le_nhds (s := Ioi 0))
  have hsmall : ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε ∧ ε ≤ 1 := by
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with ε hε
    exact ⟨hε.1, hε.2.le⟩
  filter_upwards [Hu, hsmall] with ε hε hεpos x
  by_cases hxK : x ∈ K
  · have hφ : Integrable φ := φ.smooth.continuous.integrable_of_hasCompactSupport φ.compact
    have hmeas : AEStronglyMeasurable
        (fun z => φ z * f (G.mul (G.inv (G.dilate ε z)) x)) volume :=
      (φ.smooth.continuous.mul (hf.comp ((continuous_mul G).comp
        (((continuous_inv G).comp (continuous_dilate G ε)).prodMk continuous_const)))).aestronglyMeasurable
    have hi : Integrable (fun z => φ z * f (G.mul (G.inv (G.dilate ε z)) x)) volume :=
      Integrable.mono' (hφ.mul_const C) hmeas (Eventually.of_forall fun z => by
        rw [norm_mul, Real.norm_of_nonneg (φ.nonneg z)]
        exact mul_le_mul_of_nonneg_left (hC _) (φ.nonneg z))
    have hb : ∀ᵐ z ∂volume,
        ‖φ z * (f (G.mul (G.inv (G.dilate ε z)) x) - f x)‖ ≤ φ z * (η / 2) := by
      apply Eventually.of_forall
      intro z
      by_cases hz : z ∈ tsupport φ
      · have hh := hε (⟨x, hxK⟩, ⟨z, hz⟩)
        change dist (f (G.mul (G.inv (G.dilate 0 z)) x))
          (f (G.mul (G.inv (G.dilate ε z)) x)) < η / 2 at hh
        simp only [zero_dilate, inv_zero, zero_mul] at hh
        rw [norm_mul, Real.norm_of_nonneg (φ.nonneg z)]
        apply mul_le_mul_of_nonneg_left _ (φ.nonneg z)
        simpa only [dist_eq_norm, norm_sub_rev] using hh.le
      · have hz0 : φ z = 0 := image_eq_zero_of_notMem_tsupport hz
        simp only [hz0, MulZeroClass.zero_mul, norm_zero, le_refl]
    have hn : ‖groupRegularize G φ f ε x - f x‖ ≤ η / 2 := by
      rw [groupRegularize_sub_eq_integral G φ hεpos.1 x hi]
      have hh := norm_integral_le_of_norm_le (hφ.mul_const (η / 2)) hb
      simpa only [integral_mul_const, φ.integral_eq_one, one_mul] using hh
    rw [dist_eq_norm, norm_sub_rev]
    exact hn.trans_lt (half_lt_self hη)
  · have hfx : f x = 0 := image_eq_zero_of_notMem_tsupport (fun hs => hxK (hfK hs))
    have hrx : groupRegularize G φ f ε x = 0 := by
      by_contra hn
      exact hxK (hregK ε hεpos.1 hεpos.2 hn)
    simpa only [hfx, hrx, dist_self] using hη

end RothschildStein.G2
