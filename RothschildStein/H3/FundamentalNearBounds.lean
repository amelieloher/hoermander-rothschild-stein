-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.NearConvolutionScale
public import RothschildStein.H3.FundamentalPositiveTypes

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal NNReal BigOperators
namespace RothschildStein.H3

/-- near part. The actual fundamental kernel and all its
horizontal first kernels have one common epsilon^((1-alpha)/2) bound
for their near convolutions. The constant precedes the input, center
and scale (BB Proposition 8.53, p. 382). -/
theorem fundamental_near_convolution_bounds_of_controlNorm {N q : ℕ} (G : HomogeneousGroup N)
    (H : H1.StandingHypotheses G q) (K : H1.FundamentalKernel G H)
    (Hc : G2.ControlNormConclusion G driftWeight H.fields)
    (hQ : 2 < (G.homogeneousDimension : ℝ))
    (ν : G2.HomogeneousNorm G) (hν : ν.Smooth)
    {α : ℝ≥0} (hα : 0 < α) (hα1 : (α : ℝ) < 1) {ρ : ℝ} (hρ : 0 < ρ) :
    let metric : MetricSpace (ControlCarrier N) :=
      gaugeMetric G Hc.norm Hc.constant_one Hc.symmetric
    ∃ C : ℝ, 0 < C ∧ ∀ z : ControlCarrier N, ∀ u : (Fin N → ℝ) → ℝ,
      MemLp u ∞ volume → tsupport u ⊆ G2.gaugeBall G Hc.norm z ρ →
      ∀ ε : ℝ, 0 < ε → ε < 1 →
      @H2.boundedHolderNorm (ControlCarrier N) metric α (ball z ρ)
        (fun x => G2.groupConvolution G u
          (fun w => smoothQuasiballCutoff G ν 0 (ε / 2) ε w * K w) x) +
        (∑ i : Fin q, @H2.boundedHolderNorm (ControlCarrier N) metric α (ball z ρ)
          (fun x => G2.groupConvolution G u
            (fun w => smoothQuasiballCutoff G ν 0 (ε / 2) ε w *
              fieldDerivative (H.fields i.succ) K w) x)) ≤
        ENNReal.ofReal (C * ε ^ ((1 - (α : ℝ)) / 2) * lpNorm u ∞ volume) := by
  classical
  let metric : MetricSpace (ControlCarrier N) :=
    gaugeMetric G Hc.norm Hc.constant_one Hc.symmetric
  let d := (1 - (α : ℝ)) / 2
  have hd : 0 < d := div_pos (sub_pos.mpr hα1) (by norm_num)
  have hd1 : d < 1 := by dsimp [d]; linarith [α.coe_nonneg]
  have hv1 : 0 ≤ 1 - d := by linarith
  have hv2 : 0 ≤ 2 - d := by linarith
  have hav1 : (α : ℝ) < 1 - d := by dsimp [d]; linarith
  have hav2 : (α : ℝ) < 2 - d := by dsimp [d]; linarith
  have hzero := near_convolution_holder_scale_of_controlNorm G H Hc ν hν K.smooth_off_zero
    hv2 (by linarith : 2 - d ≤ 2) hQ K.homogeneous hα hα1.le hav2 hρ
  obtain ⟨C₀, hC₀, hb₀⟩ := hzero
  have hfirst (i : Fin q) := near_convolution_holder_scale_of_controlNorm G H Hc ν hν
    (fundamental_horizontal_type_one G H K i).smooth hv1 (by linarith : 1 - d ≤ 1)
    (by linarith : (1 : ℝ) < G.homogeneousDimension)
    (fundamental_horizontal_type_one G H K i).homogeneous hα hα1.le hav1 hρ
  choose B hB hfirst_bound using hfirst
  let C := C₀ + (∑ i : Fin q, B i) + 1
  have hsum : 0 ≤ ∑ i : Fin q, B i := Finset.sum_nonneg (fun i _ => hB i)
  have hC : 0 < C := by dsimp [C]; linarith
  refine ⟨C, hC, ?_⟩
  intro z u hu hsu ε hε hε1
  have hz := hb₀ z u hu hsu ε hε hε1
  have hi (i : Fin q) := hfirst_bound i z u hu hsu ε hε hε1
  have he2 : (2 : ℝ) - (2 - d) = d := by ring
  have he1 : (1 : ℝ) - (1 - d) = d := by ring
  rw [he2] at hz
  simp only [he1] at hi
  have hp : 0 ≤ ε ^ d * lpNorm u ∞ volume := mul_nonneg (Real.rpow_nonneg hε.le _) lpNorm_nonneg
  have he : ENNReal.ofReal (C₀ * ε ^ d * lpNorm u ∞ volume) +
      (∑ i : Fin q, ENNReal.ofReal (B i * ε ^ d * lpNorm u ∞ volume)) =
        ENNReal.ofReal ((C₀ + ∑ i : Fin q, B i) * ε ^ d * lpNorm u ∞ volume) := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => by nlinarith [mul_nonneg (hB i) hp]),
      ← ENNReal.ofReal_add (by nlinarith [mul_nonneg hC₀ hp])
        (Finset.sum_nonneg (fun i _ => by nlinarith [mul_nonneg (hB i) hp]))]
    congr 1
    rw [← Finset.sum_mul, ← Finset.sum_mul]
    ring
  have hbound := (add_le_add hz (Finset.sum_le_sum (s := Finset.univ)
    (f := fun i : Fin q => @H2.boundedHolderNorm (ControlCarrier N) metric α (ball z ρ)
      (fun x => G2.groupConvolution G u
        (fun w => smoothQuasiballCutoff G ν 0 (ε / 2) ε w * fieldDerivative (H.fields i.succ) K w) x))
    (g := fun i : Fin q => ENNReal.ofReal (B i * ε ^ d * lpNorm u ∞ volume))
      (fun i _ => hi i))).trans_eq he
  apply hbound.trans
  apply ENNReal.ofReal_le_ofReal
  have hconst : C₀ + ∑ i : Fin q, B i ≤ C := by dsimp [C]; linarith
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hconst
    (Real.rpow_nonneg hε.le _)) lpNorm_nonneg

end RothschildStein.H3
