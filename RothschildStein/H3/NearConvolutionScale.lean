-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.NearKernelUniform
public import RothschildStein.H3.CenteredCutoffFractionalHolder

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal NNReal
namespace RothschildStein.H3

/-- near part. The actual cutoff convolution has Hölder
norm at most C epsilon^(lambda-v) times the global L-infinity norm.
The buffered geometry is fixed before epsilon, the input and its center;
no kernel certificate or cutoff modulus is assumed (BB p. 382). -/
theorem near_convolution_holder_scale_of_controlNorm {N q : ℕ} (G : HomogeneousGroup N)
    (H : H1.StandingHypotheses G q)
    (Hc : G2.ControlNormConclusion G driftWeight H.fields)
    (ν : G2.HomogeneousNorm G) (hν : ν.Smooth)
    {T : (Fin N → ℝ) → ℝ} (hT : ContDiffOn ℝ (⊤ : ℕ∞) T {0}ᶜ)
    {v lam : ℝ} (hv : 0 ≤ v) (hvlam : v ≤ lam)
    (hlamQ : lam < (G.homogeneousDimension : ℝ))
    (hhom : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 →
      T (G.dilate t x) = t ^ (lam - (G.homogeneousDimension : ℝ)) * T x)
    {α : ℝ≥0} (hα : 0 < α) (hα1 : (α : ℝ) ≤ 1) (hαv : (α : ℝ) < v)
    {ρ : ℝ} (hρ : 0 < ρ) :
    let metric : MetricSpace (ControlCarrier N) :=
      gaugeMetric G Hc.norm Hc.constant_one Hc.symmetric
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ControlCarrier N, ∀ u : (Fin N → ℝ) → ℝ,
      MemLp u ∞ volume → tsupport u ⊆ G2.gaugeBall G Hc.norm z ρ →
      ∀ ε : ℝ, 0 < ε → ε < 1 →
      @H2.boundedHolderNorm (ControlCarrier N) metric α (ball z ρ)
        (fun x => G2.groupConvolution G u
          (fun w => smoothQuasiballCutoff G ν 0 (ε / 2) ε w * T w) x) ≤
        ENNReal.ofReal (C * ε ^ (lam - v) * lpNorm u ∞ volume) := by
  let metric : MetricSpace (ControlCarrier N) :=
    gaugeMetric G Hc.norm Hc.constant_one Hc.symmetric
  obtain ⟨a, A, S, ha, hA, hS, hcompare, hk⟩ :=
    nearKernel_uniform_constants_of_controlNorm G H Hc ν hν hT hv hvlam hlamQ hhom
  obtain ⟨_L, _hL, hc⟩ := exists_near_cutoff_lipschitz_constant G H Hc ν hν
  let r := ρ + 1 / a
  let R := 2 / a
  have hia : 0 < 1 / a := div_pos zero_lt_one ha
  have hr : 0 < r := add_pos hρ hia
  have hρr : ρ ≤ r := by dsimp [r]; linarith
  have hR : 0 < R := div_pos (by norm_num) ha
  have hRr : R ≤ 9 * r := by
    dsimp [R, r]
    rw [show (2 : ℝ) / a = 2 * (1 / a) by ring]
    linarith
  let C := H2.fractionalHolderConstant ((2 : ℝ) ^ G.homogeneousDimension)
    (3 * r) R α v * (A + S)
  have hvp : 0 < v := lt_trans (show 0 < (α : ℝ) from hα) hαv
  have hC : 0 ≤ C := by
    have hsemi := H2.fractionalSemiConstant_nonneg
      (C := (2 : ℝ) ^ G.homogeneousDimension) (κ := 3 * r) (R := R)
      (α := (α : ℝ)) (ν := v) (by positivity) (by positivity) hR hvp hαv
    have hvol := (H2.volumeIntegralConstant_pos
      (C := (2 : ℝ) ^ G.homogeneousDimension) (by positivity) hvp).le
    dsimp [C, H2.fractionalHolderConstant]
    positivity
  refine ⟨C, hC, ?_⟩
  intro z u hu hsu ε hε hε1
  have hsupport : ∀ w, R ≤ Hc.norm w → smoothQuasiballCutoff G ν 0 (ε / 2) ε w = 0 := by
    intro w hw
    have hνw : 2 ≤ ν w := by
      calc
        2 = a * R := by dsimp [R]; field_simp
        _ ≤ a * Hc.norm w := mul_le_mul_of_nonneg_left hw ha.le
        _ ≤ ν w := hcompare w
    exact (hc ε hε).2.2.2.2.1 w (by linarith)
  have hs : tsupport u ⊆ G2.gaugeBall G Hc.norm z r := by
    intro x hx
    have hh : @dist (ControlCarrier N) metric.toDist x z < ρ := hsu hx
    exact hh.trans_le hρr
  have hb := centered_cutoff_convolution_holder_of_kernelClass Hc.norm
    Hc.constant_one Hc.symmetric z hr hR hRr hsupport (hk ε hε) hα hα1 hαv hu hs
  have he : H2.fractionalHolderConstant ((2 : ℝ) ^ G.homogeneousDimension)
      (3 * r) R α v * (A * ε ^ (lam - v) + S * ε ^ (lam - v)) * lpNorm u ∞ volume =
      C * ε ^ (lam - v) * lpNorm u ∞ volume := by dsimp [C]; ring
  rw [he] at hb
  exact (H2.boundedHolderNorm_restrict (ball_subset_ball hρr)).trans hb

end RothschildStein.H3
