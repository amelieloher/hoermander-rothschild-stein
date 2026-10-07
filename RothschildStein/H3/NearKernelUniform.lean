-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.NearCutoffConstants
public import RothschildStein.H3.CutoffKernelUniformClass

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal
namespace RothschildStein.H3

/-- near part. The constructed cutoff homogeneous kernel
has fixed size and smoothness coefficients times epsilon^(lambda-v).
The smooth gauge is compared to the actual control norm, and the
cutoff's Lipschitz constant is proved, not supplied (BB p. 382). -/
theorem nearKernel_uniform_constants_of_controlNorm {N q : ℕ} (G : HomogeneousGroup N)
    (H : H1.StandingHypotheses G q)
    (Hc : G2.ControlNormConclusion G driftWeight H.fields)
    (ν : G2.HomogeneousNorm G) (hν : ν.Smooth)
    {T : (Fin N → ℝ) → ℝ} (hT : ContDiffOn ℝ (⊤ : ℕ∞) T {0}ᶜ)
    {v lam : ℝ} (hv : 0 ≤ v) (hvlam : v ≤ lam)
    (hlamQ : lam < (G.homogeneousDimension : ℝ))
    (hhom : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 →
      T (G.dilate t x) = t ^ (lam - (G.homogeneousDimension : ℝ)) * T x) :
    ∃ a A S : ℝ, 0 < a ∧ 0 ≤ A ∧ 0 ≤ S ∧
      (∀ x, a * Hc.norm x ≤ ν x) ∧
      let metric : MetricSpace (ControlCarrier N) :=
        gaugeMetric G Hc.norm Hc.constant_one Hc.symmetric
      ∀ ε : ℝ, 0 < ε →
        @H2.KernelClass (ControlCarrier N) metric inferInstance volume univ 1 v
          (A * ε ^ (lam - v)) (S * ε ^ (lam - v))
          (fun x y => cutoffGroupKernel G
            (smoothQuasiballCutoff G ν 0 (ε / 2) ε) T x y) := by
  obtain ⟨a, b, ha, _hb, hab⟩ := G2.gauges_equivalent Hc.norm.gauge ν.gauge
  obtain ⟨L, hL, hc⟩ := exists_near_cutoff_lipschitz_constant G H Hc ν hν
  let metric : MetricSpace (ControlCarrier N) :=
    gaugeMetric G Hc.norm Hc.constant_one Hc.symmetric
  let m := (volume {z : Fin N → ℝ | Hc.norm z < 1}).toReal
  let A := m * kernelSphereBound Hc.norm T * (1 / a) ^ (lam - v)
  let S := m * cutoffKernelFrameConstant Hc.norm H.fields (G.homogeneousDimension : ℝ) *
    (1 + (1 / a) * (L / 1)) * kernelDerivativeBound Hc.norm T 1 *
    (2 : ℝ) ^ (G.homogeneousDimension : ℝ) * (1 / a) ^ (lam - v)
  have hclass (ε : ℝ) (hε : 0 < ε) := by
    obtain ⟨_hsm, hmeas, _hcompact, hrange, hsupp, hmod⟩ := hc ε hε
    have hsupport : ∀ z, ε / a < Hc.norm z →
        smoothQuasiballCutoff G ν 0 (ε / 2) ε z = 0 := by
      intro z hz
      apply hsupp z
      exact ((div_lt_iff₀ ha).mp hz).trans_le (by simpa only [mul_comm] using (hab z).1)
    exact cutoffGroupKernel_kernelClass_uniform_of_controlNorm Hc
      (fun i => (H.fields_smooth G i).continuous.continuousOn) H.homogeneous hT
      hv hvlam hlamQ hhom (div_pos hε ha) (div_pos hL hε).le
      hmeas hrange hmod hsupport
  have hunit := hclass 1 zero_lt_one
  refine ⟨a, A, S, ha, hunit.A_nonneg, hunit.S_nonneg, (fun x => (hab x).1), ?_⟩
  dsimp only
  intro ε hε
  have hk := hclass ε hε
  have hp : (ε / a) ^ (lam - v) = (1 / a) ^ (lam - v) * ε ^ (lam - v) := by
    rw [Real.div_rpow hε.le ha.le, Real.div_rpow (by norm_num : (0 : ℝ) ≤ 1) ha.le,
      Real.one_rpow]
    ring
  have he : (ε / a) * (L / ε) = (1 / a) * (L / 1) := by
    field_simp
  rw [hp, he] at hk
  convert hk using 1 <;> dsimp [A, S, m] <;> ring

end RothschildStein.H3
