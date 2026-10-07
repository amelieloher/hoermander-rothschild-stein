-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.TypeZeroLocalHolderCertificate
public import RothschildStein.H3.TypeZeroRemainderHolder
public import RothschildStein.H3.TypeZeroRemainderIdentity
public import RothschildStein.H3.UnitLocalPrincipalValueIdentification
public import RothschildStein.H3.HolderBoundary
public import RothschildStein.H2.HolderOperations

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Metric MeasureTheory
open scoped NNReal ENNReal
namespace RothschildStein.H3

/-- The full actual PV convolution has a universal unit-ball
Hölder bound for compact C1 inputs, linear in the first kernel seminorm.
All local kernel certificates and the nonsingular remainder are proved. -/
theorem exists_typeZero_unit_holder_bound_smooth_of_controlNorm {N q : ℕ}
    (G : HomogeneousGroup N)
    {Y : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ)}
    (C : G2.ControlNormConclusion G driftWeight Y)
    (hY : ∀ i, ContinuousOn (Y i) {0}ᶜ)
    (hhomY : ∀ i, G2.IsHomogeneousField G (Y i) (if i = 0 then 2 else 1))
    {a : ℝ≥0} (ha : 0 < a) (ha1 : (a : ℝ) < 1) :
    let _metric := gaugeMetric G C.norm C.constant_one C.symmetric
    let E := ball (0 : ControlCarrier N) 1
    ∃ B : ℝ, 0 < B ∧ ∀ (k : (Fin N → ℝ) → ℝ), TypeZero G C.norm k →
      ∀ (F : ControlCarrier N → ℝ), ContDiff ℝ 1 (fun x : Fin N → ℝ => F x) →
      HasCompactSupport F → tsupport F ⊆ E → H2.BoundedHolder a E F →
      H2.boundedHolderNorm a E (fun x : ControlCarrier N => H1.principalValueConvolution G C.norm k
        (fun y : Fin N → ℝ => F y) x) ≤
        ENNReal.ofReal (kernelDerivativeBound C.norm k 1 * B) * H2.boundedHolderNorm a E F := by
  let _metric := gaugeMetric G C.norm C.constant_one C.symmetric
  let E := ball (0 : ControlCarrier N) 1
  obtain ⟨A, S, hA, hS, hlocal⟩ :=
    exists_typeZero_local_holder_certificate_of_controlNorm G C hY hhomY
  obtain ⟨Bt, hBt, htail⟩ := exists_typeZero_remainder_holder_bound_of_controlNorm G C hY hhomY ha ha1
  let B₀ := normalizedLocalHolderConstant G C.norm C.constant_one C.symmetric A S hA hS a
  let B := max 0 B₀ + Bt + 1
  dsimp only
  refine ⟨B, by dsimp only [B]; linarith [le_max_left (0 : ℝ) B₀], ?_⟩
  intro k hk F hF hc hs hf
  let Λ := kernelDerivativeBound C.norm k 1
  have hΛ : 0 ≤ Λ := (kernelDerivativeBound_properties C.norm.gauge hk.smooth 1).1
  have hball : E = {y : ControlCarrier N | C.norm y < 1} := by
    ext y
    change C.norm (G.mul (G.inv 0) y) < 1 ↔ C.norm y < 1
    rw [G2.inv_zero, G2.zero_mul]
  have hsu : ∀ y : Fin N → ℝ, 1 ≤ C.norm y → F y = 0 := by
    intro y hy
    apply image_eq_zero_of_notMem_tsupport
    intro hz
    have hh := hs hz
    change y ∈ E at hh
    rw [hball] at hh
    exact (not_lt_of_ge hy) hh
  have hext : H2.boundedHolderNorm a univ F = H2.boundedHolderNorm a E F :=
    boundedHolderNorm_global_eq_of_controlNorm C isOpen_ball hc hs
  have hsrc : H2.boundedHolderNorm a (ball (0 : ControlCarrier N) 2) F ≤
      H2.boundedHolderNorm a E F :=
    (H2.boundedHolderNorm_restrict (subset_univ _)).trans_eq hext
  have hf₂ : H2.BoundedHolder a (ball (0 : ControlCarrier N) 2) F := hsrc.trans_lt hf
  obtain ⟨HK, hlocalK⟩ := hlocal k hk
  let Q := localKernelData_of_truncatedKernelFacts G C.norm C.constant_one C.symmetric (Λ * A) (Λ * S)
    (fun x y : ControlCarrier N => truncatedKernel G C.norm k x y) HK
  have hqb : H2.boundedHolderNorm a E (Q.principalValue F) ≤
      ENNReal.ofReal (Λ * B₀) * H2.boundedHolderNorm a E F :=
    (H2.boundedHolderNorm_restrict (ball_subset_ball (by norm_num : (1 : ℝ) ≤ 2))).trans
      ((hlocalK a ha ha1 F hf₂).2.trans (mul_le_mul' le_rfl hsrc))
  let R := H2.fractionalIntegral volume E
    (fun x y => cutoffGroupKernel G (typeZeroRemainderCutoff C.norm) k x y) F
  have hrb : H2.boundedHolderNorm a E R ≤
      ENNReal.ofReal (Λ * Bt) * H2.boundedHolderNorm a E F := htail k hk F hf
  have heq : EqOn (fun x : ControlCarrier N => H1.principalValueConvolution G C.norm k
        (fun y : Fin N → ℝ => F y) x) (Q.principalValue F + R) E := by
    intro x hx
    have hx' : C.norm x < 1 := by
      rw [hball] at hx
      change C.norm x < 1 at hx
      exact hx
    have hpv := localKernelData_unit_source_principalValue G C.norm C.constant_one C.symmetric
      (Λ * A) (Λ * S) k F HK hk hF hc hsu ha ha1 hf₂ hx'
    have hrem : R x = G2.groupConvolution G F (typeZeroUnitTail C.norm k) x := by
      dsimp only [R]
      rw [hball]
      exact typeZero_remainder_integral_eq_unitTail G C.norm C.constant_one C.symmetric k F hsu hx'
    change H1.principalValueConvolution G C.norm k (fun y : Fin N → ℝ => F y) x =
      Q.principalValue F x + R x
    change Q.principalValue F x = _ at hpv
    rw [hrem]
    linarith
  change H2.boundedHolderNorm a E (fun x : ControlCarrier N =>
    H1.principalValueConvolution G C.norm k (fun y : Fin N → ℝ => F y) x) ≤
      ENNReal.ofReal (Λ * B) * H2.boundedHolderNorm a E F
  rw [H2.boundedHolderNorm_congr (X := ControlCarrier N) heq]
  calc
    _ ≤ H2.boundedHolderNorm a E (Q.principalValue F) + H2.boundedHolderNorm a E R :=
      H2.boundedHolderNorm_add_le
    _ ≤ ENNReal.ofReal (Λ * B₀) * H2.boundedHolderNorm a E F +
        ENNReal.ofReal (Λ * Bt) * H2.boundedHolderNorm a E F := add_le_add hqb hrb
    _ ≤ ENNReal.ofReal (Λ * max 0 B₀) * H2.boundedHolderNorm a E F +
        ENNReal.ofReal (Λ * Bt) * H2.boundedHolderNorm a E F :=
      add_le_add (mul_le_mul' (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_left (le_max_right _ _) hΛ)) le_rfl) le_rfl
    _ = ENNReal.ofReal (Λ * (max 0 B₀ + Bt)) * H2.boundedHolderNorm a E F := by
      rw [← add_mul, ← ENNReal.ofReal_add
        (mul_nonneg hΛ (le_max_left _ _)) (mul_nonneg hΛ hBt)]
      congr 2
      ring
    _ ≤ ENNReal.ofReal (Λ * B) * H2.boundedHolderNorm a E F :=
      mul_le_mul' (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_left (by dsimp only [B]; linarith) hΛ)) le_rfl

end RothschildStein.H3
