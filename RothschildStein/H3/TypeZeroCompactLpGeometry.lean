-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.TypeZeroGeometricCertificate
public import RothschildStein.H3.CompactGlobalPrincipalValueEstimate

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal
namespace RothschildStein.H3

/-- Actual type-zero PV on every compact C1 source has a global
Lp bound linear in Lambda_1. All geometric kernel certificates are constructed. -/
theorem exists_typeZero_compact_Lp_bound_of_controlNorm {N q : ℕ}
    (G : HomogeneousGroup N)
    {Y : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ)}
    (C : G2.ControlNormConclusion G driftWeight Y)
    (hY : ∀ i, ContinuousOn (Y i) {0}ᶜ)
    (hhomY : ∀ i, G2.IsHomogeneousField G (Y i) (if i = 0 then 2 else 1))
    {p : ℝ} (hp : 1 < p) :
    ∃ B : ℝ, 0 < B ∧ ∀ k : (Fin N → ℝ) → ℝ, TypeZero G C.norm k →
      ∀ u : (Fin N → ℝ) → ℝ, ContDiff ℝ 1 u → HasCompactSupport u →
      MemLp (H1.principalValueConvolution G C.norm k u) (ENNReal.ofReal p) volume ∧
      eLpNorm (H1.principalValueConvolution G C.norm k u) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal (kernelDerivativeBound C.norm k 1 * B) * eLpNorm u (ENNReal.ofReal p) volume := by
  let _metric := gaugeMetric G C.norm C.constant_one C.symmetric
  let _hpFact : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp.le⟩
  obtain ⟨A, S, hA, hS, hcert⟩ := exists_typeZero_geometric_truncated_certificates_of_controlNorm G C hY hhomY
  let D := normalizedLocalLpConstant G C.norm C.constant_one C.symmetric A S hA hS p
  let M : ℝ≥0∞ := volume {x : Fin N → ℝ | 1 ≤ C.norm x ∧ C.norm x ≤ 2}
  have hM : M < ⊤ := (measure_mono (show {x : Fin N → ℝ | 1 ≤ C.norm x ∧ C.norm x ≤ 2} ⊆
      {x | C.norm x ≤ 2} from fun _ hx => hx.2)).trans_lt
        (G2.isCompact_gauge_le C.norm.gauge 2).measure_lt_top
  let B := max 0 D + M.toReal + 1
  have hB : 0 < B := by dsimp only [B]; linarith [le_max_left (0 : ℝ) D, ENNReal.toReal_nonneg (a := M)]
  refine ⟨B, hB, ?_⟩
  intro k hk u hu hs
  obtain ⟨Hk, Hkt⟩ := hcert k hk
  have hbase := compactPrincipalValue_global_eLpNorm_bound_of_truncatedKernelFacts G C.norm C.constant_one C.symmetric
    A S hA hS k Hk Hkt hk hp u hu hs
  have hraw : MemLp (H1.principalValueConvolution G C.norm k u) (ENNReal.ofReal p) volume ∧
      eLpNorm (H1.principalValueConvolution G C.norm k u) (ENNReal.ofReal p) volume ≤
      (ENNReal.ofReal (kernelDerivativeBound C.norm k 1 * D) + ENNReal.ofReal (kernelDerivativeBound C.norm k 1) * M) *
      eLpNorm u (ENNReal.ofReal p) volume := by
    simpa only [ControlCarrier, controlCarrierMeasureSpace, D, M] using hbase
  refine ⟨hraw.1, hraw.2.trans (mul_le_mul' ?_ le_rfl)⟩
  have hΛ : 0 ≤ kernelDerivativeBound C.norm k 1 := (kernelDerivativeBound_properties C.norm.gauge hk.smooth 1).1
  have hD : D ≤ max 0 D := le_max_right _ _
  calc
    _ ≤ ENNReal.ofReal (kernelDerivativeBound C.norm k 1 * max 0 D) +
        ENNReal.ofReal (kernelDerivativeBound C.norm k 1) * M :=
      add_le_add (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hD hΛ)) le_rfl
    _ = ENNReal.ofReal (kernelDerivativeBound C.norm k 1 * (max 0 D + M.toReal)) := by
      rw [← ENNReal.ofReal_toReal hM.ne, ← ENNReal.ofReal_mul hΛ,
        ← ENNReal.ofReal_add (mul_nonneg hΛ (le_max_left _ _)) (mul_nonneg hΛ ENNReal.toReal_nonneg)]
      rw [ENNReal.toReal_ofReal ENNReal.toReal_nonneg]
      congr 1
      ring
    _ ≤ _ := ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (by dsimp only [B]; linarith) hΛ)

end RothschildStein.H3
