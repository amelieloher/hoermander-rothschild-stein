-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.TypeZeroUnitHolderSmooth
public import RothschildStein.H3.TypeZeroPrincipalValueDilation
public import RothschildStein.H3.HolderDilationNormBound

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Metric
open scoped NNReal ENNReal
namespace RothschildStein.H3

/-- The universal full PV Hölder estimate on any fixed positive-radius
ball, for compact C1 sources. The constant precedes both kernel and source. -/
theorem exists_typeZero_radius_holder_bound_smooth_of_controlNorm {N q : ℕ}
    (G : HomogeneousGroup N)
    {Y : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ)}
    (C : G2.ControlNormConclusion G driftWeight Y)
    (hY : ∀ i, ContinuousOn (Y i) {0}ᶜ)
    (hhomY : ∀ i, G2.IsHomogeneousField G (Y i) (if i = 0 then 2 else 1))
    {a : ℝ≥0} (ha : 0 < a) (ha1 : (a : ℝ) < 1) {R : ℝ} (hR : 0 < R) :
    let _metric := gaugeMetric G C.norm C.constant_one C.symmetric
    let E := ball (0 : ControlCarrier N) R
    ∃ B : ℝ, 0 < B ∧ ∀ (k : (Fin N → ℝ) → ℝ), TypeZero G C.norm k →
      ∀ (F : ControlCarrier N → ℝ), ContDiff ℝ 1 (fun x : Fin N → ℝ => F x) →
      HasCompactSupport F → tsupport F ⊆ E → H2.BoundedHolder a E F →
      H2.boundedHolderNorm a E (fun x : ControlCarrier N => H1.principalValueConvolution G C.norm k
        (fun y : Fin N → ℝ => F y) x) ≤
        ENNReal.ofReal (kernelDerivativeBound C.norm k 1 * B) * H2.boundedHolderNorm a E F := by
  let _metric := gaugeMetric G C.norm C.constant_one C.symmetric
  let E := ball (0 : ControlCarrier N) R
  let U := ball (0 : ControlCarrier N) 1
  let d := max 1 (R ^ (a : ℝ))
  let e := max 1 (R⁻¹ ^ (a : ℝ))
  have hd : 0 < d := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have he : 0 < e := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hball (r : ℝ) : ball (0 : ControlCarrier N) r = {x | C.norm x < r} := by
    ext x
    change C.norm (G.mul (G.inv 0) x) < r ↔ C.norm x < r
    rw [G2.inv_zero, G2.zero_mul]
  have hpre : (fun x : ControlCarrier N => G.dilate R x) ⁻¹' E = U := by
    ext x
    simp only [E, U, hball, mem_preimage, mem_ofPred_eq, C.norm.gauge.2.2.2 R hR]
    change R * C.norm x < R ↔ C.norm x < 1
    constructor <;> intro hx <;> nlinarith
  have hpreInv : (fun x : ControlCarrier N => G.dilate R⁻¹ x) ⁻¹' U = E := by
    ext x
    simp only [E, U, hball, mem_preimage, mem_ofPred_eq, C.norm.gauge.2.2.2 R⁻¹ (inv_pos.mpr hR)]
    change R⁻¹ * C.norm x < 1 ↔ C.norm x < R
    constructor
    · intro hx
      have hh := mul_lt_mul_of_pos_left hx hR
      simpa [← mul_assoc, hR.ne'] using hh
    · intro hx
      have hh := mul_lt_mul_of_pos_left hx (inv_pos.mpr hR)
      simpa [hR.ne'] using hh
  obtain ⟨B₀, hB₀, hunit⟩ := exists_typeZero_unit_holder_bound_smooth_of_controlNorm G C hY hhomY ha ha1
  dsimp only
  refine ⟨e * B₀ * d, mul_pos (mul_pos he hB₀) hd, ?_⟩
  intro k hk F hF hc hs hf
  let f : ControlCarrier N → ℝ := fun x => F (G.dilate R x)
  have hfc : HasCompactSupport f := hc.comp_homeomorph (G2.dilationHomeomorph G R hR)
  have hfs : tsupport f ⊆ U := by
    rw [← hpre]
    exact (tsupport_comp_subset_preimage F (G2.continuous_dilate G R)).trans (preimage_mono hs)
  have hn := holderNorm_dilate_le G C.norm C.constant_one C.symmetric hR a E F hf
  rw [hpre] at hn
  have hfh : H2.BoundedHolder a U f := hn.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf)
  have hp := hunit k hk f (hF.comp ((G2.contDiff_dilate G R).of_le (by simp))) hfc hfs hfh
  let P : ControlCarrier N → ℝ := fun x => H1.principalValueConvolution G C.norm k
    (fun y : Fin N → ℝ => f y) x
  have hPh : H2.BoundedHolder a U P := hp.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfh)
  have hi := holderNorm_dilate_le G C.norm C.constant_one C.symmetric (inv_pos.mpr hR) a U P hPh
  rw [hpreInv] at hi
  have hPeq : (fun x : ControlCarrier N => P (G.dilate R⁻¹ x)) =
      (fun x : ControlCarrier N => H1.principalValueConvolution G C.norm k (fun y : Fin N → ℝ => F y) x) := by
    funext x
    change H1.principalValueConvolution G C.norm k (fun y => F (G.dilate R y)) (G.dilate R⁻¹ x) = _
    rw [hk.principalValue_dilate G hF hc hR]
    dsimp only
    apply congrArg (fun z : Fin N → ℝ => H1.principalValueConvolution G C.norm k (fun y : Fin N → ℝ => F y) z)
    rw [G2.dilate_dilate, mul_inv_cancel₀ hR.ne', G2.dilate_one]
  rw [hPeq] at hi
  have hΛ : 0 ≤ kernelDerivativeBound C.norm k 1 := (kernelDerivativeBound_properties C.norm.gauge hk.smooth 1).1
  calc
    _ ≤ ENNReal.ofReal e * H2.boundedHolderNorm a U P := hi
    _ ≤ ENNReal.ofReal e * (ENNReal.ofReal (kernelDerivativeBound C.norm k 1 * B₀) *
        (ENNReal.ofReal d * H2.boundedHolderNorm a E F)) :=
      mul_le_mul' le_rfl (hp.trans (mul_le_mul' le_rfl hn))
    _ = _ := by
      rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul he.le,
        ← ENNReal.ofReal_mul (mul_nonneg he.le (mul_nonneg hΛ hB₀.le))]
      congr 2
      ring

end RothschildStein.H3
