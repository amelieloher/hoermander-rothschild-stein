-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.HalfRadiusConditional

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory
open scoped ENNReal
variable {n q : ℕ}

/-- The half-radius estimate bounds each second weak word by global
input and operator norms plus the inverse-square remainder. -/
theorem secondWord_bound_of_halfRadiusEstimate
    (G : HomogeneousGroup n) (ν : G2.HomogeneousNorm G)
    (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (p : ℝ≥0∞) (K : ℝ) (hK : 0 ≤ K) (hest : HalfRadiusEstimate G ν X p K)
    {u g : (Fin n → ℝ) → ℝ} (hu : MemLp u p (volume : Measure (Fin n → ℝ)))
    (hg : MemLp g p (volume : Measure (Fin n → ℝ)))
    {R : ℝ} (hR : 0 < R)
    (hlocal : memSobolevX driftWeight X (quasiballDomain G ν 0 R) 2 p u)
    (D : WeakDriftOperatorData X (quasiballDomain G ν 0 R) p u)
    (hoperator : D.operator =ᵐ[volume.restrict (G2.gaugeBall G ν 0 R)] g)
    (I : List (Fin (q + 1))) (hI : wordWeight driftWeight I = 2) :
    weakWordENorm X (quasiballDomain G ν 0 (R / 2)) I p u ≤
      ENNReal.ofReal (K * ((eLpNorm g p volume).toReal +
        R⁻¹ ^ 2 * (eLpNorm u p volume).toReal)) := by
  have hsmall := memSobolevX_quasiball_restrict G ν 0 (by linarith : R / 2 ≤ R)
    driftWeight X 2 p u hlocal
  have hsecondfin := driftSecondWeakENorm_lt_top X _ p u hsmall
  have hwordfin := weakWordENorm_lt_top_of_memSobolev driftWeight X _ 2 p u hsmall I
    (by simp only [S.mem_wordFamily_iff]; omega)
  have hword : weakWordENorm X (quasiballDomain G ν 0 (R / 2)) I p u ≤
      driftSecondWeakENorm X (quasiballDomain G ν 0 (R / 2)) p u := by
    unfold driftSecondWeakENorm
    exact Finset.single_le_sum (f := fun J => weakWordENorm X (quasiballDomain G ν 0 (R / 2)) J p u) (fun _ _ => by positivity) ((mem_driftSecondWordFamily_iff I).mpr hI)
  have hwordreal := ENNReal.toReal_mono hsecondfin.ne hword
  have hop : (eLpNorm D.operator p (volume.restrict (G2.gaugeBall G ν 0 R))).toReal ≤
      (eLpNorm g p volume).toReal := by
    rw [eLpNorm_congr_ae hoperator]
    exact ENNReal.toReal_mono hg.eLpNorm_lt_top.ne
      (eLpNorm_mono_measure g Measure.restrict_le_self)
  have huR : (eLpNorm u p (volume.restrict (G2.gaugeBall G ν 0 R))).toReal ≤
      (eLpNorm u p volume).toReal :=
    ENNReal.toReal_mono hu.eLpNorm_lt_top.ne (eLpNorm_mono_measure u Measure.restrict_le_self)
  have hh := hest 0 R hR u hlocal D
  have hfirst : 0 ≤ R⁻¹ * (horizontalWeakENorm X (quasiballDomain G ν 0 (R / 2)) p u).toReal :=
    mul_nonneg (inv_nonneg.mpr hR.le) ENNReal.toReal_nonneg
  have hzero : 0 ≤ R⁻¹ ^ 2 * (eLpNorm u p (volume.restrict (G2.gaugeBall G ν 0 (R / 2)))).toReal :=
    mul_nonneg (sq_nonneg _) ENNReal.toReal_nonneg
  have hb : (driftSecondWeakENorm X (quasiballDomain G ν 0 (R / 2)) p u).toReal ≤
      K * ((eLpNorm D.operator p (volume.restrict (G2.gaugeBall G ν 0 R))).toReal +
        R⁻¹ ^ 2 * (eLpNorm u p (volume.restrict (G2.gaugeBall G ν 0 R))).toReal) := by
    linarith
  have hb' := hb.trans (mul_le_mul_of_nonneg_left
    (add_le_add hop (mul_le_mul_of_nonneg_left huR (sq_nonneg _))) hK)
  calc
    _ = ENNReal.ofReal (weakWordENorm X (quasiballDomain G ν 0 (R / 2)) I p u).toReal :=
      (ENNReal.ofReal_toReal hwordfin.ne).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (hwordreal.trans hb')

end RothschildStein.H3
