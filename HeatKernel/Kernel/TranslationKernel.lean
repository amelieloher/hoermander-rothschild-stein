-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.L2Pullback
public import HeatKernel.Kernel.RepresentativeCovariance
public import RothschildStein.G2.TransposeInvariance
public import RothschildStein.G2.Measure

/-! # Translation invariance and kernel profiles

Left translations act unitarily on Lebesgue L². Commutation with these maps gives
simultaneous translation invariance of the kernel and its convolution profile.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace HeatKernel

open RothschildStein RothschildStein.G2

/-- Unitary pullback by left translation on a homogeneous group. -/
def leftTranslationL2 {n : ℕ} (G : HomogeneousGroup n) (a : Fin n → ℝ) :
    Lp ℝ 2 (volume : Measure (Fin n → ℝ)) ≃ₗᵢ[ℝ] Lp ℝ 2 (volume : Measure (Fin n → ℝ)) :=
  measurePreservingL2Equiv volume (leftTranslationHomeomorph G a).toMeasurableEquiv
    (measurePreserving_leftTranslation G a)

/-- Left-translation pullback has the expected almost-everywhere representative. -/
theorem ae_leftTranslationL2_apply {n : ℕ} (G : HomogeneousGroup n) (a : Fin n → ℝ)
    (f : Lp ℝ 2 (volume : Measure (Fin n → ℝ))) :
    leftTranslationL2 G a f =ᵐ[volume] fun x => f (G.mul a x) :=
  ae_measurePreservingL2Equiv_apply volume (leftTranslationHomeomorph G a).toMeasurableEquiv
    (measurePreserving_leftTranslation G a) f

variable {n : ℕ} (G : HomogeneousGroup n)
    (T : ℝ → Lp ℝ 2 (volume : Measure (Fin n → ℝ)) →L[ℝ]
      Lp ℝ 2 (volume : Measure (Fin n → ℝ)))
    (u : ℝ → Lp ℝ 2 (volume : Measure (Fin n → ℝ)) → (Fin n → ℝ) → ℝ)
    (hu : ∀ t, 0 < t → ∀ f, Continuous (u t f))
    (hae : ∀ t, 0 < t → ∀ f, T t f =ᵐ[volume] u t f)
    (hcomm : ∀ s, 0 < s → ∀ a f,
      T s (leftTranslationL2 G a f) = leftTranslationL2 G a (T s f))

include hcomm

/-- Translation commutation of the semigroup gives simultaneous pointwise kernel invariance. -/
theorem heatRepresentativeKernel_left_invariant {t : ℝ} (ht : 0 < t)
    (a x y : Fin n → ℝ) :
    evaluationKernel (heatRepresentativeEvaluation T u hu hae) t (G.mul a x) (G.mul a y) =
      evaluationKernel (heatRepresentativeEvaluation T u hu hae) t x y := by
  have hpull : ∀ f, (leftTranslationL2 G a).symm.symm f =ᵐ[volume]
      fun z => (1 : ℝ) * f (G.mul a z) := by
    intro f
    simpa only [LinearIsometryEquiv.symm_symm, one_mul] using ae_leftTranslationL2_apply G a f
  have h := heatRepresentativeKernel_covariance T u hu hae (leftTranslationL2 G a).symm
    (G.mul a) ((contDiff_leftTranslation G a).continuous)
    (measurePreserving_leftTranslation G a).quasiMeasurePreserving 1 hpull ht ht
    one_ne_zero (hcomm (t / 2) (half_pos ht) a) x y
  simpa only [inv_one, one_pow, one_mul] using h

/-- Translation invariance identifies the kernel with its profile at the group identity. -/
theorem heatRepresentativeKernel_eq_profile {t : ℝ} (ht : 0 < t) (x y : Fin n → ℝ) :
    evaluationKernel (heatRepresentativeEvaluation T u hu hae) t x y =
      evaluationKernel (heatRepresentativeEvaluation T u hu hae) t 0 (G.mul (G.inv x) y) := by
  simpa only [inv_mul] using
    (heatRepresentativeKernel_left_invariant G T u hu hae hcomm ht (G.inv x) x y).symm

end HeatKernel
