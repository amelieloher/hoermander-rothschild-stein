-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.ComplexL2Pullback
public import HeatKernel.Kernel.TranslationKernel

/-! # Complex unitary translation and real representative compatibility

Left translation acts unitarily on complex Lebesgue L². A real embedding with
its scalar almost-everywhere formula intertwines the real and complex actions.
-/

@[expose] public section

noncomputable section

open MeasureTheory RothschildStein

namespace HeatKernel

/-- Unitary complex L² pullback by homogeneous-group left translation. -/
def complexLeftTranslationL2 {n : ℕ} (G : HomogeneousGroup n) (a : Fin n → ℝ) :
    Lp ℂ 2 (volume : Measure (Fin n → ℝ)) ≃ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure (Fin n → ℝ)) :=
  complexMeasurePreservingL2Equiv volume (G2.leftTranslationHomeomorph G a).toMeasurableEquiv
    (G2.measurePreserving_leftTranslation G a)

/-- The complex unitary translation has the literal pullback representative. -/
theorem ae_complexLeftTranslationL2_apply {n : ℕ} (G : HomogeneousGroup n) (a : Fin n → ℝ)
    (f : Lp ℂ 2 (volume : Measure (Fin n → ℝ))) :
    complexLeftTranslationL2 G a f =ᵐ[volume] fun x => f (G.mul a x) :=
  ae_complexMeasurePreservingL2Equiv_apply volume
    (G2.leftTranslationHomeomorph G a).toMeasurableEquiv (G2.measurePreserving_leftTranslation G a) f

/-- Real and complex unitary translations intertwine through an embedding with the scalar real representative formula. -/
theorem complexLeftTranslationL2_apply_real_embedding {n : ℕ}
    (G : HomogeneousGroup n) (a : Fin n → ℝ)
    (j : Lp ℝ 2 (volume : Measure (Fin n → ℝ)) → Lp ℂ 2 (volume : Measure (Fin n → ℝ)))
    (hj : ∀ f, j f =ᵐ[volume] fun x => (f x : ℂ))
    (f : Lp ℝ 2 (volume : Measure (Fin n → ℝ))) :
    complexLeftTranslationL2 G a (j f) = j (leftTranslationL2 G a f) := by
  apply Lp.ext
  filter_upwards [ae_complexLeftTranslationL2_apply G a (j f),
    (G2.measurePreserving_leftTranslation G a).quasiMeasurePreserving.ae_eq_comp (hj f),
    hj (leftTranslationL2 G a f), ae_leftTranslationL2_apply G a f] with x hleft hcomp hjleft hreal
  change j f (G.mul a x) = (f (G.mul a x) : ℂ) at hcomp
  rw [hleft, hcomp, hjleft, hreal]

end HeatKernel
