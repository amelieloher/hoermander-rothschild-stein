-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.CompactEvaluation
public import HeatKernel.Kernel.KernelComposition
public import Mathlib.MeasureTheory.Function.L2Space

/-! # Point evaluations of continuous semigroup representatives

Positive-time continuous representatives determine bounded evaluation maps. The
semigroup identity passes to these maps by full support of Lebesgue measure.
-/

@[expose] public section

noncomputable section

open MeasureTheory

namespace HeatKernel

variable {n : ℕ}

/-- Bounded positive-time evaluation, extended by zero at nonpositive times. -/
def heatRepresentativeEvaluation
    (T : ℝ → Lp ℝ 2 (volume : Measure (Fin n → ℝ)) →L[ℝ]
      Lp ℝ 2 (volume : Measure (Fin n → ℝ)))
    (u : ℝ → Lp ℝ 2 (volume : Measure (Fin n → ℝ)) → (Fin n → ℝ) → ℝ)
    (hu : ∀ t, 0 < t → ∀ f, Continuous (u t f))
    (hae : ∀ t, 0 < t → ∀ f, T t f =ᵐ[volume] u t f)
    (t : ℝ) (x : Fin n → ℝ) : Lp ℝ 2 (volume : Measure (Fin n → ℝ)) →L[ℝ] ℝ :=
  if ht : 0 < t then euclideanL2RepresentativeEvaluation (T t) (u t) (hu t ht) (hae t ht) x
  else 0

/-- Positive-time evaluation is the prescribed continuous representative. -/
@[simp] theorem heatRepresentativeEvaluation_apply
    (T : ℝ → Lp ℝ 2 (volume : Measure (Fin n → ℝ)) →L[ℝ]
      Lp ℝ 2 (volume : Measure (Fin n → ℝ)))
    (u : ℝ → Lp ℝ 2 (volume : Measure (Fin n → ℝ)) → (Fin n → ℝ) → ℝ)
    (hu : ∀ t, 0 < t → ∀ f, Continuous (u t f))
    (hae : ∀ t, 0 < t → ∀ f, T t f =ᵐ[volume] u t f)
    {t : ℝ} (ht : 0 < t) (x : Fin n → ℝ) (f : Lp ℝ 2 (volume : Measure (Fin n → ℝ))) :
    heatRepresentativeEvaluation T u hu hae t x f = u t f x := by
  simp [heatRepresentativeEvaluation, ht]

/-- The semigroup identity holds at every point for positive-time evaluations. -/
theorem heatRepresentativeEvaluation_add
    (T : ℝ → Lp ℝ 2 (volume : Measure (Fin n → ℝ)) →L[ℝ]
      Lp ℝ 2 (volume : Measure (Fin n → ℝ)))
    (u : ℝ → Lp ℝ 2 (volume : Measure (Fin n → ℝ)) → (Fin n → ℝ) → ℝ)
    (hu : ∀ t, 0 < t → ∀ f, Continuous (u t f))
    (hae : ∀ t, 0 < t → ∀ f, T t f =ᵐ[volume] u t f)
    (hsemigroup : ∀ s t, 0 ≤ s → 0 ≤ t → T (s + t) = (T s).comp (T t))
    {s t : ℝ} (hs : 0 ≤ s) (ht : 0 < t) (x : Fin n → ℝ)
    (f : Lp ℝ 2 (volume : Measure (Fin n → ℝ))) :
    heatRepresentativeEvaluation T u hu hae (t + s) x f =
      heatRepresentativeEvaluation T u hu hae t x (T s f) := by
  have hts : 0 < t + s := add_pos_of_pos_of_nonneg ht hs
  rw [heatRepresentativeEvaluation_apply T u hu hae hts,
    heatRepresentativeEvaluation_apply T u hu hae ht]
  have heq : u (t + s) f =ᵐ[volume] u t (T s f) := by
    have h := (hae (t + s) hts f).symm
    rw [hsemigroup t s ht.le hs] at h
    exact h.trans (hae t ht (T s f))
  exact congrFun (Measure.eq_of_ae_eq heq (hu _ hts f) (hu _ ht (T s f))) x

/-- Self-adjointness identifies each positive-time kernel row with its L² Riesz vector. -/
theorem ae_heatRepresentativeKernel_eq_evaluationVector
    (T : ℝ → Lp ℝ 2 (volume : Measure (Fin n → ℝ)) →L[ℝ]
      Lp ℝ 2 (volume : Measure (Fin n → ℝ)))
    (u : ℝ → Lp ℝ 2 (volume : Measure (Fin n → ℝ)) → (Fin n → ℝ) → ℝ)
    (hu : ∀ t, 0 < t → ∀ f, Continuous (u t f))
    (hae : ∀ t, 0 < t → ∀ f, T t f =ᵐ[volume] u t f)
    (hself : ∀ s, 0 ≤ s → IsSelfAdjoint (T s))
    (hsemigroup : ∀ s t, 0 ≤ s → 0 ≤ t → T (s + t) = (T s).comp (T t))
    {t : ℝ} (ht : 0 < t) (x : Fin n → ℝ) :
    (fun y => evaluationKernel (heatRepresentativeEvaluation T u hu hae) t x y) =ᵐ[volume]
      (evaluationVector (heatRepresentativeEvaluation T u hu hae t) x :
        Lp ℝ 2 (volume : Measure (Fin n → ℝ))) := by
  have ht₂ : 0 < t / 2 := half_pos ht
  apply ae_evaluationKernel_eq_representation volume
    (heatRepresentativeEvaluation T u hu hae) T (fun f => (f : (Fin n → ℝ) → ℝ)) ht
    (hself _ ht₂.le)
    (fun x f => heatRepresentativeEvaluation_add T u hu hae hsemigroup ht₂.le ht₂ x f)
  intro f
  simpa only [heatRepresentativeEvaluation_apply T u hu hae ht₂] using (hae _ ht₂ f).symm

end HeatKernel
