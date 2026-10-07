-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.E.OneStepFinal.Operators

@[expose] public section

noncomputable section

open MeasureTheory SchwartzMap

namespace Hormander.E
open Hormander.B

variable {N : ℕ}

theorem ring_first {R : Type*} [Ring R] (x A : R) :
    x * x * A - A * (x * x) =
      (x * (x * A - A * x) + x * (x * A - A * x)) +
        ((x * A - A * x) * x - x * (x * A - A * x)) := by
  noncomm_ring

theorem ring_second {R : Type*} [Ring R] (x A : R) :
    x * x * A - A * (x * x) =
      ((x * A - A * x) * x + (x * A - A * x) * x) +
        (x * (x * A - A * x) - (x * A - A * x) * x) := by
  noncomm_ring

section
variable {k : ℕ} (Vs : Fin (k + 1) → RealSchwartzVectorField N) (cs : SchwartzMap (Carrier N) ℝ)

/-- First commutator form: `[L, A] = Σ_j (2 X_j [X_j, A] + [[X_j, A], X_j]) + [X₀, A] + [c, A]`. -/
theorem comm_diffusion_first (A : Operator N) :
    operatorComm (Hormander.C.diffusionOperator Vs cs) A =
      ∑ j : Fin k, ((2 : ℂ) • (vectorFieldOperator (Vs j.succ)).comp
          (operatorComm (vectorFieldOperator (Vs j.succ)) A) +
        operatorComm (operatorComm (vectorFieldOperator (Vs j.succ)) A)
          (vectorFieldOperator (Vs j.succ))) +
      operatorComm (vectorFieldOperator (Vs 0)) A + operatorComm (realMultiplierOperator cs) A := by
  unfold Hormander.C.diffusionOperator operatorComm
  simp only [← Module.End.mul_eq_comp]
  have h1 : ∀ j : Fin k, (2 : ℂ) • (vectorFieldOperator (Vs j.succ) *
        (vectorFieldOperator (Vs j.succ) * A - A * vectorFieldOperator (Vs j.succ))) +
      ((vectorFieldOperator (Vs j.succ) * A - A * vectorFieldOperator (Vs j.succ)) *
          vectorFieldOperator (Vs j.succ) -
        vectorFieldOperator (Vs j.succ) *
          (vectorFieldOperator (Vs j.succ) * A - A * vectorFieldOperator (Vs j.succ))) =
      vectorFieldOperator (Vs j.succ) * vectorFieldOperator (Vs j.succ) * A -
        A * (vectorFieldOperator (Vs j.succ) * vectorFieldOperator (Vs j.succ)) := by
    intro j
    rw [two_smul]
    exact (ring_first _ _).symm
  simp only [h1]
  rw [add_mul, add_mul, mul_add, mul_add, Finset.sum_mul, Finset.mul_sum, Finset.sum_sub_distrib]
  abel

/-- Second commutator form: `[L, B] = Σ_j (2 [X_j, B] X_j + [X_j, [X_j, B]]) + [X₀, B] + [c, B]`. -/
theorem comm_diffusion_second (A : Operator N) :
    operatorComm (Hormander.C.diffusionOperator Vs cs) A =
      ∑ j : Fin k, ((2 : ℂ) • (operatorComm (vectorFieldOperator (Vs j.succ)) A).comp
          (vectorFieldOperator (Vs j.succ)) +
        operatorComm (vectorFieldOperator (Vs j.succ))
          (operatorComm (vectorFieldOperator (Vs j.succ)) A)) +
      operatorComm (vectorFieldOperator (Vs 0)) A + operatorComm (realMultiplierOperator cs) A := by
  unfold Hormander.C.diffusionOperator operatorComm
  simp only [← Module.End.mul_eq_comp]
  have h1 : ∀ j : Fin k, (2 : ℂ) • ((vectorFieldOperator (Vs j.succ) * A -
          A * vectorFieldOperator (Vs j.succ)) * vectorFieldOperator (Vs j.succ)) +
      (vectorFieldOperator (Vs j.succ) *
          (vectorFieldOperator (Vs j.succ) * A - A * vectorFieldOperator (Vs j.succ)) -
        (vectorFieldOperator (Vs j.succ) * A - A * vectorFieldOperator (Vs j.succ)) *
          vectorFieldOperator (Vs j.succ)) =
      vectorFieldOperator (Vs j.succ) * vectorFieldOperator (Vs j.succ) * A -
        A * (vectorFieldOperator (Vs j.succ) * vectorFieldOperator (Vs j.succ)) := by
    intro j
    rw [two_smul]
    exact (ring_second _ _).symm
  simp only [h1]
  rw [add_mul, add_mul, mul_add, mul_add, Finset.sum_mul, Finset.mul_sum, Finset.sum_sub_distrib]
  abel

/-- Distributional form of the first commutator expansion. -/
theorem Eop_diffusion_comp_first (A : Operator N) [hA : HCT A] (u : Tempered N) :
    Eop ((Hormander.C.diffusionOperator Vs cs).comp A) u =
      Eop A (Eop (Hormander.C.diffusionOperator Vs cs) u) +
      ∑ j : Fin k, ((2 : ℂ) • Eop (vectorFieldOperator (Vs j.succ))
          (Eop (operatorComm (vectorFieldOperator (Vs j.succ)) A) u) +
        Eop (operatorComm (operatorComm (vectorFieldOperator (Vs j.succ)) A)
          (vectorFieldOperator (Vs j.succ))) u) +
      Eop (operatorComm (vectorFieldOperator (Vs 0)) A) u +
      Eop (operatorComm (realMultiplierOperator cs) A) u := by
  have e : (Hormander.C.diffusionOperator Vs cs).comp A =
      A.comp (Hormander.C.diffusionOperator Vs cs) +
        (∑ j : Fin k, ((2 : ℂ) • (vectorFieldOperator (Vs j.succ)).comp
          (operatorComm (vectorFieldOperator (Vs j.succ)) A) +
        operatorComm (operatorComm (vectorFieldOperator (Vs j.succ)) A)
          (vectorFieldOperator (Vs j.succ))) +
      operatorComm (vectorFieldOperator (Vs 0)) A + operatorComm (realMultiplierOperator cs) A) := by
    rw [← comm_diffusion_first]
    unfold operatorComm
    abel
  have hj : ∀ j ∈ (Finset.univ : Finset (Fin k)), HasContinuousTranspose
      ((2 : ℂ) • (vectorFieldOperator (Vs j.succ)).comp
          (operatorComm (vectorFieldOperator (Vs j.succ)) A) +
        operatorComm (operatorComm (vectorFieldOperator (Vs j.succ)) A)
          (vectorFieldOperator (Vs j.succ))) := fun j _ => HCT.out
  have hjterm : ∀ j : Fin k, Eop ((2 : ℂ) • (vectorFieldOperator (Vs j.succ)).comp
          (operatorComm (vectorFieldOperator (Vs j.succ)) A) +
        operatorComm (operatorComm (vectorFieldOperator (Vs j.succ)) A)
          (vectorFieldOperator (Vs j.succ))) u =
      (2 : ℂ) • Eop (vectorFieldOperator (Vs j.succ))
          (Eop (operatorComm (vectorFieldOperator (Vs j.succ)) A) u) +
        Eop (operatorComm (operatorComm (vectorFieldOperator (Vs j.succ)) A)
          (vectorFieldOperator (Vs j.succ))) u := by
    intro j
    rw [Eop_add HCT.out HCT.out, Eop_smul _ HCT.out, Eop_comp HCT.out HCT.out]
    rfl
  have hs : Eop (∑ j : Fin k, ((2 : ℂ) • (vectorFieldOperator (Vs j.succ)).comp
          (operatorComm (vectorFieldOperator (Vs j.succ)) A) +
        operatorComm (operatorComm (vectorFieldOperator (Vs j.succ)) A)
          (vectorFieldOperator (Vs j.succ)))) u = ∑ j : Fin k, Eop ((2 : ℂ) • (vectorFieldOperator (Vs j.succ)).comp
          (operatorComm (vectorFieldOperator (Vs j.succ)) A) +
        operatorComm (operatorComm (vectorFieldOperator (Vs j.succ)) A)
          (vectorFieldOperator (Vs j.succ))) u := by
    rw [Eop_sum _ _ hj]
    simp
  rw [e, Eop_add HCT.out (HasContinuousTranspose.add
      (HasContinuousTranspose.add (HasContinuousTranspose.sum _ _ hj) HCT.out) HCT.out),
    Eop_add (HasContinuousTranspose.add (HasContinuousTranspose.sum _ _ hj) HCT.out) HCT.out,
    Eop_add (HasContinuousTranspose.sum _ _ hj) HCT.out, Eop_comp HCT.out HCT.out]
  simp only [add_apply, ContinuousLinearMap.comp_apply, hs, hjterm]
  abel

/-- Distributional form of the second commutator expansion. -/
theorem Eop_diffusion_comp_second (A : Operator N) [hA : HCT A] (u : Tempered N) :
    Eop ((Hormander.C.diffusionOperator Vs cs).comp A) u =
      Eop A (Eop (Hormander.C.diffusionOperator Vs cs) u) +
      ∑ j : Fin k, ((2 : ℂ) • Eop (operatorComm (vectorFieldOperator (Vs j.succ)) A)
          (Eop (vectorFieldOperator (Vs j.succ)) u) +
        Eop (operatorComm (vectorFieldOperator (Vs j.succ))
          (operatorComm (vectorFieldOperator (Vs j.succ)) A)) u) +
      Eop (operatorComm (vectorFieldOperator (Vs 0)) A) u +
      Eop (operatorComm (realMultiplierOperator cs) A) u := by
  have e : (Hormander.C.diffusionOperator Vs cs).comp A =
      A.comp (Hormander.C.diffusionOperator Vs cs) +
        (∑ j : Fin k, ((2 : ℂ) • (operatorComm (vectorFieldOperator (Vs j.succ)) A).comp
          (vectorFieldOperator (Vs j.succ)) +
        operatorComm (vectorFieldOperator (Vs j.succ))
          (operatorComm (vectorFieldOperator (Vs j.succ)) A)) +
      operatorComm (vectorFieldOperator (Vs 0)) A + operatorComm (realMultiplierOperator cs) A) := by
    rw [← comm_diffusion_second]
    unfold operatorComm
    abel
  have hj : ∀ j ∈ (Finset.univ : Finset (Fin k)), HasContinuousTranspose
      ((2 : ℂ) • (operatorComm (vectorFieldOperator (Vs j.succ)) A).comp
          (vectorFieldOperator (Vs j.succ)) +
        operatorComm (vectorFieldOperator (Vs j.succ))
          (operatorComm (vectorFieldOperator (Vs j.succ)) A)) := fun j _ => HCT.out
  have hjterm : ∀ j : Fin k, Eop ((2 : ℂ) • (operatorComm (vectorFieldOperator (Vs j.succ)) A).comp
          (vectorFieldOperator (Vs j.succ)) +
        operatorComm (vectorFieldOperator (Vs j.succ))
          (operatorComm (vectorFieldOperator (Vs j.succ)) A)) u =
      (2 : ℂ) • Eop (operatorComm (vectorFieldOperator (Vs j.succ)) A)
          (Eop (vectorFieldOperator (Vs j.succ)) u) +
        Eop (operatorComm (vectorFieldOperator (Vs j.succ))
          (operatorComm (vectorFieldOperator (Vs j.succ)) A)) u := by
    intro j
    rw [Eop_add HCT.out HCT.out, Eop_smul _ HCT.out, Eop_comp HCT.out HCT.out]
    rfl
  have hs : Eop (∑ j : Fin k, ((2 : ℂ) • (operatorComm (vectorFieldOperator (Vs j.succ)) A).comp
          (vectorFieldOperator (Vs j.succ)) +
        operatorComm (vectorFieldOperator (Vs j.succ))
          (operatorComm (vectorFieldOperator (Vs j.succ)) A))) u =
      ∑ j : Fin k, Eop ((2 : ℂ) • (operatorComm (vectorFieldOperator (Vs j.succ)) A).comp
          (vectorFieldOperator (Vs j.succ)) +
        operatorComm (vectorFieldOperator (Vs j.succ))
          (operatorComm (vectorFieldOperator (Vs j.succ)) A)) u := by
    rw [Eop_sum _ _ hj]
    simp
  rw [e, Eop_add HCT.out (HasContinuousTranspose.add
      (HasContinuousTranspose.add (HasContinuousTranspose.sum _ _ hj) HCT.out) HCT.out),
    Eop_add (HasContinuousTranspose.add (HasContinuousTranspose.sum _ _ hj) HCT.out) HCT.out,
    Eop_add (HasContinuousTranspose.sum _ _ hj) HCT.out, Eop_comp HCT.out HCT.out]
  simp only [add_apply, ContinuousLinearMap.comp_apply, hs, hjterm]
  abel

end

end Hormander.E
