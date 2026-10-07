-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.C.Induction.Facts
public import Hormander.B.Mollifier.Uncut

@[expose] public section

noncomputable section

namespace Hormander.C

open Hormander.B

variable {N : ℕ}

/-- The algebraic identity `[A², T] = 2 [A,T] A + [A,[A,T]]`. -/
theorem comm_sq_left (A T : Operator N) :
    operatorComm (A.comp A) T =
      (2 : ℂ) • (operatorComm A T).comp A + operatorComm A (operatorComm A T) := by
  ext u : 1
  simp only [operatorComm, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
    LinearMap.smul_apply, map_sub]
  rw [two_smul]
  abel

theorem comm_diffusion_expand {k : ℕ} (X : Fin (k + 1) → RealSchwartzVectorField N)
    (c : SchwartzMap (Carrier N) ℝ) (T : Operator N) :
    operatorComm (diffusionOperator X c) T =
      (∑ i : Fin k, operatorComm ((vectorFieldOperator (X i.succ)).comp
          (vectorFieldOperator (X i.succ))) T) +
        operatorComm (vectorFieldOperator (X 0)) T + operatorComm (realMultiplierOperator c) T := by
  unfold diffusionOperator
  rw [operatorComm_add_left, operatorComm_add_left, operatorComm_sum_left]

/-- Decompose the commutator as `[L,T] = ∑ⱼ Tⱼ Xⱼ + T₀` with `Tⱼ, T₀ ∈ 𝓞^σ`. -/
theorem commutator_left_decomposition_of_B10 (F : B10Facts N) {k : ℕ}
    (X : Fin (k + 1) → RealSchwartzVectorField N) (c : SchwartzMap (Carrier N) ℝ)
    {σ : ℝ} {T : Operator N} (hT : OperatorClass σ T) :
    ∃ (Tj : Fin k → Operator N) (T0 : Operator N),
      (∀ j, OperatorClass σ (Tj j)) ∧ OperatorClass σ T0 ∧
      operatorComm (diffusionOperator X c) T =
        (∑ j : Fin k, (Tj j).comp (vectorFieldOperator (X j.succ))) + T0 := by
  have h1 : ∀ j : Fin k, OperatorClass σ (operatorComm (vectorFieldOperator (X j.succ)) T) :=
    fun j => F.comm_vectorField σ T _ hT
  have h2 : ∀ j : Fin k, OperatorClass σ
      (operatorComm (vectorFieldOperator (X j.succ)) (operatorComm (vectorFieldOperator (X j.succ)) T)) :=
    fun j => F.comm_vectorField σ _ _ (h1 j)
  have h3 : OperatorClass σ (operatorComm (vectorFieldOperator (X 0)) T) :=
    F.comm_vectorField σ T _ hT
  have h4 : OperatorClass σ (operatorComm (realMultiplierOperator c) T) :=
    F.mono_mem _ _ _ (F.comm_multiplier σ T c hT) (by linarith)
  refine ⟨fun j => (2 : ℂ) • operatorComm (vectorFieldOperator (X j.succ)) T,
    (∑ j : Fin k, operatorComm (vectorFieldOperator (X j.succ))
        (operatorComm (vectorFieldOperator (X j.succ)) T)) +
      operatorComm (vectorFieldOperator (X 0)) T + operatorComm (realMultiplierOperator c) T,
    fun j => F.smul_mem σ 2 _ (h1 j), ?_, ?_⟩
  · exact F.add_mem σ _ _ (F.add_mem σ _ _ (F.sum_mem _ _ σ fun j _ => h2 j) h3) h4
  · rw [comm_diffusion_expand]
    simp only [comm_sq_left, LinearMap.smul_comp, Finset.sum_add_distrib]
    abel

end Hormander.C
