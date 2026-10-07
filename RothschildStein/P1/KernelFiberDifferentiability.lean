-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PrincipalFourTermLeibniz
public import RothschildStein.P1.ContinuityPositive

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set
namespace RothschildStein.P1
variable {N : ℕ}

/-- Directional derivatives commute with finite list sums whenever
the actual fibers are differentiable at the evaluation point. -/
theorem differentiableAt_and_fieldDerivative_listSum {ι : Type*} (l : List ι)
    (f : ι → (Fin N → ℝ) → ℝ) (Y : (Fin N → ℝ) → (Fin N → ℝ))
    (ξ : Fin N → ℝ) (hf : ∀ t ∈ l, DifferentiableAt ℝ (f t) ξ) :
    DifferentiableAt ℝ (fun x => (l.map (fun t => f t x)).sum) ξ ∧
    fieldDerivative Y (fun x => (l.map (fun t => f t x)).sum) ξ =
      (l.map (fun t => fieldDerivative Y (f t) ξ)).sum := by
  have h : DifferentiableAt ℝ (fun x => (l.map (fun t => f t x)).sum) ξ ∧
      fieldDerivative Y (fun x => (l.map (fun t => f t x)).sum) ξ =
        (l.map (fun t => fieldDerivative Y (f t) ξ)).sum := by
    induction l with
    | nil =>
      simp only [List.map_nil, List.sum_nil]
      exact ⟨differentiableAt_const 0, by simp [fieldDerivative]⟩
    | cons t l ih =>
      have ht := hf t List.mem_cons_self
      obtain ⟨hd, he⟩ := ih (fun t ht => hf t (List.mem_cons_of_mem _ ht))
      simp only [List.map_cons, List.sum_cons]
      refine ⟨ht.add hd, ?_⟩
      unfold fieldDerivative at he ⊢
      rw [fderiv_fun_add ht hd, add_apply, he]
  exact h

/-- The directional derivative component of the finite list sum identity. -/
theorem fieldDerivative_listSum {ι : Type*} (l : List ι)
    (f : ι → (Fin N → ℝ) → ℝ) (Y : (Fin N → ℝ) → (Fin N → ℝ))
    (ξ : Fin N → ℝ) (hf : ∀ t ∈ l, DifferentiableAt ℝ (f t) ξ) :
    fieldDerivative Y (fun x => (l.map (fun t => f t x)).sum) ξ =
      (l.map (fun t => fieldDerivative Y (f t) ξ)).sum :=
  (differentiableAt_and_fieldDerivative_listSum l f Y ξ hf).2

variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {F : KernelFrame (n + m)}

/-- A principal kernel fiber is differentiable off its pole
on the actual chart, with the endpoint parameter held fixed. -/
theorem LiftedChart.principalKernel_differentiableAt
    (hF : C.IsLiftedFrame F) (t : PrincipalTerm F)
    {ξ η : Fin (n + m) → ℝ} (hξ : ξ ∈ C.U) (hη : η ∈ C.U) (hne : ξ ≠ η) :
    DifferentiableAt ℝ (fun x => t.kernel x η) ξ := by
  have hd := C.hasFDerivAt_kernel
    ((t.modelKernel_contDiffOn (hF.pole_smooth t.star)).of_le (by simp)) hη hξ hne
  have ha := (t.a.contDiff.differentiable (by simp) ξ).hasFDerivAt
  have hp := (ha.mul_const (t.b η)).mul hd
  simpa only [Pi.mul_def, PrincipalTerm.kernel, PrincipalTerm.modelKernel, hF.Θ_eq]
    using hp.differentiableAt

end RothschildStein.P1
