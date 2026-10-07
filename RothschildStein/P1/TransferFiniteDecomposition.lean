-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.TransferErrorLinearity

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set
namespace RothschildStein.P1.LiftedChart
variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  (C : LiftedChart w s Ω hΩ X x₀ m) (F : KernelFrame (n+m))

/-- A principal kernel input fiber is
differentiable off the diagonal on the actual frame chart
(BB Theorem 11.24, pp. 555–558). -/
theorem transferPrincipal_input_differentiableAt (hF : C.IsLiftedFrame F)
    (t : PrincipalTerm F) {ξ η : Fin (n+m) → ℝ}
    (hξ : ξ ∈ C.U) (hη : η ∈ C.U) (hne : ξ ≠ η) :
    DifferentiableAt ℝ (t.kernel ξ) η := by
  have hd := C.hasFDerivAt_transfer_input_kernel
    ((t.modelKernel_contDiffOn (hF.pole_smooth t.star)).of_le (by simp)) hξ hη hne
  have hp := (((t.b.contDiff.differentiable (by simp) η).hasFDerivAt).const_mul (t.a ξ)).mul hd
  change DifferentiableAt ℝ (fun ζ => t.kernel ξ ζ) η
  simpa only [Pi.mul_def, PrincipalTerm.kernel, PrincipalTerm.modelKernel, hF.Θ_eq] using hp.differentiableAt

/-- Transfer errors commute with a finite
smooth-kernel decomposition plus a regular remainder. The expression
is assembled at the actual endpoints, before any limiting procedure
(BB Theorem 11.24, pp. 555–558). -/
theorem regularTransferErrorKernel_listSum_add {ι : Type*} (i : Fin k)
    (l : List ι) (f : ι → (Fin (n+m) → ℝ) → (Fin (n+m) → ℝ) → ℝ)
    (r : (Fin (n+m) → ℝ) → (Fin (n+m) → ℝ) → ℝ)
    {ξ η : Fin (n+m) → ℝ} (hξ : ξ ∈ C.U) (hη : η ∈ C.U) (hΘ : F.Θ = C.Θ)
    (hfo : ∀ t ∈ l, DifferentiableAt ℝ (fun ζ => f t ζ η) ξ)
    (hfi : ∀ t ∈ l, DifferentiableAt ℝ (f t ξ) η)
    (hro : DifferentiableAt ℝ (fun ζ => r ζ η) ξ)
    (hri : DifferentiableAt ℝ (r ξ) η) :
    C.regularTransferErrorKernel F i (fun x y => (l.map (fun t => f t x y)).sum + r x y) ξ η =
      (l.map (fun t => C.regularTransferErrorKernel F i (f t) ξ η)).sum +
        C.regularTransferErrorKernel F i r ξ η := by
  induction l with
  | nil => simp only [List.map_nil, List.sum_nil, zero_add]
  | cons a l ih =>
    have hlo := fun t ht => hfo t (List.mem_cons_of_mem a ht)
    have hli := fun t ht => hfi t (List.mem_cons_of_mem a ht)
    have hso := (differentiableAt_and_fieldDerivative_listSum l
      (fun t ζ => f t ζ η) (C.Xl i) ξ hlo).1
    have hsi := (differentiableAt_and_fieldDerivative_listSum l
      (fun t ζ => f t ξ ζ) (C.Xl i) η hli).1
    have he : (fun x y => ((a :: l).map (fun t => f t x y)).sum + r x y) =
        fun x y => f a x y + ((l.map (fun t => f t x y)).sum + r x y) := by
      funext x y; simp only [List.map_cons, List.sum_cons, add_assoc]
    rw [he, C.regularTransferErrorKernel_add F i (f a) _ hξ hη hΘ
      (hfo a List.mem_cons_self) (hso.add hro) (hfi a List.mem_cons_self) (hsi.add hri)]
    rw [ih hlo hli]
    simp only [List.map_cons, List.sum_cons, add_assoc]

end RothschildStein.P1.LiftedChart
