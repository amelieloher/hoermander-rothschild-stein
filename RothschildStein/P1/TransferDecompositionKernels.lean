-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.TypeTransferErrorKernel
public import RothschildStein.P1.PrincipalCutoffWeakTransfer

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter MvPolynomial
open scoped Topology
namespace RothschildStein.P1.LiftedChart
variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  (C : LiftedChart w s Ω hΩ X x₀ m) (F : KernelFrame (n+m))

/-- Canonical transfer kernels commute with
one finite decomposition off the diagonal. They remain independent
of the chosen regularity budget (BB Theorem 11.24, pp. 555–558). -/
theorem generatorTransferKernel_decomposition {lam : ℕ}
    {κ : (Fin (n+m) → ℝ) → (Fin (n+m) → ℝ) → ℝ}
    (d : TypeDecomposition F lam 1 κ) (i : Fin k) (j : Fin (n+m))
    {ξ η : Fin (n+m) → ℝ} (hne : ξ ≠ η) :
    C.generatorTransferKernel F i j κ ξ η =
      (d.principal.map (fun t => C.generatorTransferKernel F i j t.kernel ξ η)).sum +
        C.generatorTransferKernel F i j d.regular ξ η := by
  simp only [generatorTransferKernel]
  rw [d.eq_off_diagonal ξ η hne, mul_add, List.sum_map_mul_left]

/-- The canonical full error equals the finite
principal errors plus the actual regular remainder error off the
interior diagonal. All coefficient derivatives are retained. -/
theorem cutoffTransferErrorKernel_decomposition (hF : C.IsLiftedFrame F)
    {lam : ℕ} {κ : (Fin (n+m) → ℝ) → (Fin (n+m) → ℝ) → ℝ}
    (d : TypeDecomposition F lam 1 κ) (i : Fin k)
    {ξ η : Fin (n+m) → ℝ}
    (hξ : ξ ∈ (F.V : Set (Fin (n+m) → ℝ)))
    (hη : η ∈ (F.V : Set (Fin (n+m) → ℝ))) (hne : ξ ≠ η) :
    C.cutoffTransferErrorKernel F i κ ξ η =
      (d.principal.map (fun t => C.principalTransferErrorKernel F hF t i ξ η)).sum +
        C.regularTransferErrorKernel F i d.regular ξ η := by
  have hVU : (F.V : Set (Fin (n+m) → ℝ)) ⊆ C.U := subset_closure.trans hF.closure_subset
  let g := fun x y => (d.principal.map (fun t => t.kernel x y)).sum + d.regular x y
  have hgo : (fun x => κ x η) =ᶠ[𝓝 ξ] fun x => g x η := by
    filter_upwards [isOpen_compl_singleton.mem_nhds (by simpa using hne)] with x hx
    exact d.eq_off_diagonal x η (by simpa using hx)
  have hgi : κ ξ =ᶠ[𝓝 η] g ξ := by
    filter_upwards [isOpen_compl_singleton.mem_nhds (by simpa using hne.symm)] with y hy
    exact d.eq_off_diagonal ξ y (Ne.symm (by simpa using hy))
  have hfo (t : PrincipalTerm F) (_ : t ∈ d.principal) :
      DifferentiableAt ℝ (fun x => t.kernel x η) ξ :=
    C.principalKernel_differentiableAt hF t (hVU hξ) (hVU hη) hne
  have hfi (t : PrincipalTerm F) (_ : t ∈ d.principal) :
      DifferentiableAt ℝ (t.kernel ξ) η :=
    C.transferPrincipal_input_differentiableAt F hF t (hVU hξ) (hVU hη) hne
  have hro : DifferentiableAt ℝ (fun x => d.regular x η) ξ :=
    (d.regular_isRegular.1.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) ξ
  have hri : DifferentiableAt ℝ (d.regular ξ) η :=
    (d.regular_isRegular.1.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp) η
  simp only [cutoffTransferErrorKernel, ite_eq_left (show ξ ∈ (F.V : Set (Fin (n+m) → ℝ)) ∧
    η ∈ (F.V : Set (Fin (n+m) → ℝ)) ∧ ξ ≠ η from ⟨hξ, hη, hne⟩)]
  rw [C.regularTransferErrorKernel_congr_germs F i κ g ξ η hgo hgi]
  rw [C.regularTransferErrorKernel_listSum_add F i d.principal (fun t => t.kernel)
    d.regular (hVU hξ) (hVU hη) hF.Θ_eq hfo hfi hro hri]
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro t _
  exact (C.principalTransferErrorKernel_eq_generic F hF t i (hVU hξ) (hVU hη) hne).symm

end RothschildStein.P1.LiftedChart
