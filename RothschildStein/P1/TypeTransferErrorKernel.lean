-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.TransferFiniteDecomposition
public import RothschildStein.P1.TypeKernelSupport
public import RothschildStein.P1.KernelListSums

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter Classical
open scoped Topology
namespace RothschildStein.P1.LiftedChart
variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  (C : LiftedChart w s Ω hΩ X x₀ m) (F : KernelFrame (n+m))

/-- The canonical error kernel is the actual
transfer derivative expression on the off-diagonal cutoff patch and
zero elsewhere. It is independent of every regularity decomposition
(BB Theorem 11.24, pp. 555–558). -/
def cutoffTransferErrorKernel (i : Fin k)
    (κ : (Fin (n+m) → ℝ) → (Fin (n+m) → ℝ) → ℝ) (ξ η : Fin (n+m) → ℝ) : ℝ :=
  if ξ ∈ (F.V : Set (Fin (n+m) → ℝ)) ∧ η ∈ (F.V : Set (Fin (n+m) → ℝ)) ∧ ξ ≠ η
    then C.regularTransferErrorKernel F i κ ξ η else 0

/-- The full canonical transfer error has type
λ+1-w_i at every regularity budget, on the actual lifted frame. All
principal and regular contributions are constructed and identified
with the same actual kernel (BB Theorem 11.24, pp. 555–558). -/
theorem isTypeKernel_cutoffTransferErrorKernel (hF : C.IsLiftedFrame F)
    {lam : ℕ} {κ : (Fin (n+m) → ℝ) → (Fin (n+m) → ℝ) → ℝ}
    (hκ : IsTypeKernel F lam κ) (i : Fin k) (hw : (w i : ℕ) ≤ lam) :
    IsTypeKernel F (lam+1-(w i : ℕ)) (C.cutoffTransferErrorKernel F i κ) := by
  intro budget
  obtain ⟨d⟩ := hκ (budget+1)
  let q := fun t : {t // t ∈ d.principal} => C.principalTransferErrorKernel F hF t.val i
  let Q := fun ξ η => (d.principal.attach.map (fun t => q t ξ η)).sum
  have hQ : IsTypeKernel F (lam+1-(w i : ℕ)) Q :=
    IsTypeKernel.listSum d.principal.attach q (fun t _ =>
      C.isTypeKernel_principalTransferErrorKernel F hF t.val i lam hw (d.principal_degree t.val t.property))
  let R := C.regularTransferErrorKernel F i d.regular
  have hR : IsRegularKernel F budget R :=
    C.isRegularKernel_regularTransferErrorKernel F hF d.regular_isRegular i
  obtain ⟨dQ⟩ := hQ budget
  let dR : TypeDecomposition F (lam+1-(w i : ℕ)) budget R := {
    principal := []
    principal_degree := by simp
    regular := R
    regular_isRegular := hR
    eq_off_diagonal := by simp }
  let dout := dQ.add dR
  refine ⟨{ dout with eq_off_diagonal := ?_ }⟩
  intro ξ η hne
  have he : C.cutoffTransferErrorKernel F i κ ξ η = Q ξ η + R ξ η := by
    by_cases hp : ξ ∈ (F.V : Set (Fin (n+m) → ℝ)) ∧ η ∈ (F.V : Set (Fin (n+m) → ℝ))
    · have hVU : (F.V : Set (Fin (n+m) → ℝ)) ⊆ C.U := subset_closure.trans hF.closure_subset
      have hξ := hVU hp.1
      have hη := hVU hp.2
      let g := fun x y => (d.principal.attach.map (fun t => t.val.kernel x y)).sum + d.regular x y
      have hgo : (fun x => κ x η) =ᶠ[𝓝 ξ] fun x => g x η := by
        filter_upwards [isOpen_compl_singleton.mem_nhds (by simpa using hne)] with x hx
        dsimp only [g]
        rw [List.attach_map_val (f := fun t : PrincipalTerm F => t.kernel x η)]
        exact d.eq_off_diagonal x η (by simpa using hx)
      have hgi : κ ξ =ᶠ[𝓝 η] g ξ := by
        filter_upwards [isOpen_compl_singleton.mem_nhds (by simpa using hne.symm)] with y hy
        dsimp only [g]
        rw [List.attach_map_val (f := fun t : PrincipalTerm F => t.kernel ξ y)]
        exact d.eq_off_diagonal ξ y (Ne.symm (by simpa using hy))
      have hfo (t : {t // t ∈ d.principal}) (_ : t ∈ d.principal.attach) :
          DifferentiableAt ℝ (fun x => t.val.kernel x η) ξ :=
        C.principalKernel_differentiableAt hF t.val hξ hη hne
      have hfi (t : {t // t ∈ d.principal}) (_ : t ∈ d.principal.attach) :
          DifferentiableAt ℝ (t.val.kernel ξ) η :=
        C.transferPrincipal_input_differentiableAt F hF t.val hξ hη hne
      have hro : DifferentiableAt ℝ (fun x => d.regular x η) ξ :=
        (d.regular_isRegular.1.comp (contDiff_id.prodMk contDiff_const)).differentiable (by simp) ξ
      have hri : DifferentiableAt ℝ (d.regular ξ) η :=
        (d.regular_isRegular.1.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp) η
      have hpfull : ξ ∈ (F.V : Set (Fin (n+m) → ℝ)) ∧
          η ∈ (F.V : Set (Fin (n+m) → ℝ)) ∧ ξ ≠ η := ⟨hp.1, hp.2, hne⟩
      simp only [cutoffTransferErrorKernel, ite_eq_left hpfull]
      rw [C.regularTransferErrorKernel_congr_germs F i κ g ξ η hgo hgi]
      rw [C.regularTransferErrorKernel_listSum_add F i d.principal.attach
        (fun t x y => t.val.kernel x y) d.regular hξ hη hF.Θ_eq hfo hfi hro hri]
      dsimp only [Q, q, R]
      congr 1
      apply congrArg List.sum
      apply List.map_congr_left
      intro t _
      exact (C.principalTransferErrorKernel_eq F hF t.val i hξ hη hne).symm
    · have hout : ξ ∉ (F.V : Set (Fin (n+m) → ℝ)) ∨ η ∉ (F.V : Set (Fin (n+m) → ℝ)) :=
        not_and_or.mp hp
      have hzero : Q ξ η = 0 := hQ.eq_zero_of_outside hne hout
      have hrzero : R ξ η = 0 := image_eq_zero_of_notMem_tsupport
        (f := fun z : (Fin (n+m) → ℝ) × (Fin (n+m) → ℝ) => R z.1 z.2) (x := (ξ, η)) (fun ht => by
          have hz := hR.2.2 ht
          rcases hout with hx | hy
          · exact hx hz.1
          · exact hy hz.2)
      have hnot : ¬(ξ ∈ (F.V : Set (Fin (n+m) → ℝ)) ∧
          η ∈ (F.V : Set (Fin (n+m) → ℝ)) ∧ ξ ≠ η) := fun h => hp ⟨h.1, h.2.1⟩
      simp only [cutoffTransferErrorKernel, ite_eq_right hnot, hzero, hrzero, zero_add]
  rw [he, ← dout.eq_off_diagonal ξ η hne]

end RothschildStein.P1.LiftedChart
