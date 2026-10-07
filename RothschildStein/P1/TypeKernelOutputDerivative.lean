-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PrincipalFourTermTypes
public import RothschildStein.P1.KernelFiberDifferentiability
public import RothschildStein.P1.TypeKernelSupport
public import RothschildStein.P1.KernelListSums
public import RothschildStein.P1.RegularKernelFiberDerivative

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter Classical
open scoped Topology
namespace RothschildStein.P1
variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {F : KernelFrame (n + m)}

/-- Differentiate the actual output fiber on the cutoff region,
normalizing all other values to zero. Diagonal values are immaterial. -/
def cutoffOutputDerivative (F : KernelFrame (n + m))
    (Y : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ))
    (r : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ)
    (ξ η : Fin (n + m) → ℝ) : ℝ :=
  if ξ ∈ (F.V : Set (Fin (n + m) → ℝ)) ∧ η ∈ (F.V : Set (Fin (n + m) → ℝ)) ∧ ξ ≠ η
  then fieldDerivative Y (fun x => r x η) ξ else 0

/-- The actual differentiated kernel has type λ-wᵢ at every
regularity budget. The principal four-term decomposition and the regular
remainder derivative are assembled without a weak-operator premise. -/
theorem LiftedChart.isTypeKernel_cutoffOutputDerivative
    (hF : C.IsLiftedFrame F) {lam : ℕ}
    {r : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ}
    (hr : IsTypeKernel F lam r) (i : Fin k) (hw : (w i : ℕ) ≤ lam) :
    IsTypeKernel F (lam - (w i : ℕ)) (cutoffOutputDerivative F (C.Xl i) r) := by
  classical
  have hVU : (F.V : Set (Fin (n + m) → ℝ)) ⊆ C.U :=
    subset_closure.trans hF.closure_subset
  have hX : ContDiffOn ℝ (⊤ : ℕ∞) (C.Xl i) (F.V : Set (Fin (n + m) → ℝ)) :=
    (C.lift_smooth i).mono (hVU.trans C.U_subset_O)
  intro budget
  obtain ⟨d⟩ := hr (budget + 1)
  have hex (t : {t // t ∈ d.principal}) :
      ∃ q : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ,
        IsTypeKernel F (lam - (w i : ℕ)) q ∧
        ∀ ξ ∈ C.U, ∀ η ∈ C.U, ξ ≠ η →
          fieldDerivative (C.Xl i) (fun x => t.val.kernel x η) ξ = q ξ η := by
    obtain ⟨a, b, c, e, ha, hb, hc, he, hid⟩ :=
      C.exists_principal_fourTerm_types F hF.Θ_eq hF.G_eq hVU t.val i lam hw
        (d.principal_degree t.val t.property) (hF.pole_smooth t.val.star)
        (by simpa only [hF.G_eq] using hF.pole_homogeneous t.val.star)
    exact ⟨fun ξ η => c ξ η + e ξ η + a ξ η + b ξ η,
      (((hc.mono (by omega)).add (he.mono (by omega))).add ha).add (hb.mono (by omega)), hid⟩
  choose q hq he using hex
  let Q := fun ξ η => (d.principal.attach.map (fun t => q t ξ η)).sum
  have hQ : IsTypeKernel F (lam - (w i : ℕ)) Q :=
    IsTypeKernel.listSum d.principal.attach q (fun t _ => hq t)
  let R := fun ξ η => fieldDerivative (C.Xl i) (fun x => d.regular x η) ξ
  have hR : IsRegularKernel F budget R := d.regular_isRegular.fieldDerivative_output (C.Xl i) hX
  obtain ⟨dQ⟩ := hQ budget
  let dR : TypeDecomposition F (lam - (w i : ℕ)) budget R := {
    principal := []
    principal_degree := by simp
    regular := R
    regular_isRegular := hR
    eq_off_diagonal := by simp }
  let dout := dQ.add dR
  refine ⟨{ dout with eq_off_diagonal := ?_ }⟩
  intro ξ η hne
  have hEq : cutoffOutputDerivative F (C.Xl i) r ξ η = Q ξ η + R ξ η := by
    by_cases hp : ξ ∈ (F.V : Set (Fin (n + m) → ℝ)) ∧ η ∈ (F.V : Set (Fin (n + m) → ℝ))
    · have hξ := hVU hp.1
      have hη := hVU hp.2
      have hg : (fun x => r x η) =ᶠ[𝓝 ξ]
          (fun x => (d.principal.attach.map (fun t => t.val.kernel x η)).sum + d.regular x η) := by
        filter_upwards [isOpen_compl_singleton.mem_nhds (by simpa using hne)] with x hx
        rw [List.attach_map_val (f := fun t : PrincipalTerm F => t.kernel x η)]
        exact d.eq_off_diagonal x η (by simpa using hx)
      have hP (t : {t // t ∈ d.principal}) :
          DifferentiableAt ℝ (fun x => t.val.kernel x η) ξ :=
        C.principalKernel_differentiableAt hF t.val hξ hη hne
      have hdP : DifferentiableAt ℝ
          (fun x => (d.principal.attach.map (fun t => t.val.kernel x η)).sum) ξ :=
        (differentiableAt_and_fieldDerivative_listSum d.principal.attach
          (fun t x => t.val.kernel x η) (C.Xl i) ξ (fun t _ => hP t)).1
      have hdR : DifferentiableAt ℝ (fun x => d.regular x η) ξ :=
        (d.regular_isRegular.1.comp (contDiff_id.prodMk contDiff_const)).differentiable
          (by simp) ξ
      have hp' : ξ ∈ (F.V : Set (Fin (n + m) → ℝ)) ∧
          η ∈ (F.V : Set (Fin (n + m) → ℝ)) ∧ ξ ≠ η := ⟨hp.1, hp.2, hne⟩
      simp only [cutoffOutputDerivative, ite_eq_left hp', Q, R, fieldDerivative]
      rw [hg.fderiv_eq, fderiv_fun_add hdP hdR, add_apply]
      congr 1
      have hs := fieldDerivative_listSum d.principal.attach
        (fun t x => t.val.kernel x η) (C.Xl i) ξ (fun t _ => hP t)
      simp only [fieldDerivative] at hs
      rw [hs]
      apply congrArg List.sum
      apply List.map_congr_left
      intro t _
      exact he t ξ hξ η hη hne
    · have ho : ξ ∉ (F.V : Set (Fin (n + m) → ℝ)) ∨ η ∉ (F.V : Set (Fin (n + m) → ℝ)) :=
        not_and_or.mp hp
      have hQ0 := hQ.eq_zero_of_outside hne ho
      have hR0 : R ξ η = 0 := image_eq_zero_of_notMem_tsupport
        (f := fun z : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => R z.1 z.2)
        (x := (ξ, η))
        (fun ht => by
          have h := hR.2.2 ht
          rcases ho with hξ | hη
          · exact hξ h.1
          · exact hη h.2)
      have hp' : ¬(ξ ∈ (F.V : Set (Fin (n + m) → ℝ)) ∧
          η ∈ (F.V : Set (Fin (n + m) → ℝ)) ∧ ξ ≠ η) := fun h => hp ⟨h.1, h.2.1⟩
      simp only [cutoffOutputDerivative, ite_eq_right hp', hQ0, hR0, add_zero]
  rw [hEq]
  exact dout.eq_off_diagonal ξ η hne

end RothschildStein.P1
