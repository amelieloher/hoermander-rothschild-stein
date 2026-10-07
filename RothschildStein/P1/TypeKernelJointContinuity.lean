-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.TypeKernelInputSmoothness
public import RothschildStein.P1.TypeKernelRepresentative

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set
namespace RothschildStein.P1.LiftedChart
variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {F : KernelFrame (n + m)}

/-- Joint continuity of the actual principal kernel on the interior
away from the diagonal. -/
theorem principalKernel_continuousOn_joint (hF : C.IsLiftedFrame F) (t : PrincipalTerm F) :
    ContinuousOn (Function.uncurry t.kernel)
      (((F.V : Set _) ×ˢ (F.V : Set _)) ∩ {p | p.1 ≠ p.2}) := by
  let E := ((F.V : Set _) ×ˢ (F.V : Set _)) ∩ {p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) | p.1 ≠ p.2}
  have hVU : (F.V : Set (Fin (n + m) → ℝ)) ⊆ C.U :=
    subset_closure.trans hF.closure_subset
  have hEU : E ⊆ C.U ×ˢ C.U := fun _ hp => ⟨hVU hp.1.1, hVU hp.1.2⟩
  have hθ : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => C.Θ p.2 p.1) E :=
    (C.theta_smooth.comp (contDiffOn_snd.prodMk contDiffOn_fst)
      (fun _ hp => ⟨hp.2, hp.1⟩)).mono hEU
  have hmap : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => (p.1, p.2, C.Θ p.2 p.1)) E :=
    contDiffOn_fst.prodMk (contDiffOn_snd.prodMk hθ)
  have h := (t.cutoffModelKernel_contDiffOn (hF.pole_smooth t.star)).comp hmap
    (fun p hp => (C.theta_eq_zero_iff (hVU hp.1.2) (hVU hp.1.1)).not.mpr hp.2)
  have he : (kernelUncurry t.cutoffModelKernel ∘
      (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => (p.1, p.2, C.Θ p.2 p.1))) =
      Function.uncurry t.kernel := by
    funext p
    change t.cutoffModelKernel p.1 p.2 (C.Θ p.2 p.1) = t.kernel p.1 p.2
    rw [t.kernel_eq_cutoffModelKernel, hF.Θ_eq]
  rw [he] at h
  exact h.continuousOn

/-- All actual type kernels are jointly continuous on interior
pairs away from the diagonal, using the budget-one decomposition. -/
theorem isTypeKernel_continuousOn_joint {lam : ℕ}
    (hF : C.IsLiftedFrame F)
    {κ : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ}
    (hκ : IsTypeKernel F lam κ) :
    ContinuousOn (Function.uncurry κ)
      (((F.V : Set _) ×ˢ (F.V : Set _)) ∩ {p | p.1 ≠ p.2}) := by
  obtain ⟨d⟩ := hκ 1
  have hp : ∀ l : List (PrincipalTerm F), ContinuousOn
      (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) =>
        (l.map (fun t => t.kernel p.1 p.2)).sum)
      (((F.V : Set _) ×ˢ (F.V : Set _)) ∩ {p | p.1 ≠ p.2}) := by
    intro l
    induction l with
    | nil => simp only [List.map_nil, List.sum_nil]; exact continuousOn_const
    | cons t l ih =>
      simp only [List.map_cons, List.sum_cons]
      exact (C.principalKernel_continuousOn_joint hF t).add ih
  apply ((hp d.principal).add d.regular_isRegular.1.continuous.continuousOn).congr
  intro p hp
  exact d.eq_off_diagonal p.1 p.2 hp.2

end RothschildStein.P1.LiftedChart
