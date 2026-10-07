-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PrincipalModelKernel
public import RothschildStein.P1.ContinuityPositive
public import RothschildStein.P1.KernelEstimatesChart

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

/-- Each actual principal input fiber is smooth
on the chart away from its diagonal pole. -/
theorem principalKernel_contDiffOn_input (hF : C.IsLiftedFrame F) (t : PrincipalTerm F)
    {ξ : Fin (n + m) → ℝ} (hξ : ξ ∈ C.U) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun η => t.kernel ξ η) (C.U \ {ξ}) := by
  have hθ : ContDiffOn ℝ (⊤ : ℕ∞) (fun η => C.Θ η ξ) (C.U \ {ξ}) :=
    C.theta_smooth.comp (contDiffOn_id.prodMk contDiffOn_const) (fun η hη => ⟨hη.1, hξ⟩)
  have hbody := (t.modelKernel_contDiffOn (hF.pole_smooth t.star)).comp
    ((contDiffOn_const (c := ξ)).prodMk (contDiffOn_id.prodMk hθ)) (fun η hη => by
      have hne : ξ ≠ η := (show η ≠ ξ from hη.2).symm
      exact fun hz => hne ((C.theta_eq_zero_iff hη.1 hξ).mp hz))
  have hout := ((contDiffOn_const (c := t.a ξ)).mul t.b.contDiff.contDiffOn).mul hbody
  simpa only [PrincipalTerm.kernel, PrincipalTerm.modelKernel, hF.Θ_eq,
    kernelUncurry, Function.comp_def, id_eq] using hout

/-- A type kernel has a C¹ input fiber off the
pole. Its arbitrary diagonal values have no regularity role. -/
theorem isTypeKernel_contDiffOn_input {lam : ℕ}
    (hF : C.IsLiftedFrame F) {κ : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ}
    (hκ : IsTypeKernel F lam κ) {ξ : Fin (n + m) → ℝ} (hξ : ξ ∈ C.U) :
    ContDiffOn ℝ 1 (fun η => κ ξ η) ((F.V : Set (Fin (n + m) → ℝ)) \ {ξ}) := by
  obtain ⟨d⟩ := hκ 1
  have hsub : ((F.V : Set (Fin (n + m) → ℝ)) \ {ξ}) ⊆ C.U \ {ξ} :=
    fun η hη => ⟨hF.closure_subset (subset_closure hη.1), hη.2⟩
  have hp : ∀ l : List (PrincipalTerm F),
      ContDiffOn ℝ 1 (fun η => (l.map (fun t => t.kernel ξ η)).sum)
        ((F.V : Set (Fin (n + m) → ℝ)) \ {ξ}) := by
    intro l
    induction l with
    | nil => simpa only [List.map_nil, List.sum_nil] using (contDiffOn_const (c := (0 : ℝ)))
    | cons t l ih =>
      simpa only [List.map_cons, List.sum_cons] using
        (((C.principalKernel_contDiffOn_input hF t hξ).of_le (by simp)).mono hsub).add ih
  have hr : ContDiffOn ℝ 1 (fun η => d.regular ξ η)
      ((F.V : Set (Fin (n + m) → ℝ)) \ {ξ}) :=
    (d.regular_isRegular.1.comp (contDiff_const.prodMk contDiff_id)).contDiffOn
  apply ((hp d.principal).add hr).congr
  intro η hη
  exact d.eq_off_diagonal ξ η (show ξ ≠ η from (show η ≠ ξ from hη.2).symm)

end RothschildStein.P1.LiftedChart
