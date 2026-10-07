-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.TypeKernelOutputDerivative
public import RothschildStein.P1.TypeKernelInputMultiplier
public import RothschildStein.P1.StandardFrame
public import RothschildStein.P1.ChartTranspose
public import RothschildStein.P1.AdjointExpansion

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set
namespace RothschildStein.P1
variable {n k m q : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {F : KernelFrame (n + m)}
  {H : H1.StandingHypotheses C.G q} {K : H1.FundamentalKernel C.G H}
  {hQ : 2 < (C.G.homogeneousDimension : ℝ)}

/-- A standard frame supplies the actual adjoint-pole reflection
used by the kernel transpose theorem. -/
theorem LiftedChart.IsStandardFrame.pole_reflection (hF : C.IsStandardFrame F H K hQ)
    (u : Fin (n + m) → ℝ) : F.Γs u = F.Γ (-u) := by
  rw [hF.Γs_eq, hF.Γ_eq]
  exact K.reflection_neg hQ C.inv_eq_neg u

/-- The input formal-adjoint kernel includes minus the input
field derivative and the input divergence coefficient. -/
def cutoffInputTranspose (F : KernelFrame (n + m))
    (Y : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ))
    (r : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ)
    (ξ η : Fin (n + m) → ℝ) : ℝ :=
  -cutoffOutputDerivative F Y (fun x y => r y x) η ξ -
    r ξ η * Hormander.Interface.euclideanDivergence Y η

/-- For a standard frame, the actual input
formal-adjoint kernel is of type λ-wᵢ at every regularity budget.
The divergence term has type λ before lowering the type. -/
theorem LiftedChart.isTypeKernel_cutoffInputTranspose
    (hF : C.IsStandardFrame F H K hQ) {lam : ℕ}
    {r : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ}
    (hr : IsTypeKernel F lam r) (i : Fin k) (hw : (w i : ℕ) ≤ lam) :
    IsTypeKernel F (lam - (w i : ℕ)) (cutoffInputTranspose F (C.Xl i) r) := by
  have hVU : (F.V : Set (Fin (n + m) → ℝ)) ⊆ C.U :=
    subset_closure.trans hF.lifted.closure_subset
  have htrans {d : ℕ} {f : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ}
      (hf : IsTypeKernel F d f) : IsTypeKernel F d (fun ξ η => f η ξ) :=
    C.isTypeKernel_transpose F hF.lifted.Θ_eq hVU
      (fun u _ => hF.pole_reflection u) hF.lifted.Γ_smooth hF.lifted.Γs_smooth d f hf
  have hd := C.isTypeKernel_cutoffOutputDerivative hF.lifted (htrans hr) i hw
  have hdt := htrans hd
  have hX : ContDiffOn ℝ (⊤ : ℕ∞) (C.Xl i) (F.V : Set (Fin (n + m) → ℝ)) :=
    (C.lift_smooth i).mono (hVU.trans C.U_subset_O)
  have hm := hr.inputMultiplier (Hormander.Interface.euclideanDivergence (C.Xl i))
    (contDiffOn_euclideanDivergence F.V (C.Xl i) hX)
  have hout := hdt.neg.add ((hm.mono (by omega)).neg)
  change IsTypeKernel F (lam - (w i : ℕ)) (fun ξ η =>
    -cutoffOutputDerivative F (C.Xl i) (fun x y => r y x) η ξ -
      r ξ η * Hormander.Interface.euclideanDivergence (C.Xl i) η)
  simpa only [sub_eq_add_neg] using hout

/-- On the interior off the diagonal, the formal-adjoint
kernel has precisely the source derivative and divergence expression. -/
theorem cutoffInputTranspose_apply
    (Y : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ))
    (r : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ)
    {ξ η : Fin (n + m) → ℝ}
    (hξ : ξ ∈ (F.V : Set (Fin (n + m) → ℝ)))
    (hη : η ∈ (F.V : Set (Fin (n + m) → ℝ))) (hne : ξ ≠ η) :
    cutoffInputTranspose F Y r ξ η =
      -fieldDerivative Y (fun y => r ξ y) η -
        r ξ η * Hormander.Interface.euclideanDivergence Y η := by
  have hp : η ∈ (F.V : Set (Fin (n + m) → ℝ)) ∧
      ξ ∈ (F.V : Set (Fin (n + m) → ℝ)) ∧ η ≠ ξ := ⟨hη, hξ, hne.symm⟩
  simp only [cutoffInputTranspose, cutoffOutputDerivative, ite_eq_left hp]

end RothschildStein.P1
