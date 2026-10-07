-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PrincipalLeadingTerms
public import RothschildStein.P1.TypeClosure

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
namespace RothschildStein.P1

variable {N : ℕ} {F : KernelFrame N}

/-- An actual principal term satisfying the degree bound is a kernel
of the stated type at every regularity budget (BB Definition 11.7, p. 543). -/
theorem PrincipalTerm.isTypeKernel (t : PrincipalTerm F) (lam : ℕ)
    (hdegree : t.degree ≤ 2 - (lam : ℤ)) : IsTypeKernel F lam t.kernel := by
  intro m
  refine ⟨{
    principal := [t]
    principal_degree := ?_
    regular := fun _ _ => 0
    regular_isRegular := IsRegularKernel.zero
    eq_off_diagonal := ?_ }⟩
  · intro s hs
    simpa only [List.mem_singleton.mp hs] using hdegree
  · intro ξ η _
    simp

/-- Differentiating an operator coefficient in
a homogeneous field produces the exact lower type λ-w (BB Lemma 11.18, p. 549). -/
theorem PrincipalTerm.leadingCoefficientDerivative_isTypeKernel (t : PrincipalTerm F)
    (α : Fin N → ℕ) (hα : α ∈ t.indices) (j : Fin N)
    (Y : (Fin N → ℝ) → (Fin N → ℝ)) (hY : ContDiff ℝ (⊤ : ℕ∞) Y)
    (w lam : ℕ) (hhY : G2.IsHomogeneousField F.G Y (w : ℤ))
    (hw : w ≤ lam) (hd : t.degree ≤ 2 - (lam : ℤ)) :
    IsTypeKernel F (lam - w)
      (t.leadingCoefficientDerivative α hα j Y hY (w : ℤ) hhY).kernel := by
  apply PrincipalTerm.isTypeKernel
  change t.degree + (w : ℤ) ≤ 2 - ((lam - w : ℕ) : ℤ)
  omega

/-- The successor-partial contribution also has
exact type λ-w, including the drift weight w=2 (BB Lemma 11.18, p. 549). -/
theorem PrincipalTerm.leadingPoleDerivative_isTypeKernel (t : PrincipalTerm F)
    (α : Fin N → ℕ) (hα : α ∈ t.indices) (j : Fin N)
    (Y : (Fin N → ℝ) → (Fin N → ℝ)) (hY : ContDiff ℝ (⊤ : ℕ∞) Y)
    (w lam : ℕ) (hhY : G2.IsHomogeneousField F.G Y (w : ℤ))
    (hw : w ≤ lam) (hd : t.degree ≤ 2 - (lam : ℤ)) :
    IsTypeKernel F (lam - w)
      (t.leadingPoleDerivative α hα j Y hY (w : ℤ) hhY).kernel := by
  apply PrincipalTerm.isTypeKernel
  change t.degree + (w : ℤ) ≤ 2 - ((lam - w : ℕ) : ℤ)
  omega

end RothschildStein.P1
