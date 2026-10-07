-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.ParametrixStatements
public import RothschildStein.P1.TypeClosure

/-!
# The parametrices are single principal terms of type 2

The kernels of the parametrices `P₁` and `P₂` are `a(ξ) b'(η) Γ*(Θ(η, ξ))` and `a'(ξ) b(η) Γ(Θ(η, ξ))` with
smooth compactly supported cutoffs: a single principal term with `D = id` homogeneous of
degree `0 ≤ 2 - λ` for every `λ ≤ 2`, and zero regular remainder. Such a kernel is therefore of type
`λ ≤ 2` modeled on its pole, with no condition on the frame (BB p. 543, Def 11.7; BB Thm 11.25:
they have type 2).

* `idOperator` is the identity differential operator;
* `PrincipalTerm.ofCutoffs` the principal term `α(ξ) β(η) Γ_pole(Θ(η, ξ))`;
* `isTypeKernelOn_of_eq_principal`: a kernel equal to `α(ξ) β(η) Γ_pole(Θ(η, ξ))` is of every type
  `λ ≤ 2` modeled on the pole;
* `divTest`: the test function `b / c` for `b ∈ C_c^∞(V)` and `c` smooth and positive on `V`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
namespace RothschildStein.P1

variable {N : ℕ}

/-- The identity differential operator `D = id` (one multi-index, `0`, coefficient `1`). -/
def idOperator (N : ℕ) : SmoothDifferentialOperator N where
  indices := {0}
  coefficient := fun _ _ => 1
  smooth_coefficient := fun _ _ => contDiff_const

/-- The identity operator acts as the identity. -/
theorem idOperator_apply (f : (Fin N → ℝ) → ℝ) (x : Fin N → ℝ) :
    (idOperator N).apply f x = f x := by
  have h : ∀ l : List (Fin N), l.flatMap (fun _ => ([] : List (Fin N))) = [] := by
    intro l
    induction l with
    | nil => rfl
    | cons a l ih => simp [List.flatMap_cons, ih]
  simp [idOperator, SmoothDifferentialOperator.apply, euclideanPartial, h]

/-- The identity operator is homogeneous of degree `0` for every group. -/
theorem idOperator_isHomogeneous (G : HomogeneousGroup N) :
    (idOperator N).IsHomogeneous G ((0 : ℤ) : ℝ) := by
  intro f _ t _ x
  simp [idOperator_apply]

/-- The principal term `α(ξ) β(η) (id Γ_pole)(Θ(η, ξ))` with cutoffs `α, β ∈ C_c^∞(V)`:
`D = id`, degree `0` (BB p. 543, Def 11.7). -/
def PrincipalTerm.ofCutoffs (F : KernelFrame N) (α β : TestFunction F.V ℝ (⊤ : ℕ∞))
    (star : Bool) : PrincipalTerm F where
  a := α
  b := β
  D := fun _ _ => idOperator N
  indices := {0}
  indices_eq := fun _ _ => rfl
  coefficient_smooth := fun _ _ => contDiff_const
  degree := 0
  homogeneous := fun _ _ => idOperator_isHomogeneous F.G
  star := star

/-- The kernel of `PrincipalTerm.ofCutoffs`. -/
theorem PrincipalTerm.ofCutoffs_kernel (F : KernelFrame N) (α β : TestFunction F.V ℝ (⊤ : ℕ∞))
    (star : Bool) (ξ η : Fin N → ℝ) :
    (PrincipalTerm.ofCutoffs F α β star).kernel ξ η = α ξ * β η * F.pole star (F.Θ η ξ) := by
  simp [PrincipalTerm.kernel, PrincipalTerm.ofCutoffs, idOperator_apply]

/-- A kernel of the form `α(ξ) β(η) Γ_pole(Θ(η, ξ))` with `α, β ∈ C_c^∞(V)` has every type
`lam ≤ 2` and is modeled on its pole: a single principal term with `D = id` of degree `0 ≤ 2 - lam`
and zero regular remainder. -/
theorem isTypeKernelOn_of_eq_principal (F : KernelFrame N) {lam : ℕ} (hlam : lam ≤ 2)
    (α β : TestFunction F.V ℝ (⊤ : ℕ∞)) (star : Bool) (k : (Fin N → ℝ) → (Fin N → ℝ) → ℝ)
    (hk : ∀ ξ η, k ξ η = α ξ * β η * F.pole star (F.Θ η ξ)) : IsTypeKernelOn F star lam k := by
  intro m
  refine ⟨{ principal := [PrincipalTerm.ofCutoffs F α β star]
            principal_degree := ?_
            regular := fun _ _ => 0
            regular_isRegular := IsRegularKernel.zero
            eq_off_diagonal := ?_ }, ?_⟩
  · intro t ht
    obtain rfl := List.mem_singleton.1 ht
    change (0 : ℤ) ≤ 2 - (lam : ℤ)
    omega
  · intro ξ η _
    simp [hk, PrincipalTerm.ofCutoffs_kernel]
  · intro t ht
    obtain rfl := List.mem_singleton.1 ht
    rfl

/-- The test function `b / c`: for `b ∈ C_c^∞(V)` and `c` smooth and positive on `V`
(the density of a lifted chart), `ξ ↦ b(ξ) / c(ξ)` lies in `C_c^∞(V)`. -/
def divTest (F : KernelFrame N) (c : (Fin N → ℝ) → ℝ)
    (hc : ContDiffOn ℝ (⊤ : ℕ∞) c (F.V : Set (Fin N → ℝ)))
    (hc0 : ∀ ξ ∈ (F.V : Set (Fin N → ℝ)), 0 < c ξ) (b : TestFunction F.V ℝ (⊤ : ℕ∞)) :
    TestFunction F.V ℝ (⊤ : ℕ∞) :=
  testMultiplierOn F.V (fun x => (c x)⁻¹) (hc.inv fun x hx => (hc0 x hx).ne') b

/-- The values of `divTest`. -/
theorem divTest_apply (F : KernelFrame N) (c : (Fin N → ℝ) → ℝ)
    (hc : ContDiffOn ℝ (⊤ : ℕ∞) c (F.V : Set (Fin N → ℝ)))
    (hc0 : ∀ ξ ∈ (F.V : Set (Fin N → ℝ)), 0 < c ξ) (b : TestFunction F.V ℝ (⊤ : ℕ∞))
    (ξ : Fin N → ℝ) : divTest F c hc hc0 b ξ = b ξ / c ξ := by
  change b ξ * (c ξ)⁻¹ = b ξ / c ξ
  rw [div_eq_mul_inv]

end RothschildStein.P1
