-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PrincipalKernelMeasurable

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory

namespace RothschildStein.P1

/-- A measurable candidate obtained from the principal terms
with zero diagonal and the genuine regular remainder of one decomposition. -/
def TypeDecomposition.measurableKernel {N : ℕ} {F : KernelFrame N} {lam budget : ℕ}
    {kern : (Fin N → ℝ) → (Fin N → ℝ) → ℝ} (D : TypeDecomposition F lam budget kern)
    (ξ η : Fin N → ℝ) : ℝ :=
  (D.principal.map (fun t => zeroDiagonal t.kernel ξ η)).sum + D.regular ξ η

/-- The representative agrees with the original type kernel
at every pair of distinct endpoints. -/
theorem TypeDecomposition.measurableKernel_eq_off_diagonal
    {N : ℕ} {F : KernelFrame N} {lam budget : ℕ}
    {kern : (Fin N → ℝ) → (Fin N → ℝ) → ℝ} (D : TypeDecomposition F lam budget kern)
    (ξ η : Fin N → ℝ) (hne : ξ ≠ η) : D.measurableKernel ξ η = kern ξ η := by
  classical
  simp only [measurableKernel, zeroDiagonal, ite_eq_right hne]
  exact (D.eq_off_diagonal ξ η hne).symm

variable {n k m : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}

/-- The representative from a finite type decomposition is
jointly measurable on the ambient coordinate carrier. -/
theorem LiftedChart.measurable_typeDecomposition_kernel
    (C : LiftedChart w s Ω hΩ X x₀ m) (F : KernelFrame (n + m))
    (hΘ : F.Θ = C.Θ) (hVU : (F.V : Set (Fin (n + m) → ℝ)) ⊆ C.U)
    (hΓ : ∀ star : Bool, ContDiffOn ℝ (⊤ : ℕ∞) (F.pole star) {(0 : Fin (n + m) → ℝ)}ᶜ)
    {lam budget : ℕ} {kern : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ}
    (D : TypeDecomposition F lam budget kern) :
    Measurable (Function.uncurry D.measurableKernel) := by
  have hm : ∀ l : List (PrincipalTerm F), Measurable
      (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) =>
        (l.map (fun t => zeroDiagonal t.kernel p.1 p.2)).sum) := by
    intro l
    induction l with
    | nil => simpa only [List.map_nil, List.sum_nil] using (measurable_const (a := (0 : ℝ)))
    | cons t l ih =>
      simp only [List.map_cons, List.sum_cons]
      exact (C.measurable_principal_zeroDiagonal F hΘ hVU t (hΓ t.star)).add ih
  exact (hm D.principal).add D.regular_isRegular.1.continuous.measurable

/-- Every actual type kernel has a jointly measurable
representative agreeing almost everywhere on every row and every column.
No measurability is demanded of its arbitrary diagonal values. -/
theorem LiftedChart.exists_typeKernel_measurableRepresentative
    (C : LiftedChart w s Ω hΩ X x₀ m) (F : KernelFrame (n + m))
    (hΘ : F.Θ = C.Θ) (hVU : (F.V : Set (Fin (n + m) → ℝ)) ⊆ C.U)
    (hΓ : ∀ star : Bool, ContDiffOn ℝ (⊤ : ℕ∞) (F.pole star) {(0 : Fin (n + m) → ℝ)}ᶜ)
    {lam : ℕ} {kern : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ}
    (hk : IsTypeKernel F lam kern) :
    ∃ r : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ,
      Measurable (Function.uncurry r) ∧ ∀ ξ,
        (r ξ =ᵐ[volume] kern ξ) ∧ ((fun η => r η ξ) =ᵐ[volume] fun η => kern η ξ) := by
  let rsRepresentativeFinNonempty : Nonempty (Fin (n + m)) := ⟨⟨0, C.G.dimension_pos⟩⟩
  obtain ⟨D⟩ := hk 0
  refine ⟨D.measurableKernel, C.measurable_typeDecomposition_kernel F hΘ hVU hΓ D, ?_⟩
  intro ξ
  constructor
  · filter_upwards [volume.ae_ne ξ] with η hη
    exact D.measurableKernel_eq_off_diagonal ξ η hη.symm
  · filter_upwards [volume.ae_ne ξ] with η hη
    exact D.measurableKernel_eq_off_diagonal η ξ hη

end RothschildStein.P1
