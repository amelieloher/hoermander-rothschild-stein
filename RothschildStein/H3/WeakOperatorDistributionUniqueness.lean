-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.WeakOperatorDistributionEquation

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory TopologicalSpace
open scoped ENNReal

/-- the inherited actual distributional equation identifies
the certified Sobolev operator with the forcing almost everywhere. -/
theorem WeakDriftOperatorData.operator_ae_eq_of_distribution_equation {n q : ℕ}
    {X : Fin (q+1) → (Fin n → ℝ) → (Fin n → ℝ)}
    {Ω : Opens (Fin n → ℝ)} {p : ℝ≥0∞} {u : (Fin n → ℝ) → ℝ}
    (D : WeakDriftOperatorData X Ω p u) (hp : 1 ≤ p)
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (F : (Fin n → ℝ) → ℝ)
    (hF : LocallyIntegrableOn F (Ω : Set (Fin n → ℝ)) volume)
    (heq : ∀ ψ : TestFunction Ω ℝ (⊤ : ℕ∞),
      Distribution.ofFun Ω u volume (⊤ : ℕ∞)
        (Distribution.adjointTest Ω X (fun _ => 0) hX (by fun_prop) ψ) =
      Distribution.ofFun Ω F volume (⊤ : ℕ∞) ψ) :
    D.operator =ᵐ[volume.restrict (Ω : Set (Fin n → ℝ))] F := by
  have hD := locallyIntegrableOn_of_locallyIntegrable_restrict (D.operator_memLp.locallyIntegrable hp)
  apply Distribution.ofFun_injective hD hF
  ext ψ
  exact (D.ofFun_adjoint_equation hp hX D.operator ae_eq_rfl ψ).symm.trans (heq ψ)

end RothschildStein.H3
