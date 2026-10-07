-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.GainWord
public import RothschildStein.P1.GeneratorTransferKernels
public import RothschildStein.P1.LeftParametrixAlgebra

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped BigOperators
namespace RothschildStein.P1

/-- Finite sums of locally integrable rows are
locally integrable on the actual open frame domain. -/
theorem locallyIntegrableOn_finiteRows {N A : ℕ} (V : Opens (Fin N → ℝ))
    (f : Fin A → (Fin N → ℝ) → ℝ)
    (hi : ∀ j, LocallyIntegrableOn (f j) (V : Set (Fin N → ℝ)) volume) :
    LocallyIntegrableOn (fun ξ => ∑ j, f j ξ) (V : Set (Fin N → ℝ)) volume := by
  apply (locallyIntegrableOn_iff V.isOpen.isLocallyClosed).mpr
  intro K hKV hK
  exact integrable_finsetSum Finset.univ
    (fun j _ => (hi j).integrableOn_compact_subset hKV hK)

namespace LiftedChart
variable {n k m q : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {F : KernelFrame (n+m)}
  {H : H1.StandingHypotheses C.G q} {K : H1.FundamentalKernel C.G H}
  {hQ : 2 < (C.G.homogeneousDimension : ℝ)}

/-- Every positive typed kernel row acting on
an interior test is locally integrable, by the proved continuity theorem. -/
theorem positiveKernelRow_locallyIntegrableOn_standard
    (hF : C.IsStandardFrame F H K hQ) {lam : ℕ} (hlam : 1 ≤ lam)
    {κ : (Fin (n+m) → ℝ) → (Fin (n+m) → ℝ) → ℝ} (hκ : IsTypeKernel F lam κ)
    (φ : TestFunction F.V ℝ (⊤ : ℕ∞)) :
    LocallyIntegrableOn (fun ξ => ∫ η, κ ξ η * φ η) (F.V : Set (Fin (n+m) → ℝ)) volume := by
  let T : TypeOperator F lam := {
    kernel := κ
    isType := hκ
    mult := 0
    mult_eq_zero := by intro _; rfl }
  have hi := T.locallyIntegrableOn_apply_test hF φ
  rw [T.apply_eq_integral (by omega)] at hi
  exact hi

end LiftedChart
end RothschildStein.P1
