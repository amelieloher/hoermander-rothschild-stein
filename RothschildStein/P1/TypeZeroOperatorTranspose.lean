-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.TypeZeroTestedSharpLimit
public import RothschildStein.P1.ActualSharpTransposeIdentity
public import RothschildStein.P1.PositiveTypeOperatorTranspose

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace RothschildStein.P1.LiftedChart
variable {n k m q : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {F : KernelFrame (n + m)}
  {H : H1.StandingHypotheses C.G q} {K : H1.FundamentalKernel C.G H}
  {hQ : 2 < (C.G.homogeneousDimension : ℝ)}

/-- Actual type-zero operators have the
same-type bilinear transpose, keeping the identical multiplier and the
prescribed symmetric gauge truncation. -/
theorem exists_typeZero_transpose_standard (hF : C.IsStandardFrame F H K hQ)
    (T : TypeOperator F 0) :
    ∃ U : TypeOperator F 0,
      U.kernel = (fun ξ η => T.kernel η ξ) ∧ U.mult = T.mult ∧
      ∀ f g : TestFunction F.V ℝ (⊤ : ℕ∞),
        (∫ ξ, g ξ * T.apply f ξ) = ∫ η, f η * U.apply g η := by
  have hVU : (F.V : Set (Fin (n + m) → ℝ)) ⊆ C.U :=
    subset_closure.trans hF.lifted.closure_subset
  let U : TypeOperator F 0 := {
    kernel := fun ξ η => T.kernel η ξ
    isType := C.isTypeKernel_transpose F hF.lifted.Θ_eq hVU (fun u _ => hF.pole_reflection u)
      (hF.lifted.pole_smooth false) (hF.lifted.pole_smooth true) 0 T.kernel T.isType
    mult := T.mult
    mult_eq_zero := T.mult_eq_zero }
  refine ⟨U, rfl, rfl, ?_⟩
  intro f g
  have hl := C.tendsto_typeZero_tested_sharpIntegral hF T f g
  have hr := C.tendsto_typeZero_tested_sharpIntegral hF U g f
  have he : (∫ ξ, g ξ * (T.apply f ξ - T.mult ξ * f ξ)) =
      ∫ η, f η * (U.apply g η - T.mult η * g η) := by
    apply tendsto_nhds_unique hl
    refine hr.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact (C.sharp_tested_bilinearTranspose hF T.isType f g hε).symm
  have hiT : Integrable (fun ξ => g ξ * T.apply f ξ) := by
    simpa only [mul_comm] using S.integrable_mul_test F.V (T.locallyIntegrableOn_apply_test hF f) g
  have hiU : Integrable (fun ξ => f ξ * U.apply g ξ) := by
    simpa only [mul_comm] using S.integrable_mul_test F.V (U.locallyIntegrableOn_apply_test hF g) f
  have hiM : Integrable (fun ξ => g ξ * (T.mult ξ * f ξ)) :=
    (g.contDiff.continuous.mul (T.mult.contDiff.continuous.mul f.contDiff.continuous)).integrable_of_hasCompactSupport
      (g.hasCompactSupport.mul_right)
  have heM : (fun ξ => f ξ * (T.mult ξ * g ξ)) = fun ξ => g ξ * (T.mult ξ * f ξ) := by
    funext ξ
    ring
  simp only [mul_sub] at he
  have hiMr : Integrable (fun ξ => f ξ * (T.mult ξ * g ξ)) := heM.symm ▸ hiM
  rw [integral_sub hiT hiM, integral_sub hiU hiMr] at he
  have hIM := congrArg (fun h : (Fin (n + m) → ℝ) → ℝ => ∫ ξ, h ξ) heM
  rw [hIM] at he
  linarith


/-- Every standard-frame type operator,
including type zero, has its actual bilinear transpose on tests. -/
theorem exists_type_transpose_standard {lam : ℕ} (hF : C.IsStandardFrame F H K hQ)
    (T : TypeOperator F lam) :
    ∃ U : TypeOperator F lam,
      U.kernel = (fun ξ η => T.kernel η ξ) ∧ U.mult = T.mult ∧
      ∀ f g : TestFunction F.V ℝ (⊤ : ℕ∞),
        (∫ ξ, g ξ * T.apply f ξ) = ∫ η, f η * U.apply g η := by
  by_cases hl : lam = 0
  · subst lam
    exact C.exists_typeZero_transpose_standard hF T
  · exact C.exists_positiveType_transpose F hF.lifted.G_eq hF.lifted.Θ_eq
      (subset_closure.trans hF.lifted.closure_subset) (fun u _ => hF.pole_reflection u)
      hF.lifted.pole_smooth
      (by simpa only [hF.lifted.G_eq] using hF.lifted.pole_homogeneous)
      lam (Nat.one_le_iff_ne_zero.mpr hl) T

end RothschildStein.P1.LiftedChart
