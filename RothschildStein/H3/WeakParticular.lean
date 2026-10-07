-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.PatchRegularity
public import RothschildStein.H3.WeakOperatorDistributionEquation
public import RothschildStein.H3.QuasiballDomainRestriction

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory TopologicalSpace
open scoped ENNReal

/-- a certified weak Sobolev particular solution on an
interior patch supplies local Sobolev regularity of the original actual
distribution. Its distributional equation and local integrability are
proved from the weak operator, rather than supplied separately. -/
theorem patch_regular_of_weak_particular_solution {n q : ℕ}
    (G : HomogeneousGroup n) (H : H1.StandingHypotheses G q)
    (Ω V U : Opens (Fin n → ℝ)) (hV : V ≤ Ω)
    (hK : IsCompact (closure (U : Set (Fin n → ℝ))))
    (hKV : closure (U : Set (Fin n → ℝ)) ⊆ V)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (T : Distribution Ω ℝ (⊤ : ℕ∞))
    (F v : (Fin n → ℝ) → ℝ)
    (hv : memSobolevX driftWeight H.fields V 2 p v)
    (D : WeakDriftOperatorData H.fields V p v)
    (hD : D.operator =ᵐ[volume.restrict (V : Set (Fin n → ℝ))] F)
    (hT : ∀ ψ : TestFunction V ℝ (⊤ : ℕ∞),
      T (TestFunction.monoCLM ℝ
        (Distribution.adjointTest V H.fields (fun _ => 0)
          (fun i => (H.fields_smooth G i).contDiffOn) (by fun_prop) ψ)) =
        Distribution.ofFun V F volume (⊤ : ℕ∞) ψ) :
    ∃ w : (Fin n → ℝ) → ℝ, memSobolevX driftWeight H.fields U 2 p w ∧
      ∀ ψ : TestFunction U ℝ (⊤ : ℕ∞),
        T (TestFunction.monoCLM ℝ ψ) = ∫ x, ψ x*w x := by
  apply patch_regular_of_particular_solution G H Ω V U hV hK hKV p T
    (Distribution.ofFun V F volume (⊤ : ℕ∞)) v (D.first_weak 0).1
    (S.memSobolevX_restrict driftWeight H.fields V U (subset_closure.trans hKV) hv) hT
  intro ψ
  exact D.ofFun_adjoint_equation hp (fun i => (H.fields_smooth G i).contDiffOn) F hD ψ

end RothschildStein.H3
