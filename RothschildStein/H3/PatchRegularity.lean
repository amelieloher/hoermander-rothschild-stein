-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.SobolevDistributionParticular
public import RothschildStein.S.DistributionRestriction

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory TopologicalSpace
open scoped ENNReal

/-- the particular solution and forcing need agree only
on an interior patch. The original distribution is retained on its
larger domain and represented on the relatively compact subpatch. -/
theorem patch_regular_of_particular_solution {n q : ℕ}
    (G : HomogeneousGroup n) (H : H1.StandingHypotheses G q)
    (Ω V U : Opens (Fin n → ℝ)) (hV : V ≤ Ω)
    (hK : IsCompact (closure (U : Set (Fin n → ℝ))))
    (hKV : closure (U : Set (Fin n → ℝ)) ⊆ V)
    (p : ℝ≥0∞) (T : Distribution Ω ℝ (⊤ : ℕ∞))
    (F : Distribution V ℝ (⊤ : ℕ∞)) (v : (Fin n → ℝ) → ℝ)
    (hv : LocallyIntegrableOn v (V : Set (Fin n → ℝ)) volume)
    (hvs : memSobolevX driftWeight H.fields U 2 p v)
    (hT : ∀ ψ : TestFunction V ℝ (⊤ : ℕ∞),
      T (TestFunction.monoCLM ℝ
        (Distribution.adjointTest V H.fields (fun _ => 0)
          (fun i => (H.fields_smooth G i).contDiffOn) (by fun_prop) ψ)) = F ψ)
    (hsol : ∀ ψ : TestFunction V ℝ (⊤ : ℕ∞),
      Distribution.ofFun V v volume (⊤ : ℕ∞)
        (Distribution.adjointTest V H.fields (fun _ => 0)
          (fun i => (H.fields_smooth G i).contDiffOn) (by fun_prop) ψ) = F ψ) :
    ∃ w : (Fin n → ℝ) → ℝ, memSobolevX driftWeight H.fields U 2 p w ∧
      ∀ ψ : TestFunction U ℝ (⊤ : ℕ∞),
        T (TestFunction.monoCLM ℝ ψ) = ∫ x, ψ x*w x := by
  obtain ⟨w,hw,hrep⟩ := local_regular_of_particular_solution G H V U hK hKV p
    (S.distributionRestrictionCLM Ω V T) F v hv hvs hT hsol
  refine ⟨w,hw,?_⟩
  intro ψ
  have hU : U ≤ V := subset_closure.trans hKV
  have hext : ((TestFunction.monoCLM ℝ ψ : TestFunction V ℝ (⊤ : ℕ∞)) :
      (Fin n → ℝ) → ℝ) = ψ := by simp [TestFunction.monoCLM_apply,hU]
  have hcomp : (TestFunction.monoCLM ℝ
      (TestFunction.monoCLM ℝ ψ : TestFunction V ℝ (⊤ : ℕ∞)) :
      TestFunction Ω ℝ (⊤ : ℕ∞)) = TestFunction.monoCLM ℝ ψ := by
    ext x
    simp [TestFunction.monoCLM_apply,hU,hV,hU.trans hV]
  have hh := hrep (TestFunction.monoCLM ℝ ψ)
  change T (TestFunction.monoCLM ℝ
    (TestFunction.monoCLM ℝ ψ : TestFunction V ℝ (⊤ : ℕ∞))) = _ at hh
  rw [hcomp] at hh
  simpa only [hext] using hh

end RothschildStein.H3
