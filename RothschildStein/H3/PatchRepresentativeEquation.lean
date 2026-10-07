-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.AdjointTestRestriction
public import RothschildStein.H1.Standing

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory TopologicalSpace

/-- a function representing the actual distribution on
an interior patch inherits its exact distributional forcing equation. -/
theorem distribution_equation_of_patch_representative {n q : ℕ}
    (G : HomogeneousGroup n) (H : H1.StandingHypotheses G q)
    (Ω V U : Opens (Fin n → ℝ)) (hV : V ≤ Ω) (hU : U ≤ V)
    (T : Distribution Ω ℝ (⊤ : ℕ∞)) (F w : (Fin n → ℝ) → ℝ)
    (hF : LocallyIntegrableOn F (V : Set (Fin n → ℝ)) volume)
    (hw : LocallyIntegrableOn w (U : Set (Fin n → ℝ)) volume)
    (hrep : ∀ ψ : TestFunction U ℝ (⊤ : ℕ∞),
      T (TestFunction.monoCLM ℝ ψ) = ∫ x, ψ x*w x)
    (hT : ∀ ψ : TestFunction V ℝ (⊤ : ℕ∞),
      T (TestFunction.monoCLM ℝ
        (Distribution.adjointTest V H.fields (fun _ => 0)
          (fun i => (H.fields_smooth G i).contDiffOn) (by fun_prop) ψ)) =
        Distribution.ofFun V F volume (⊤ : ℕ∞) ψ)
    (ψ : TestFunction U ℝ (⊤ : ℕ∞)) :
    Distribution.ofFun U w volume (⊤ : ℕ∞)
      (Distribution.adjointTest U H.fields (fun _ => 0)
        (fun i => (H.fields_smooth G i).contDiffOn) (by fun_prop) ψ) =
      Distribution.ofFun U F volume (⊤ : ℕ∞) ψ := by
  have hh := hT (TestFunction.monoCLM ℝ ψ)
  rw [← adjointTest_mono V U hU H.fields (fun _ => 0)
    (fun i => (H.fields_smooth G i).contDiffOn) (by fun_prop),
    test_mono_comp Ω V U hV hU, hrep] at hh
  rw [Distribution.ofFun_apply hF] at hh
  have he : ((TestFunction.monoCLM ℝ ψ : TestFunction V ℝ (⊤ : ℕ∞)) :
      (Fin n → ℝ) → ℝ) = ψ := by simp [TestFunction.monoCLM_apply,hU]
  simp only [smul_eq_mul,he] at hh
  rw [Distribution.ofFun_apply hw,Distribution.ofFun_apply (hF.mono_set hU)]
  simpa only [smul_eq_mul] using hh

end RothschildStein.H3
