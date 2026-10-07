-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.FiniteAnalytic
@[expose] public section
noncomputable section
open Set Metric
namespace RothschildStein.G3

theorem contDiff_finiteBCH {a s : ℕ} {p : Fin a → ℕ+} :
    ContDiff ℝ (⊤ : ℕ∞) (fun z : FiniteWordAlgebra a s p × FiniteWordAlgebra a s p =>
      finiteBCH z.1 z.2) := by
  unfold finiteBCH
  exact (contDiff_logApprox s).comp
    ((((contDiff_finite_mul.comp
      ((contDiff_finiteExp.comp contDiff_fst).prodMk
        (contDiff_finiteExp.comp contDiff_snd)))).sub contDiff_const))

/-- Fixed finite BCH coefficients give bounds on each numerical coefficient ball. -/
theorem exists_finiteBCH_norm_bound {a s : ℕ} {p : Fin a → ℕ+} (R : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ A B : FiniteWordAlgebra a s p,
      ‖A‖ ≤ R → ‖B‖ ≤ R → ‖finiteBCH A B‖ ≤ C := by
  let K : Set (FiniteWordAlgebra a s p × FiniteWordAlgebra a s p) := closedBall (0 : FiniteWordAlgebra a s p) R ×ˢ closedBall 0 R
  have hK : IsCompact K := (isCompact_closedBall _ _).prod (isCompact_closedBall _ _)
  obtain ⟨C,hC⟩ := (hK.image (contDiff_finiteBCH (a := a) (s := s) (p := p)).continuous).isBounded.exists_norm_le
  refine ⟨1+|C|,by positivity,?_⟩
  intro A B hA hB
  have hz : (A,B) ∈ K := by simpa [K,mem_closedBall,dist_zero_right] using And.intro hA hB
  exact (hC _ (mem_image_of_mem _ hz)).trans (by linarith [le_abs_self C])
end RothschildStein.G3
