-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.Integration
public import RothschildStein.Definitions.sumSquaresWithDriftTransposeTest
public import RothschildStein.Definitions.isFundamentalDistribution

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

@[expose] public section
noncomputable section
namespace RothschildStein.H1
open MeasureTheory TopologicalSpace
open scoped BigOperators
variable {N q : ℕ} (G : HomogeneousGroup N)

/-- The bundled transpose test has precisely the scalar group operator as its function
(BB Definition 6.16, p. 264). -/
theorem StandingHypotheses.transposeTest_apply (H : StandingHypotheses G q)
    (U : Opens (Fin N → ℝ)) (φ : TestFunction U ℝ (⊤ : ℕ∞)) (x : Fin N → ℝ) :
    sumSquaresWithDriftTransposeTest U H.fields (fun i => (H.fields_smooth G i).contDiffOn) φ x =
      sumSquaresWithDriftTranspose H.fields φ x := by
  let ev : TestFunction U ℝ (⊤ : ℕ∞) →+ ℝ :=
    { toFun ψ := ψ x, map_zero' := rfl, map_add' _ _ := rfl }
  change ev (fieldTransposeTest U (H.fields 0) (H.fields_smooth G 0).contDiffOn φ +
    ∑ i : Fin q, fieldTransposeTest U (H.fields i.succ) (H.fields_smooth G i.succ).contDiffOn
      (fieldTransposeTest U (H.fields i.succ) (H.fields_smooth G i.succ).contDiffOn φ)) = _
  rw [map_add, map_sum]
  change fieldTransposeTest U (H.fields 0) (H.fields_smooth G 0).contDiffOn φ x +
    ∑ i : Fin q, fieldTransposeTest U (H.fields i.succ) (H.fields_smooth G i.succ).contDiffOn
      (fieldTransposeTest U (H.fields i.succ) (H.fields_smooth G i.succ).contDiffOn φ) x = _
  rw [S.fieldTransposeTest_apply]
  unfold sumSquaresWithDriftTranspose
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [S.fieldTransposeTest_apply, S.fieldTransposeTest_coe]

/-- The fundamental-solution predicate is the concrete transpose pairing
(BB Definition 6.16, p. 264). No existence of a fundamental solution is asserted here. -/
theorem StandingHypotheses.isFundamentalDistribution_iff (H : StandingHypotheses G q)
    (T : Distribution (⊤ : Opens (Fin N → ℝ)) ℝ (⊤ : ℕ∞)) :
    isFundamentalDistribution (sumSquaresWithDriftTranspose H.fields) T ↔
      ∀ φ : TestFunction (⊤ : Opens (Fin N → ℝ)) ℝ (⊤ : ℕ∞),
        T (sumSquaresWithDriftTransposeTest ⊤ H.fields
          (fun i => (H.fields_smooth G i).contDiffOn) φ) = φ 0 := by
  constructor
  · intro h φ
    obtain ⟨ψ, hψ, he⟩ := h φ
    have hh : ψ = sumSquaresWithDriftTransposeTest ⊤ H.fields
        (fun i => (H.fields_smooth G i).contDiffOn) φ := by
      ext x
      rw [hψ x, H.transposeTest_apply G]
    rwa [hh] at he
  · intro h φ
    exact ⟨sumSquaresWithDriftTransposeTest ⊤ H.fields
      (fun i => (H.fields_smooth G i).contDiffOn) φ, H.transposeTest_apply G ⊤ φ, h φ⟩

end RothschildStein.H1
