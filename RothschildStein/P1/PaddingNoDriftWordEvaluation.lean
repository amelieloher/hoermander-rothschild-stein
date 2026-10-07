-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PaddingNoDriftDefs
public import RothschildStein.P1.PaddingVectorDerivative
public import RothschildStein.G1.BracketAlgebra

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter
open scoped Topology
namespace RothschildStein.P1

/-- Every original no-drift standard bracket word extends
with zero fiber components. No artificial drift enters the word carrier. -/
theorem wordBracket_paddingNoDrift_map {q n d : ℕ}
    (Ω : Set (Fin n → ℝ)) (hΩ : IsOpen Ω)
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω) :
    ∀ I : List (Fin q), EqOn
      (wordBracket (paddingNoDriftVectorFields (d := d) X) (I.map (Fin.castAdd d)))
      (paddingBaseField (d := d) (wordBracket X I)) ((paddingBaseCLM n d) ⁻¹' Ω) := by
  let U := (paddingBaseCLM n d) ⁻¹' Ω
  have hU : IsOpen U := hΩ.preimage (paddingBaseCLM n d).continuous
  intro I
  induction I with
  | nil =>
      intro ξ _
      change 0 = joinPoint (0 : Fin n → ℝ) (0 : Fin d → ℝ)
      rw [← paddingJoinCLM_apply]
      exact (map_zero (paddingJoinCLM n d)).symm
  | cons i I ih =>
      cases I with
      | nil =>
          intro ξ _
          simp only [List.map_cons, List.map_nil, wordBracket,
            paddingNoDriftVectorFields_original]
      | cons j I =>
          intro ξ hξ
          have ht : wordBracket (paddingNoDriftVectorFields (d := d) X)
              ((j :: I).map (Fin.castAdd d)) =ᶠ[𝓝 ξ]
              paddingBaseField (d := d) (wordBracket X (j :: I)) := by
            filter_upwards [hU.mem_nhds hξ] with y hy
            exact ih hy
          have hdi := ((hX i).contDiffAt (hΩ.mem_nhds hξ)).differentiableAt (by simp)
          have hdj := ((G1.wordBracket_contDiffOn hΩ X hX (j :: I)).contDiffAt
            (hΩ.mem_nhds hξ)).differentiableAt (by simp)
          simp only [List.map_cons, wordBracket, paddingNoDriftVectorFields_original]
          have hb := lieBracket_paddingBaseField (d := d) (X i) (wordBracket X (j :: I)) ξ hdi hdj
          refine Eq.trans ?_ hb
          change fderiv ℝ (wordBracket (paddingNoDriftVectorFields (d := d) X)
              ((j :: I).map (Fin.castAdd d))) ξ (paddingBaseField (d := d) (X i) ξ) -
              fderiv ℝ (paddingBaseField (d := d) (X i)) ξ
                (wordBracket (paddingNoDriftVectorFields (d := d) X)
                  ((j :: I).map (Fin.castAdd d)) ξ) = _
          rw [ht.fderiv_eq, ih hξ]
          rfl

end RothschildStein.P1
