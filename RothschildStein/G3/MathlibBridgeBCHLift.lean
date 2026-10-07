-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G3.MathlibBridgeLie

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.G3
variable {a : ℕ}

/-- Nested syntax is exactly the fixed right-fold
free Lie monomial, with the same number of leaves (BB pp. 471–472). -/
theorem mathlibNested_foldr (u : Nested (Fin a)) :
    ∃ (l : List (Fin a)) (j : Fin a),l.length+1 = u.letters.length ∧
      u.eval (FreeLieAlgebra.of ℚ) =
        l.foldr (fun i b => ⁅FreeLieAlgebra.of ℚ i,b⁆) (FreeLieAlgebra.of ℚ j) := by
  induction u with
  | letter i => exact ⟨[],i,rfl,rfl⟩
  | bracket i u ih =>
    obtain ⟨l,j,hl,he⟩ := ih
    exact ⟨i::l,j,by simpa only [Nested.letters,List.length_cons] using congrArg (·+1) hl,
      by simp only [Nested.eval,List.foldr_cons,he]⟩

/-- The chosen homogeneous nested span satisfies
exactly the Lie-homogeneity clause fixed at the root (BB p. 472). -/
theorem mathlibHomogeneousLieSpan_le_frozen (n : ℕ) :
    mathlibHomogeneousLieSpan a n ≤ Submodule.span ℚ
      {z : FreeLieAlgebra ℚ (Fin a) | ∃ (l : List (Fin a)) (j : Fin a),l.length+1 = n ∧
        z = l.foldr (fun i b => ⁅FreeLieAlgebra.of ℚ i,b⁆) (FreeLieAlgebra.of ℚ j)} := by
  apply Submodule.span_le.mpr
  rintro z ⟨u,hu,rfl⟩
  obtain ⟨l,j,hl,he⟩ := mathlibNested_foldr u
  exact Submodule.subset_span ⟨l,j,hl.trans hu,he⟩

/-- Every n-leaf nested free bracket has an
associatively homogeneous canonical image of degree n (BB p. 472). -/
theorem mathlibNested_image_mem_generatorSpan_pow (u : Nested (Fin a)) :
    mathlibLieImage a (u.eval (FreeLieAlgebra.of ℚ)) ∈
      Submodule.span ℚ (Set.range (FreeAlgebra.ι ℚ : Fin a → FreeAlgebra ℚ (Fin a))) ^ u.letters.length := by
  let M := Submodule.span ℚ (Set.range (FreeAlgebra.ι ℚ : Fin a → FreeAlgebra ℚ (Fin a)))
  have hgen : ∀ i,FreeAlgebra.ι ℚ i ∈ M := fun i => Submodule.subset_span (Set.mem_range_self i)
  induction u with
  | letter i => simpa only [Nested.eval,Nested.letters,List.length_singleton,
      mathlibLieImage_generator,Submodule.pow_one] using hgen i
  | bracket i u ih =>
    change mathlibLieImage a ⁅FreeLieAlgebra.of ℚ i,u.eval (FreeLieAlgebra.of ℚ)⁆ ∈ M ^ (u.letters.length+1)
    rw [mathlibLieImage_bracket,mathlibLieImage_generator]
    apply Submodule.sub_mem
    · rw [Submodule.pow_succ' M (fun h => u.letters_ne_nil (List.length_eq_zero_iff.mp h))]
      exact Submodule.mul_mem_mul (hgen i) ih
    · rw [Submodule.pow_succ]
      exact Submodule.mul_mem_mul ih (hgen i)

/-- Rational spans preserve associative homogeneity
of the canonical images, without invoking free-Lie injectivity (BB p. 472). -/
theorem mathlibLieImage_mem_generatorSpan_pow {n : ℕ} {z : FreeLieAlgebra ℚ (Fin a)}
    (hz : z ∈ mathlibHomogeneousLieSpan a n) :
    mathlibLieImage a z ∈
      Submodule.span ℚ (Set.range (FreeAlgebra.ι ℚ : Fin a → FreeAlgebra ℚ (Fin a))) ^ n := by
  induction hz using Submodule.span_induction with
  | mem z hz => obtain ⟨u,hu,rfl⟩ := hz; rw [← hu]; exact mathlibNested_image_mem_generatorSpan_pow u
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add z t _ _ hz ht => rw [map_add]; exact Submodule.add_mem _ hz ht
  | smul r z _ hz => rw [map_smul]; exact Submodule.smul_mem _ r hz

/-- A free-Lie lift of every rational BCH component
exists by the proved homogeneous rational Lie-span theorem (BB pp. 471–474). -/
def mathlibBCHLift (n : ℕ) : FreeLieAlgebra ℚ (Fin 2) :=
  if n = 0 then 0 else if n = 1 then FreeLieAlgebra.of ℚ (0 : Fin 2) + FreeLieAlgebra.of ℚ (1 : Fin 2)
  else if n = 2 then (1/2 : ℚ) • ⁅FreeLieAlgebra.of ℚ (0 : Fin 2),FreeLieAlgebra.of ℚ (1 : Fin 2)⁆
  else (exists_mathlib_homogeneous_lie_lift (bchComponent_mem_homogeneousRationalLieSpan n)).choose

/-- The selected Lie lift has its prescribed
homogeneous leaf count, including the zero component (BB pp. 471–474). -/
theorem mathlibBCHLift_mem (n : ℕ) : mathlibBCHLift n ∈ mathlibHomogeneousLieSpan 2 n := by
  unfold mathlibBCHLift
  split
  · subst n; exact Submodule.zero_mem _
  · split
    · subst n
      exact Submodule.add_mem _ (Submodule.subset_span ⟨Nested.letter 0,rfl,rfl⟩)
        (Submodule.subset_span ⟨Nested.letter 1,rfl,rfl⟩)
    · split
      · subst n
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨Nested.bracket 0 (.letter 1),rfl,rfl⟩)
      · exact (exists_mathlib_homogeneous_lie_lift
          (bchComponent_mem_homogeneousRationalLieSpan n)).choose_spec.1

/-- The selected free-Lie component has exactly
the existing BCH coefficients; the sign and rational scalar of C2 are
preserved (BB pp. 470–471). -/
theorem mathlibBCHLift_coefficients (n : ℕ) :
    mathlibCoefficients 2 (mathlibLieImage 2 (mathlibBCHLift n)) = bchComponent n := by
  unfold mathlibBCHLift
  split
  · subst n; simp only [map_zero,bchComponent_zero]
  · split
    · subst n; simp only [map_add,mathlibLieImage_generator,mathlibCoefficients_generator,bchComponent_one]
    · split
      · subst n
        rw [map_smul,map_smul]
        have he := mathlibCoefficients_nested (Nested.bracket (0 : Fin 2) (.letter 1))
        change mathlibCoefficients 2 (mathlibLieImage 2 ⁅FreeLieAlgebra.of ℚ (0 : Fin 2),FreeLieAlgebra.of ℚ (1 : Fin 2)⁆) =
          ⁅letterSeries 0,letterSeries 1⁆ at he
        rw [he,bchComponent_two]
        have hbr : ⁅letterSeries (0 : Fin 2),letterSeries 1⁆ = formalBracket [0,1] :=
          nested_eval_formalBracket (Nested.bracket (0 : Fin 2) (.letter 1))
        rw [← hbr]
        change (1/2 : ℚ) • ⁅letterSeries 0,letterSeries 1⁆ = (1/2 : ℝ) • ⁅letterSeries 0,letterSeries 1⁆
        simpa only [Rat.cast_id,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using
          (ratCast_smul_eq ℚ ℝ (1/2 : ℚ)
            (⁅letterSeries (0 : Fin 2),letterSeries (1 : Fin 2)⁆ : CoefficientSeries 2))
      · exact (exists_mathlib_homogeneous_lie_lift
          (bchComponent_mem_homogeneousRationalLieSpan n)).choose_spec.2

end RothschildStein.G3
