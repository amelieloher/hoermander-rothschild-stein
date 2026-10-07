-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.EnumeratedLayerCorrection
public import RothschildStein.G3.FixedQuasiFactorization
public import RothschildStein.G3.WeightProjectionNorm
@[expose] public section
noncomputable section
namespace RothschildStein.G3

/-- Words through the cutoff, enumerated once in increasing homogeneous layers. -/
def correctionWordEnumeration (a s : ℕ) (p : Fin a → ℕ+) : ℕ → List (List (Fin a))
  | 0 => []
  | n+1 => correctionWordEnumeration a s p n ++ layerWordEnumeration a s p (n+1)

/-- Numerical bounds persist through the complete fixed-slot residual induction. -/
theorem exists_bounded_enumerated_residual_factorization {a s : ℕ} {p : Fin a → ℕ+}
    (hs : 1 ≤ s) (R : ℝ) (n : ℕ) (hn : n ≤ s) :
    ∃ A C : ℝ, 0 < A ∧ 0 < C ∧
      ∀ T : FiniteWordAlgebra a s p, T ∈ finiteLieSpan a s p → ‖T‖ ≤ R →
        ∃ AS : List (ℝ × List (Fin a)),
          AS.length = quasiCorrectionSlotCount a s p n ∧
          AS.map Prod.snd = correctionWordEnumeration a s p n ∧
          (∀ Z ∈ AS, Z.2 ≠ [] ∧ wordWeight p Z.2 ≤ s ∧ |Z.1| ≤ A) ∧
          FiniteOrderAtLeast (n+1) (T-signedWordProduct AS) ∧
          ‖signedWordProduct (s := s) (p := p) AS‖ ≤ C := by
  induction n with
  | zero =>
    refine ⟨1,1,by norm_num,by norm_num,?_⟩
    intro T hT _
    refine ⟨[],by simp [quasiCorrectionSlotCount],rfl,by simp,?_,?_⟩
    · change FiniteOrderAtLeast 1 (T-0)
      rw [sub_zero]
      exact formalSpan_positive_order T hT
    · simp [signedWordProduct,correctionProduct]
  | succ n ih =>
    obtain ⟨A,C,hA,hC,hprev⟩ := ih (by omega)
    obtain ⟨B,D,hB,hD,hstage⟩ := exists_bounded_enumerated_layer_correction
      (p := p) hs (by omega : 1 ≤ n+1) (by omega : n+1 ≤ s) (R+C)
    obtain ⟨F,hF,hBCH⟩ := exists_finiteBCH_norm_bound (a := a) (s := s) (p := p) (max C D)
    refine ⟨max A B,F,lt_of_lt_of_le hA (le_max_left _ _),hF,?_⟩
    intro T hT hTnorm
    obtain ⟨AS,hlen,hwords,hAS,hR,hP⟩ := hprev T hT hTnorm
    let U : FiniteWordAlgebra a s p := T-signedWordProduct AS
    let u : WordCoefficients a s p := U
    have hu : u ∈ formalSpan a s p := Submodule.sub_mem _ hT (signedWordProduct_mem AS)
    let f : weightedLieLayer (s := s) p (n+1) :=
      ⟨weightProjection (n+1) u,weightProjection_mem_weightedLieLayer (n+1) hu⟩
    have hf : ‖f.val‖ ≤ R+C := by
      have hp := norm_weightProjection_le (n+1) u
      have hnU : ‖U‖ ≤ R+C := (norm_sub_le T (signedWordProduct AS)).trans (add_le_add hTnorm hP)
      exact hp.trans hnU
    obtain ⟨BS,hBSlen,hBSwords,hBS,horder,hmatch,hQ⟩ := hstage f hf
    change FiniteOrderAtLeast (n+1+1)
      (signedWordProduct BS-finiteWeightLayer (n+1) U) at hmatch
    have hh := BCH_layer_residual_order (by omega : 1 ≤ n+1) (by omega : n+1 ≤ s)
      (formalSpan_positive_order _ (signedWordProduct_mem AS)) horder hR hmatch
    refine ⟨AS++BS,?_,?_,?_,?_,?_⟩
    · rw [List.length_append,hlen,hBSlen]
      simp only [quasiCorrectionSlotCount,Finset.sum_range_succ]
    · rw [List.map_append,hwords,hBSwords]
      rfl
    · intro Z hZ
      rcases List.mem_append.mp hZ with hZ | hZ
      · exact ⟨(hAS Z hZ).1,(hAS Z hZ).2.1,((hAS Z hZ).2.2).trans (le_max_left _ _)⟩
      · exact ⟨(hBS Z hZ).1,(hBS Z hZ).2.1.trans_le (by omega),
          ((hBS Z hZ).2.2).trans (le_max_right _ _)⟩
    · rw [signedWordProduct_append]
      exact hh
    · rw [signedWordProduct_append]
      exact hBCH _ _ (hP.trans (le_max_left _ _)) (hQ.trans (le_max_right _ _))

theorem exists_bounded_enumerated_quasi_factorization {a s : ℕ} {p : Fin a → ℕ+}
    (hs : 1 ≤ s) (R : ℝ) :
    ∃ A : ℝ, 0 < A ∧ ∀ T : FiniteWordAlgebra a s p,
      T ∈ finiteLieSpan a s p → ‖T‖ ≤ R →
      ∃ AS : List (ℝ × List (Fin a)),
        AS.length = quasiCorrectionSlotCount a s p s ∧
        AS.map Prod.snd = correctionWordEnumeration a s p s ∧
        (∀ Z ∈ AS, Z.2 ≠ [] ∧ wordWeight p Z.2 ≤ s ∧ |Z.1| ≤ A) ∧
        T = signedWordProduct AS := by
  obtain ⟨A,C,hA,hC,hfactor⟩ := exists_bounded_enumerated_residual_factorization (p := p) hs R s le_rfl
  refine ⟨A,hA,?_⟩
  intro T hT hTnorm
  obtain ⟨AS,hlen,hwords,hAS,hR,_⟩ := hfactor T hT hTnorm
  exact ⟨AS,hlen,hwords,hAS,sub_eq_zero.mp (eq_zero_of_finiteOrderAtLeast_gt hR (by omega))⟩
end RothschildStein.G3
