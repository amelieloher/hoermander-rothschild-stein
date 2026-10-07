-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.FixedLayerCoefficientBounds
public import RothschildStein.G3.QuasiCorrectionNormBounds
public import RothschildStein.G3.CorrectionProductNormBounds
@[expose] public section
noncomputable section
open scoped BigOperators
namespace RothschildStein.G3

/-- Canonical enumeration of the words in one retained homogeneous layer. -/
def layerWordEnumeration (a s : ℕ) (p : Fin a → ℕ+) (k : ℕ) : List (List (Fin a)) :=
  (Finset.univ : Finset (LayerWord a s p k)).toList.map (fun I => I.val.val)

theorem exists_bounded_enumerated_layer_correction {a s k : ℕ} {p : Fin a → ℕ+}
    (hs : 1 ≤ s) (hk : 1 ≤ k) (hks : k ≤ s) (R : ℝ) :
    ∃ A C : ℝ, 0 < A ∧ 0 < C ∧
      ∀ f : weightedLieLayer (s := s) p k, ‖f.val‖ ≤ R →
        let F : FiniteWordAlgebra a s p := f.val
        ∃ BS : List (ℝ × List (Fin a)),
          BS.length = Fintype.card (LayerWord a s p k) ∧
          BS.map Prod.snd = layerWordEnumeration a s p k ∧
          (∀ B ∈ BS, B.2 ≠ [] ∧ wordWeight p B.2 = k ∧ |B.1| ≤ A) ∧
          FiniteOrderAtLeast k (signedWordProduct (s := s) (p := p) BS) ∧
          FiniteOrderAtLeast (k+1) (signedWordProduct (s := s) (p := p) BS-F) ∧
          ‖signedWordProduct (s := s) (p := p) BS‖ ≤ C := by
  classical
  obtain ⟨D,hD,hcoeff⟩ := exists_bounded_layer_representation hk hks
  let A := D*(1+|R|)
  have hA : 0 < A := by dsimp [A]; positivity
  obtain ⟨B,hB,hword⟩ := exists_quasiCorrection_norm_bound (a := a) (s := s) (p := p) A
  obtain ⟨C,hC,hprod⟩ := exists_correctionProduct_norm_bound (a := a) (s := s) (p := p)
    B (Fintype.card (LayerWord a s p k))
  refine ⟨A,C,hA,hC,?_⟩
  intro f hf
  obtain ⟨c,hc,hcnorm⟩ := hcoeff f
  let BS := (Finset.univ : Finset (LayerWord a s p k)).toList.map
    (fun I => (c I,I.val.val))
  have hlen : BS.length = Fintype.card (LayerWord a s p k) := by simp [BS]
  have hBS : ∀ Z ∈ BS, Z.2 ≠ [] ∧ wordWeight p Z.2 = k ∧ |Z.1| ≤ A := by
    intro Z hZ
    obtain ⟨I,_,rfl⟩ := List.mem_map.mp hZ
    refine ⟨layerWord_ne_nil hk I,I.property,?_⟩
    have hi : |c I| ≤ ‖c‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm c I
    exact (hi.trans hcnorm).trans (by
      dsimp [A]
      exact mul_le_mul_of_nonneg_left (hf.trans (by linarith [le_abs_self R])) hD.le)
  have hsum0 : (BS.map (fun Z => Z.1 •
      (truncatedBracket Z.2 : WordCoefficients a s p))).sum = f.val := by
    simpa only [BS,List.map_map,Function.comp_def,Finset.sum_map_toList] using hc
  have hsum : (BS.map (fun Z => Z.1 •
      (finiteBracketWord Z.2 : FiniteWordAlgebra a s p))).sum =
      (f.val : FiniteWordAlgebra a s p) := hsum0
  have he := signedCorrections_leading_sum hs hk hks BS
    (fun Z hZ => ⟨(hBS Z hZ).1,(hBS Z hZ).2.1⟩)
  rw [hsum] at he
  refine ⟨BS,hlen,by simp [BS,layerWordEnumeration,List.map_map,Function.comp_def],hBS,he.1,he.2,?_⟩
  apply hprod
  · simpa only [List.length_map,hlen] using le_rfl
  · intro Z hZ
    obtain ⟨Q,hQ,rfl⟩ := List.mem_map.mp hZ
    let I : BoundedWord a s p := boundedWord p Q.2 ((hBS Q hQ).2.1 ▸ hks)
    exact hword I (hBS Q hQ).1 Q.1 (hBS Q hQ).2.2
end RothschildStein.G3
