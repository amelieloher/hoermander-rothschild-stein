-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.QuasiCorrectionProducts
@[expose] public section
noncomputable section
namespace RothschildStein.G3

/-- A signed root correction has no coefficient below its word's
weight (BB Theorem 9.25, pp. 419–420). -/
theorem signedQuasiCorrection_weight_order {a s : ℕ} {p : Fin a → ℕ+}
    (hs : 1 ≤ s) (b : ℝ) (I : List (Fin a)) (hne : I ≠ []) :
    FiniteOrderAtLeast (wordWeight p I)
      (signedQuasiCorrection (s := s) (p := p) b I).val := by
  have hh := signedQuasiCorrection_leading_order (p := p) hs b I hne
  have he : (signedQuasiCorrection (s := s) (p := p) b I).val =
      ((signedQuasiCorrection b I).val - b • finiteBracketWord I) +
        b • finiteBracketWord I := by abel
  rw [he]
  exact finiteOrderAtLeast_add (finiteOrderAtLeast_mono hh (Nat.le_succ _))
    (finiteOrderAtLeast_smul (finiteBracketWord_weight_order p I) b)

/-- The root corrections for a finite constant-coefficient word
combination match that combination modulo the next weighted layer. -/
theorem signedCorrections_leading_sum {a s k : ℕ} {p : Fin a → ℕ+}
    (hs : 1 ≤ s) (hk : 1 ≤ k) (hks : k ≤ s)
    (BS : List (ℝ × List (Fin a)))
    (hBS : ∀ B ∈ BS, B.2 ≠ [] ∧ wordWeight p B.2 = k) :
    let CS := BS.map (fun B => (signedQuasiCorrection (s := s) (p := p) B.1 B.2).val)
    FiniteOrderAtLeast k (correctionProduct CS) ∧
      FiniteOrderAtLeast (k + 1)
        (correctionProduct CS - (BS.map (fun B => B.1 • (finiteBracketWord B.2 : FiniteWordAlgebra a s p))).sum) := by
  let CS := BS.map (fun B => (signedQuasiCorrection (s := s) (p := p) B.1 B.2).val)
  have hCS : ∀ C ∈ CS, FiniteOrderAtLeast k C := by
    intro C hC
    obtain ⟨B, hB, rfl⟩ := List.mem_map.mp hC
    have hb := hBS B hB
    rw [← hb.2]
    exact signedQuasiCorrection_weight_order hs B.1 B.2 hb.1
  have ht := correctionProduct_leading_sum hk hks CS hCS
  have hsum : FiniteOrderAtLeast (k + 1)
      (CS.sum - (BS.map (fun B => B.1 • (finiteBracketWord B.2 : FiniteWordAlgebra a s p))).sum) := by
    dsimp [CS]
    clear ht hCS CS
    induction BS with
    | nil =>
      simp only [List.map_nil, List.sum_nil, sub_self]
      exact finiteOrderAtLeast_zero_element _
    | cons B BS ih =>
      have hb := hBS B (List.mem_cons_self ..)
      have hr := ih (fun D hD => hBS D (List.mem_cons_of_mem B hD))
      have hh := signedQuasiCorrection_leading_order (p := p) hs B.1 B.2 hb.1
      rw [hb.2] at hh
      simp only [List.map_cons, List.sum_cons]
      have he : (signedQuasiCorrection (s := s) (p := p) B.1 B.2).val +
          (BS.map (fun D => (signedQuasiCorrection (s := s) (p := p) D.1 D.2).val)).sum -
          (B.1 • finiteBracketWord B.2 +
            (BS.map (fun D => D.1 • (finiteBracketWord D.2 : FiniteWordAlgebra a s p))).sum) =
          ((signedQuasiCorrection B.1 B.2).val - B.1 • finiteBracketWord B.2) +
            ((BS.map (fun D => (signedQuasiCorrection (s := s) (p := p) D.1 D.2).val)).sum -
              (BS.map (fun D => D.1 • (finiteBracketWord D.2 : FiniteWordAlgebra a s p))).sum) := by abel
      rw [he]
      exact finiteOrderAtLeast_add hh hr
  refine ⟨ht.1, ?_⟩
  have he : correctionProduct CS -
      (BS.map (fun B => B.1 • (finiteBracketWord B.2 : FiniteWordAlgebra a s p))).sum =
      (correctionProduct CS - CS.sum) +
        (CS.sum - (BS.map (fun B => B.1 • (finiteBracketWord B.2 : FiniteWordAlgebra a s p))).sum) := by abel
  rw [he]
  exact finiteOrderAtLeast_add ht.2 hsum
end RothschildStein.G3
