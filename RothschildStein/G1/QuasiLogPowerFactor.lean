-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G3.QuasiExponentialJet
public import RothschildStein.G3.DilatedInputCoordinates

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set
open scoped BigOperators

namespace RothschildStein.G1
open G3

/-- The retained logarithm's actual coordinate polynomial has
an exact smooth time-power factor. Its zero coefficient is the positive
nested word, including weighted drift letters (BB Lemma 9.26, pp. 417–419;
Theorem 1.48, pp. 32–34). -/
theorem exists_quasi_log_coordinate_power_factor {a s : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (hs : 1 ≤ s) (I : List (Fin a)) :
    ∃ H : ℝ → (Fin (freeDimension a s p) → ℝ), ContDiff ℝ (⊤ : ℕ∞) H ∧
      H 0 = D.basis.equivFun (wordLieElement I) ∧
      ∀ t, dilatedInputCoordinates D (quasiExponentialLog I) t =
        t ^ wordWeight p I • H t := by
  let k := wordWeight p I
  have hmem (j : ℕ) : quasiJetComponent (s := s) (p := p) I j ∈ formalSpan a s p :=
    weightProjection_mem_formalSpan j (Submodule.sub_mem _
      (quasiExponentialLog I).property (wordLieElement I).property)
  let c (j : ℕ) := D.basis.equivFun ⟨quasiJetComponent I j, hmem j⟩
  have hc (j : ℕ) (hj : j ≤ k) : c j = 0 := by
    have he : (⟨quasiJetComponent I j, hmem j⟩ : formalSpan a s p) = 0 :=
      Subtype.ext (quasiJetComponent_eq_zero hs I hj)
    dsimp only [c]
    rw [he, map_zero]
  let H := fun t : ℝ => D.basis.equivFun (wordLieElement I) +
    ∑ j ∈ Finset.range (s + 1), t ^ (j - k) • c j
  have hH : ContDiff ℝ (⊤ : ℕ∞) H :=
    contDiff_const.add (ContDiff.sum (fun j _ => (contDiff_id.pow (j - k)).smul contDiff_const))
  refine ⟨H, hH, ?_, ?_⟩
  · change _ + _ = _
    rw [Finset.sum_eq_zero]
    · exact add_zero _
    · intro j _
      by_cases hj : j ≤ k
      · rw [hc j hj, smul_zero]
      · rw [zero_pow (by omega : j - k ≠ 0), zero_smul]
  · intro t
    have he : (quasiExponentialLogAt (s := s) (p := p) t I : formalSpan a s p) =
        t ^ k • wordLieElement I +
          ∑ j ∈ Finset.range (s + 1), t ^ j • ⟨quasiJetComponent I j, hmem j⟩ := by
      apply Subtype.ext
      change (quasiExponentialLogAt (s := s) (p := p) t I).val =
        (formalSpan a s p).subtype (t ^ k • wordLieElement I +
          ∑ j ∈ Finset.range (s + 1), t ^ j • ⟨quasiJetComponent I j, hmem j⟩)
      rw [map_add, map_smul, map_sum]
      simp only [map_smul, Submodule.subtype_apply, wordLieElement]
      exact quasiExponentialLogAt_jet (s := s) (p := p) t I
    rw [dilatedInputCoordinates_eq]
    change D.basis.equivFun (quasiExponentialLogAt t I) = _
    rw [he, map_add, map_sum]
    simp only [map_smul]
    dsimp only [H]
    rw [smul_add, Finset.smul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    change t ^ j • c j = t ^ k • (t ^ (j - k) • c j)
    by_cases hj : j ≤ k
    · rw [hc j hj, smul_zero, smul_zero, smul_zero]
    · rw [smul_smul, ← pow_add, Nat.add_sub_of_le (by omega : k ≤ j)]

end RothschildStein.G1
