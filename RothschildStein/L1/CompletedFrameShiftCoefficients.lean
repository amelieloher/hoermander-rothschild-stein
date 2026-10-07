-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.SelectedAuxiliaryControls
public import RothschildStein.G4.SelectedAuxiliaryFamily

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped BigOperators
namespace RothschildStein.L1

/-- Insert the vertical completion coefficients into the fixed
full short-word coefficient carrier (BB pp. 520–521). -/
def completionShift {q m s : ℕ} (w : Fin q → ℕ+)
    (J : Fin m → G4.ShortWord w s) (v : Fin m → ℝ) :
    Fin (Fintype.card (G4.ShortWord w s)) → ℝ :=
  G4.aggregateMappedControls ((Fintype.equivFin (G4.ShortWord w s)) ∘ J) v

/-- A completion with no repeated word embeds its strict
weighted parameter box into the original chart's shift box. -/
theorem completionShift_mem_weightedBox {q m s : ℕ} (w : Fin q → ℕ+)
    (J : Fin m → G4.ShortWord w s) (hJ : Function.Injective J)
    {r : ℝ} (hr : 0 < r) {v : Fin m → ℝ}
    (hv : v ∈ G4.weightedBox (G4.shortWeight w ∘ J) r) :
    completionShift w J v ∈ G4.weightedBox
      (fun j => G4.shortWeight w (G4.shortIndex (s := s) w j)) r := by
  classical
  let Jf := (Fintype.equivFin (G4.ShortWord w s)) ∘ J
  have hJf : Function.Injective Jf := (Fintype.equivFin _).injective.comp hJ
  intro j
  by_cases hj : ∃ l, Jf l = j
  · obtain ⟨l,rfl⟩ := hj
    have he : completionShift w J v (Jf l) = v l := by
      change G4.aggregateMappedControls Jf v (Jf l) = v l
      simp [G4.aggregateMappedControls, hJf.eq_iff]
    rw [he]
    simpa only [Jf, Function.comp_apply, G4.shortIndex, Equiv.symm_apply_apply] using hv l
  · have he : completionShift w J v j = 0 := by
      change (∑ l, if Jf l = j then v l else 0) = 0
      apply Finset.sum_eq_zero
      intro l _
      exact ite_eq_right (fun hl => hj ⟨l,hl⟩)
    rw [he,abs_zero]
    exact pow_pos hr _

/-- The completed-frame flow and the shifted selected-frame
flow have exactly the same constant field, including the shift terms. -/
theorem completionShift_field_eq {q n m d s : ℕ} (w : Fin q → ℕ+)
    (B : Fin n → G4.ShortWord w s) (J : Fin m → G4.ShortWord w s)
    (u : Fin n → ℝ) (v : Fin m → ℝ)
    (Z : G4.ShortWord w s → (Fin d → ℝ) → (Fin d → ℝ)) (x : Fin d → ℝ) :
    (∑ i : Fin (n+m), Fin.append u v i • Z (Fin.addCases B J i) x) =
      ∑ i : Fin (n+Fintype.card (G4.ShortWord w s)),
        Fin.append u (completionShift w J v) i • Z (G4.selectedAuxiliaryIndex w B i) x := by
  rw [Fin.sum_univ_add, Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, Fin.addCases_left, Fin.addCases_right,
    G4.selectedAuxiliaryIndex_selected, G4.selectedAuxiliaryIndex_auxiliary]
  congr 1
  have he := G4.aggregateMappedControls_field_eq
    ((Fintype.equivFin (G4.ShortWord w s)) ∘ J) v
    (fun j => Z (G4.shortIndex w j)) x
  simpa only [completionShift, Function.comp_apply, G4.shortIndex,
    Equiv.symm_apply_apply] using he.symm

/-- The actual completed-frame determinant supplies the needed
absence of repeated completion words (BB pp. 520–521). -/
theorem completionShift_mem_weightedBox_of_frameDet_ne_zero {q n m s : ℕ}
    (w : Fin q → ℕ+) (B : Fin n → G4.ShortWord w s)
    (J : Fin m → G4.ShortWord w s)
    (Z : G4.ShortWord w s → (Fin (n+m) → ℝ) → (Fin (n+m) → ℝ))
    (ξ : Fin (n+m) → ℝ)
    (hdet : G4.frameDet Z (Fin.addCases B J) ξ ≠ 0)
    {r : ℝ} (hr : 0 < r) {v : Fin m → ℝ}
    (hv : v ∈ G4.weightedBox (G4.shortWeight w ∘ J) r) :
    completionShift w J v ∈ G4.weightedBox
      (fun j => G4.shortWeight w (G4.shortIndex (s := s) w j)) r := by
  have hf := G4.frame_index_injective_of_frameDet_ne_zero Z (Fin.addCases B J) hdet
  have hJ : Function.Injective J := by
    intro l l' he
    have hh : Fin.natAdd n l = Fin.natAdd n l' :=
      hf (by simpa only [Fin.addCases_right] using he)
    have hv := congrArg Fin.val hh
    apply Fin.ext
    change n + l.val = n + l'.val at hv
    omega
  exact completionShift_mem_weightedBox w J hJ hr hv

end RothschildStein.L1
