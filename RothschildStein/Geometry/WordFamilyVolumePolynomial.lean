-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G4.FrameReindex
public import RothschildStein.G4.VolumePolynomial
public import Mathlib.Data.Fintype.BigOperators
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal
namespace RothschildStein.Geometry

/-- Empty-word columns are zero, so the literal fixed word-family
polynomial equals the nonempty short-word polynomial, without a factor. -/
theorem wordFamily_volumePolynomial_eq {a n s : ℕ} (w : Fin a → ℕ+)
    (X : Fin a → (Fin n → ℝ) → (Fin n → ℝ)) (x : Fin n → ℝ) (r : ℝ) :
    (∑ B ∈ Fintype.piFinset (fun _ : Fin n => wordFamily w s),
      |(Matrix.of fun i j => wordBracket X (B j) x i).det| * r ^ (∑ j, wordWeight w (B j))) =
    G4.volumePolynomial (fun B : Fin n → G4.ShortWord w s => G4.frameDet (G4.shortField w X) B x)
      (fun B => ∑ i, (G4.shortWeight w (B i) : ℕ)) r := by
  classical
  let f := fun B : Fin n → List (Fin a) =>
    |(Matrix.of fun i j => wordBracket X (B j) x i).det| * r ^ (∑ j, wordWeight w (B j))
  let g := fun B : Fin n → G4.ShortWord w s =>
    |G4.frameDet (G4.shortField w X) B x| * r ^ (∑ j, (G4.shortWeight w (B j) : ℕ))
  have hne : ∀ B, f B ≠ 0 → ∀ j, B j ≠ [] := by
    intro B hB j hj
    have hz : (Matrix.of fun i j => wordBracket X (B j) x i).det = 0 :=
      Matrix.det_eq_zero_of_column_eq_zero j (by intro i; simp [hj, wordBracket])
    exact hB (by simp [f, hz])
  let toShort := fun (B : Fin n → List (Fin a))
      (hB : B ∈ Fintype.piFinset (fun _ : Fin n => wordFamily w s)) (h : f B ≠ 0) =>
    fun j => (⟨B j, Finset.mem_filter.mpr ⟨(Fintype.mem_piFinset.mp hB) j, hne B h j⟩⟩ : G4.ShortWord w s)
  change (∑ B ∈ Fintype.piFinset (fun _ : Fin n => wordFamily w s), f B) = ∑ B, g B
  apply Finset.sum_bij_ne_zero toShort
  · intro B hB h
    exact Finset.mem_univ _
  · intro B hB h B' hB' h' he
    funext j
    exact congrArg Subtype.val (congrFun he j)
  · intro B _ hB
    let B' : Fin n → List (Fin a) := fun j => (B j).val
    have hb : B' ∈ Fintype.piFinset (fun _ : Fin n => wordFamily w s) :=
      Fintype.mem_piFinset.mpr (fun j => (Finset.mem_filter.mp (B j).property).1)
    have he : f B' = g B := rfl
    have hn : f B' ≠ 0 := he ▸ hB
    refine ⟨B', hb, hn, ?_⟩
    funext j
    exact Subtype.ext rfl
  · intro B hB h
    rfl

/-- Enumerating every ordered short frame preserves the volume polynomial. -/
theorem enumerated_volumePolynomial_eq {a n s : ℕ} (w : Fin a → ℕ+)
    (X : Fin a → (Fin n → ℝ) → (Fin n → ℝ)) (x : Fin n → ℝ) (r : ℝ) :
    G4.volumePolynomial (fun B : Fin n → Fin (Fintype.card (G4.ShortWord w s)) =>
      G4.frameDet (fun j => G4.shortField w X (G4.shortIndex w j)) B x)
      (fun B => ∑ i, (G4.shortWeight w (G4.shortIndex w (B i)) : ℕ)) r =
    G4.volumePolynomial (fun B : Fin n → G4.ShortWord w s => G4.frameDet (G4.shortField w X) B x)
      (fun B => ∑ i, (G4.shortWeight w (B i) : ℕ)) r := by
  classical
  let e := Fintype.equivFin (G4.ShortWord w s)
  unfold G4.volumePolynomial
  symm
  apply Fintype.sum_equiv (Equiv.arrowCongr (Equiv.refl (Fin n)) e)
  intro B
  change |G4.frameDet (G4.shortField w X) B x| * r ^ (∑ i, (G4.shortWeight w (B i) : ℕ)) =
    |G4.frameDet (fun j => G4.shortField w X (e.symm j)) (e ∘ B) x| *
      r ^ (∑ i, (G4.shortWeight w (e.symm (e (B i))) : ℕ))
  simp only [Equiv.symm_apply_apply, G4.frameDet_reindex]

end RothschildStein.Geometry
