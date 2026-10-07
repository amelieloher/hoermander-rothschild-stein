-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.AuxiliaryControl

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators ENNReal
namespace RothschildStein.Geometry

/-- Removing zero fields outside an injectively indexed subfamily preserves
controlled curves, their measurable controls, and their costs. -/
theorem isControlledCurve_restrict_zero_fields {m b n : ℕ}
    {Ω : Set (Fin n → ℝ)} {w : Fin m → ℕ+} {v : Fin b → ℕ+}
    {X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)}
    {Z : Fin b → (Fin n → ℝ) → (Fin n → ℝ)}
    (e : Fin m → Fin b) (he : Function.Injective e)
    (hw : ∀ i, v (e i) = w i) (hX : ∀ i, Z (e i) = X i)
    (hzero : ∀ j, (∀ i, e i ≠ j) → Z j = 0)
    {δ : ℝ} {γ : ℝ → (Fin n → ℝ)} (hγ : isControlledCurve Ω v Z δ γ) :
    isControlledCurve Ω w X δ γ := by
  classical
  obtain ⟨hδ, hac, hmap, a, hmeas, ha⟩ := hγ
  refine ⟨hδ, hac, hmap, fun i => a (e i), fun i => hmeas (e i), ?_⟩
  filter_upwards [ha] with t ht
  refine ⟨fun i => by simpa only [hw] using ht.1 (e i), ?_⟩
  have hsum : (∑ j : Fin b, a j t • Z j (γ t)) =
      ∑ i : Fin m, a (e i) t • X i (γ t) := by
    calc
      _ = ∑ j ∈ Finset.univ.image e, a j t • Z j (γ t) := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro j _ hj
        have hz : Z j = 0 := hzero j (by
          intro i hi
          apply hj
          exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, hi⟩)
        simp only [hz, Pi.zero_apply, smul_zero]
      _ = ∑ i : Fin m, a (e i) t • X i (γ t) := by
        rw [Finset.sum_image (fun i _ j _ hij => he hij)]
        simp only [hX]
  rw [hsum] at ht
  exact ht.2

/-- An injected subfamily with only zero fields outside it has the same
extended control distance, without a finiteness assumption. -/
theorem controlDistance_eq_of_zero_extension {m b n : ℕ}
    (Ω : Set (Fin n → ℝ)) (w : Fin m → ℕ+) (v : Fin b → ℕ+)
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (Z : Fin b → (Fin n → ℝ) → (Fin n → ℝ))
    (e : Fin m → Fin b) (he : Function.Injective e)
    (hw : ∀ i, v (e i) = w i) (hX : ∀ i, Z (e i) = X i)
    (hzero : ∀ j, (∀ i, e i ≠ j) → Z j = 0) (x y : Fin n → ℝ) :
    controlDistance Ω v Z x y = controlDistance Ω w X x y := by
  apply le_antisymm
  · exact G4.controlDistance_le_of_control_inclusion Ω w v X Z
      (fun _ _ hγ => G4.isControlledCurve_extend e he hw hX hγ) x y
  · exact G4.controlDistance_le_of_control_inclusion Ω v w Z X
      (fun _ _ hγ => isControlledCurve_restrict_zero_fields e he hw hX hzero hγ) x y

/-- BB Definition 9.4's enumeration including the empty zero bracket gives
exactly G4's nonempty short-word distance. The empty word is assigned the
positive weight `Nat.toPNat' 0`; its control contributes zero to the ODE. -/
theorem wordFamily_controlDistance_eq_auxiliaryDistance {m n s : ℕ}
    (Ω : Set (Fin n → ℝ)) (w : Fin m → ℕ+)
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)) (x y : Fin n → ℝ) :
    let e : Fin (wordFamily w s).card → List (Fin m) :=
      fun j => ((wordFamily w s).equivFin.symm j).val
    let ws : Fin (wordFamily w s).card → ℕ+ := fun j => Nat.toPNat' (wordWeight w (e j))
    controlDistance Ω ws (fun j => wordBracket X (e j)) x y =
      G4.auxiliaryDistance (s := s) Ω w X x y := by
  classical
  intro e ws
  let incl : G4.ShortWord w s → ↥(wordFamily w s) :=
    fun I => ⟨I.val, (Finset.mem_filter.mp I.property).1⟩
  let f := fun j => (wordFamily w s).equivFin (incl (G4.shortIndex w j))
  have hword : ∀ j, e (f j) = (G4.shortIndex w j).val := by
    intro j
    simp only [e, f, Equiv.symm_apply_apply, incl]
  have hf : Function.Injective f := by
    intro i j hij
    have hval := congrArg Subtype.val ((wordFamily w s).equivFin.injective hij)
    have hshort : G4.shortIndex w i = G4.shortIndex w j := Subtype.ext hval
    exact (Fintype.equivFin (G4.ShortWord w s)).symm.injective hshort
  unfold G4.auxiliaryDistance
  apply controlDistance_eq_of_zero_extension Ω _ ws _ _ f hf
  · intro i
    apply Subtype.ext
    simp only [ws, hword, G4.shortWeight]
    exact PNat.toPNat'_coe (G4.shortWord_weight_pos (G4.shortIndex w i))
  · intro i
    simp only [hword, G4.shortField]
  · intro j hj
    have hempty : e j = [] := by
      by_contra hne
      let I : G4.ShortWord w s := ⟨e j, Finset.mem_filter.mpr
        ⟨((wordFamily w s).equivFin.symm j).property, hne⟩⟩
      let i := Fintype.equivFin (G4.ShortWord w s) I
      have hi : G4.shortIndex w i = I := (Fintype.equivFin _).symm_apply_apply I
      apply hj i
      apply (wordFamily w s).equivFin.symm.injective
      apply Subtype.ext
      simp only [f, Equiv.symm_apply_apply, incl, hi, I, e]
    simp only [hempty, wordBracket]

end RothschildStein.Geometry
