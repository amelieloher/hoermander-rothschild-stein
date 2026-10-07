-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.ShortFields
public import RothschildStein.G1.ControlEMetric

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter MeasureTheory
open scoped BigOperators ENNReal

namespace RothschildStein.G4

/-- Inserting generator controls into a larger finite family preserves
actual controlled curves and measurable controls (BB Remark 9.5, p. 402). -/
theorem isControlledCurve_extend {m k n : ℕ} {Ω : Set (Fin n → ℝ)}
    {w : Fin m → ℕ+} {v : Fin k → ℕ+}
    {X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)}
    {Z : Fin k → (Fin n → ℝ) → (Fin n → ℝ)}
    (e : Fin m → Fin k) (he : Function.Injective e)
    (hw : ∀ i, v (e i) = w i) (hX : ∀ i, Z (e i) = X i)
    {δ : ℝ} {γ : ℝ → (Fin n → ℝ)} (hγ : isControlledCurve Ω w X δ γ) :
    isControlledCurve Ω v Z δ γ := by
  classical
  obtain ⟨hδ, hac, hmap, a, hmeas, ha⟩ := hγ
  let b := fun j t => ∑ i : Fin m, if e i = j then a i t else 0
  have hb : ∀ i t, b (e i) t = a i t := by
    intro i t
    simp only [b, he.eq_iff]
    simp
  refine ⟨hδ, hac, hmap, b, ?_, ?_⟩
  · intro j
    have hm := Finset.aemeasurable_sum Finset.univ (μ := volume.restrict (Icc (0 : ℝ) 1))
      (f := fun i t => if e i = j then a i t else (0 : ℝ)) (fun i hi => ?_)
    · convert hm using 1
      funext t
      simp only [b, Finset.sum_apply]
    by_cases h : e i = j
    · simpa only [ite_eq_left h] using hmeas i
    · simp only [ite_eq_right h]
      exact aemeasurable_const
  · filter_upwards [ha] with t ht
    refine ⟨fun j => ?_, ?_⟩
    · by_cases hj : ∃ i, e i = j
      · obtain ⟨i, rfl⟩ := hj
        simpa only [hb, hw] using ht.1 i
      · have hzero : b j t = 0 := by
          apply Finset.sum_eq_zero
          intro i hi
          simp only [ite_eq_right (fun h => hj ⟨i, h⟩)]
        rw [hzero, abs_zero]
        positivity
    · have heq : (∑ j : Fin k, b j t • Z j (γ t)) = ∑ i : Fin m, a i t • X i (γ t) := by
        simp only [b, Finset.sum_smul]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i hi
        simp [ite_smul, hX i]
      rw [heq]
      exact ht.2

/-- Inclusion of the actual curve classes reverses the distance
inequality, including infinite values (BB Remark 9.5, p. 402). -/
theorem controlDistance_le_of_control_inclusion {m k n : ℕ}
    (Ω : Set (Fin n → ℝ)) (w : Fin m → ℕ+) (v : Fin k → ℕ+)
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (Z : Fin k → (Fin n → ℝ) → (Fin n → ℝ))
    (hcurve : ∀ δ γ, isControlledCurve Ω w X δ γ → isControlledCurve Ω v Z δ γ)
    (x y : Fin n → ℝ) : controlDistance Ω v Z x y ≤ controlDistance Ω w X x y := by
  unfold controlDistance
  apply sInf_le_sInf
  rintro r ⟨δ, rfl, γ, hγ, hzero, hone⟩
  exact ⟨δ, rfl, γ, hcurve δ γ hγ, hzero, hone⟩

/-- Enumeration of short words for the `Fin`-indexed interface. -/
def shortIndex {m s : ℕ} (w : Fin m → ℕ+)
    (j : Fin (Fintype.card (ShortWord w s))) : ShortWord w s :=
  (Fintype.equivFin (ShortWord w s)).symm j

/-- The auxiliary distance uses the original ambient domain and all
nonempty short brackets with their weighted control costs (BB Def 9.4, p. 402). -/
def auxiliaryDistance {m n s : ℕ} (Ω : Set (Fin n → ℝ)) (w : Fin m → ℕ+)
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)) (x y : Fin n → ℝ) : ℝ≥0∞ :=
  controlDistance Ω (fun j => shortWeight w (shortIndex (s := s) w j))
    (fun j => shortField w X (shortIndex (s := s) w j)) x y

/-- Auxiliary control distance is no greater than the original one,
provided the cutoff includes every generator weight (BB Remark 9.5, p. 402). -/
theorem auxiliaryDistance_le {m n s : ℕ} (Ω : Set (Fin n → ℝ)) (w : Fin m → ℕ+)
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)) (hs : ∀ i, (w i : ℕ) ≤ s)
    (x y : Fin n → ℝ) : auxiliaryDistance (s := s) Ω w X x y ≤ controlDistance Ω w X x y := by
  let singleton : Fin m → ShortWord w s := fun i => ⟨[i],
    (mem_shortWordFamily_iff w [i]).mpr ⟨by simp, by simpa [wordWeight] using hs i⟩⟩
  let e := fun i => Fintype.equivFin (ShortWord w s) (singleton i)
  have he : Function.Injective e := by
    intro i j hij
    have hlist := congrArg Subtype.val ((Fintype.equivFin _).injective hij)
    simpa only [singleton, List.cons.injEq, and_true] using hlist
  have hindex : ∀ i, shortIndex w (e i) = singleton i :=
    fun i => (Fintype.equivFin _).symm_apply_apply _
  apply controlDistance_le_of_control_inclusion
  intro δ γ hγ
  apply isControlledCurve_extend e he _ _ hγ
  · intro i
    apply Subtype.ext
    simp [hindex, singleton, shortWeight, wordWeight]
    rfl
  · intro i
    simp [hindex, singleton, shortField, wordBracket]

end RothschildStein.G4
