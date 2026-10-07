-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Group.Measure
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

@[expose] public section
noncomputable section
namespace RothschildStein.G2
open MeasureTheory Function

/-- Each coordinate differs from its signed diagonal part by a function of
strictly earlier coordinates, as in BB Theorem 3.6(d), p. 96. -/
def IsTriangular {n : ℕ} (T : (Fin n → ℝ) → Fin n → ℝ) (ε : Fin n → ℝ) : Prop :=
  ∀ k x y, (∀ j, j < k → x j = y j) → T x k - ε k * x k = T y k - ε k * y k

private def splitLast (n : ℕ) : (Fin (n + 1) → ℝ) ≃ᵐ (Fin n → ℝ) × ℝ :=
  (MeasurableEquiv.piFinSuccAbove (fun _ => ℝ) (Fin.last n)).trans
    MeasurableEquiv.prodComm

private theorem splitLast_apply (n : ℕ) (x : Fin (n + 1) → ℝ) :
    splitLast n x = (Fin.init x, x (Fin.last n)) := by
  simp [splitLast, MeasurableEquiv.piFinSuccAbove, MeasurableEquiv.prodComm]

private theorem splitLast_symm_apply (n : ℕ) (p : (Fin n → ℝ) × ℝ) :
    (splitLast n).symm p = Fin.snoc p.1 p.2 := by
  ext j
  cases j using Fin.lastCases <;> simp [splitLast, MeasurableEquiv.piFinSuccAbove, MeasurableEquiv.prodComm]

private theorem splitLast_preserving (n : ℕ) : MeasurePreserving (splitLast n) := by
  rw [Measure.volume_eq_prod]
  exact MeasureTheory.Measure.measurePreserving_swap.comp
    (volume_preserving_piFinSuccAbove (fun _ => ℝ) (Fin.last n))

private theorem measurable_snoc_zero (n : ℕ) :
    Measurable (fun x : Fin n → ℝ => Fin.snoc (α := fun _ : Fin (n + 1) => ℝ) x (0 : ℝ)) := by
  have h : Measurable (fun x : Fin n → ℝ => (splitLast n).symm (x, 0)) :=
    (splitLast n).symm.measurable.comp (measurable_id.prodMk measurable_const)
  simpa only [splitLast_symm_apply] using h

private theorem signed_translate_preserving {ε : ℝ} (hε : ε = 1 ∨ ε = -1) (c : ℝ) :
    MeasurePreserving (fun t : ℝ => ε * t + c) := by
  rcases hε with rfl | rfl
  · simpa using measurePreserving_add_right (volume : Measure ℝ) c
  · simpa only [Function.comp_def, neg_one_mul] using (measurePreserving_add_right (volume : Measure ℝ) c).comp
      (Measure.measurePreserving_neg (volume : Measure ℝ))

/-- A Borel triangular map with diagonal entries ±1 is a measure-preserving bijection (BB Theorem 3.6(d), p. 96). -/
theorem triangular_measurePreserving_bijective {n : ℕ}
    (T : (Fin n → ℝ) → Fin n → ℝ) (ε : Fin n → ℝ)
    (hT : Measurable T) (hε : ∀ k, ε k = 1 ∨ ε k = -1) (htri : IsTriangular T ε) :
    MeasurePreserving T ∧ Bijective T := by
  induction n with
  | zero =>
    have he : T = id := by ext x k; exact Fin.elim0 k
    rw [he]
    exact ⟨MeasurePreserving.id _, Function.bijective_id⟩
  | succ n ih =>
    let f : (Fin n → ℝ) → Fin n → ℝ := fun x => Fin.init (T (Fin.snoc x 0))
    let g : (Fin n → ℝ) → ℝ := fun x => T (Fin.snoc x 0) (Fin.last n)
    have hf : Measurable f := measurable_pi_iff.mpr fun k =>
      (measurable_pi_apply k.castSucc).comp (hT.comp (measurable_snoc_zero n))
    have hg : Measurable g :=
      (measurable_pi_apply (Fin.last n)).comp (hT.comp (measurable_snoc_zero n))
    have hftri : IsTriangular f (fun k => ε k.castSucc) := by
      intro k x y hxy
      have h := htri k.castSucc (Fin.snoc x 0) (Fin.snoc y 0) (by
        intro j hj
        have hjn : j.val < n := lt_of_lt_of_le hj (Nat.le_of_lt k.isLt)
        let j' : Fin n := ⟨j.val, hjn⟩
        have he : j = j'.castSucc := rfl
        rw [he]
        simpa only [Fin.snoc_castSucc] using hxy j' hj)
      simpa only [f, Fin.init, Fin.snoc_castSucc] using h
    obtain ⟨hfmp, hfbij⟩ := ih f (fun k => ε k.castSucc) hf (fun k => hε k.castSucc) hftri
    let H : (Fin n → ℝ) × ℝ → (Fin n → ℝ) × ℝ :=
      fun p => (f p.1, ε (Fin.last n) * p.2 + g p.1)
    have hH : MeasurePreserving H := by
      rw [Measure.volume_eq_prod]
      apply hfmp.skew_product (g := fun x t => ε (Fin.last n) * t + g x)
      · exact (measurable_const.mul measurable_snd).add (hg.comp measurable_fst)
      · exact Filter.Eventually.of_forall fun x =>
          (signed_translate_preserving (hε (Fin.last n)) (g x)).map_eq
    have hεne : ε (Fin.last n) ≠ 0 := by
      rcases hε (Fin.last n) with h | h <;> rw [h] <;> norm_num
    have hHbij : Bijective H := by
      constructor
      · intro p q hpq
        have hbase := hfbij.injective (congrArg Prod.fst hpq)
        have hfiber := congrArg Prod.snd hpq
        dsimp [H] at hbase hfiber
        apply Prod.ext hbase
        rw [hbase] at hfiber
        exact mul_left_cancel₀ hεne (add_right_cancel hfiber)
      · intro p
        obtain ⟨x, hx⟩ := hfbij.surjective p.1
        refine ⟨(x, (p.2 - g x) / ε (Fin.last n)), ?_⟩
        apply Prod.ext hx
        dsimp [H]
        field_simp
        ring
    have hconj : T = (splitLast n).symm ∘ H ∘ splitLast n := by
      funext x
      apply (splitLast n).injective
      simp only [Function.comp_apply, MeasurableEquiv.apply_symm_apply, splitLast_apply]
      apply Prod.ext
      · ext k
        dsimp [H, f, Fin.init]
        have h := htri k.castSucc x (Fin.snoc (Fin.init x) 0) (by
          intro j hj
          have hjn : j.val < n := lt_of_lt_of_le hj (Nat.le_of_lt k.isLt)
          let j' : Fin n := ⟨j.val, hjn⟩
          have he : j = j'.castSucc := rfl
          rw [he]
          simp [Fin.init])
        simp only [Fin.snoc_castSucc, Fin.init] at h
        exact sub_left_injective h
      · dsimp [H, g]
        have h := htri (Fin.last n) x (Fin.snoc (Fin.init x) 0) (by
          intro j hj
          let j' : Fin n := ⟨j.val, hj⟩
          have he : j = j'.castSucc := rfl
          rw [he]
          simp [Fin.init])
        simp only [Fin.snoc_last, mul_zero, sub_zero] at h
        linarith
    rw [hconj]
    exact ⟨(MeasurePreserving.symm (splitLast n) (splitLast_preserving n)).comp
      (hH.comp (splitLast_preserving n)),
      (splitLast n).symm.bijective.comp (hHbij.comp (splitLast n).bijective)⟩

end RothschildStein.G2
