-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.LiftedChart
public import RothschildStein.H1.Standing
public import RothschildStein.G2.GaugeConsequences
public import RothschildStein.G3.FiniteWords

/-!
# The lifted model satisfies the standing hypotheses of H1

The free homogeneous model `(G; Y₀, …, Y_q)` of a `LiftedChart` is an
`H1.StandingHypotheses` (BB Definitions 6.5–6.8, pp. 254–256).

* `LiftedChart.driftModel` : chart over the alphabet `Fin (q + 1)` with weights
  `if i = 0 then 2 else 1`; the H1 fields are the chart fields `Y`.
* `LiftedChart.noDriftModel` : chart over the alphabet `Fin q` with all weights one; the H1 fields
  are `Fin.cons 0 Y` (zero drift at index `0`).

The homogeneous norm is a parameter. The inversion of the chart group is `u ↦ -u`, so every norm
built by `G2.smoothNorm` is symmetric (`LiftedChart.smoothNorm_symmetric`). The dimension
hypothesis `(D) Q ≥ 3` follows from `3 ≤ n` (`LiftedChart.two_lt_homogeneousDimension`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set Hormander.Interface
namespace RothschildStein.P1

/-- Every nonempty standard word is the evaluation of a binary
bracket word (BB Def 1.17, p. 10; right-nested bracketings). -/
theorem exists_lieWord_eval_eq_wordBracket {q N : ℕ}
    (F : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ)) :
    ∀ I : List (Fin (q + 1)), I ≠ [] → ∃ t : LieWord q, LieWord.eval F t = wordBracket F I
  | [], h => absurd rfl h
  | [i], _ => ⟨.generator i, rfl⟩
  | i :: j :: I, _ => by
    obtain ⟨t, ht⟩ := exists_lieWord_eval_eq_wordBracket F (j :: I) (List.cons_ne_nil _ _)
    exact ⟨.bracket (.generator i) t, by
      change VectorField.lieBracket ℝ (F i) (LieWord.eval F t) = _
      rw [ht]
      rfl⟩

/-- If the standard basis vectors are values at the origin of nonempty
word brackets, then the origin values of all bracket words span the whole space (Hörmander's condition at
the origin). -/
theorem span_lieWord_origin_eq_top {q N : ℕ}
    (F : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ))
    (hF : ∀ j : Fin N, ∃ I : List (Fin (q + 1)), I ≠ [] ∧ wordBracket F I 0 = Pi.single j 1) :
    Submodule.span ℝ (Set.range (fun t : LieWord q => LieWord.eval F t 0)) = ⊤ := by
  rw [eq_top_iff, ← (Pi.basisFun ℝ (Fin N)).span_eq]
  apply Submodule.span_le.mpr
  rintro _ ⟨j, rfl⟩
  obtain ⟨I, hI, hIj⟩ := hF j
  obtain ⟨t, ht⟩ := exists_lieWord_eval_eq_wordBracket F I hI
  apply Submodule.subset_span
  exact ⟨t, by
    change LieWord.eval F t 0 = _
    rw [ht, hIj, Pi.basisFun_apply]⟩

/-- Brackets in the zero-drift extension `Fin.cons 0 Y` of words
without the drift letter are the brackets of `Y`. -/
theorem wordBracket_cons_zero_map_succ {q N : ℕ}
    (Y : Fin q → (Fin N → ℝ) → (Fin N → ℝ)) :
    ∀ I : List (Fin q),
      wordBracket (Fin.cons (0 : (Fin N → ℝ) → (Fin N → ℝ)) Y :
        Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ)) (I.map Fin.succ) = wordBracket Y I
  | [] => rfl
  | [i] => rfl
  | i :: j :: I => by
    have ih := wordBracket_cons_zero_map_succ Y (j :: I)
    change VectorField.lieBracket ℝ
      ((Fin.cons (0 : (Fin N → ℝ) → (Fin N → ℝ)) Y :
        Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ)) i.succ)
      (wordBracket (Fin.cons (0 : (Fin N → ℝ) → (Fin N → ℝ)) Y :
        Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ)) ((j :: I).map Fin.succ)) =
      VectorField.lieBracket ℝ (Y i) (wordBracket Y (j :: I))
    rw [ih, Fin.cons_succ]

namespace LiftedChart

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  (C : LiftedChart w s Ω hΩ X x₀ m)

/-- The chart group has inversion `u ↦ -u` (BB p. 98). -/
theorem hasNegInverse : G2.HasNegInverse C.G := fun u => C.inv_eq_neg u

/-- The corrected smooth homogeneous norm of the chart group is
symmetric (BB Prop 3.10, pp. 100–101). -/
theorem smoothNorm_symmetric : (G2.smoothNorm C.G).Symmetric :=
  G2.smoothNorm_symmetric C.G C.hasNegInverse

/-- The model fields are the prescribed left invariant fields
(BB (3.9), p. 108). -/
theorem model_field_eq_leftField (i : Fin k) : C.Y i = G2.leftField C.G (C.v i) :=
  funext (C.model_field_eq i)

/-- The value of a model field at the origin is its generator
vector. -/
theorem model_field_zero (i : Fin k) : C.Y i 0 = C.v i := by
  rw [C.model_field_eq_leftField i, G2.leftField_zero]

/-- The model fields are left invariant in the sense of G2. -/
theorem isLeftInvariantField (i : Fin k) : G2.IsLeftInvariantField C.G (C.Y i) :=
  fun u z => C.model_field_invariant i u z

/-- Homogeneity of the model field `Y i` of degree `w i` in the
tangent-vector form of G2 (BB Prop 3.23, p. 107). -/
theorem isHomogeneousField (i : Fin k) :
    G2.IsHomogeneousField C.G (C.Y i) ((w i : ℕ) : ℝ) := by
  intro t ht x
  rw [C.model_field_homogeneous i t ht x, smul_smul]
  have h1 : t ^ ((w i : ℕ) : ℝ) * t ^ (-((w i : ℕ) : ℤ)) = 1 := by
    rw [Real.rpow_natCast, zpow_neg, zpow_natCast]
    exact mul_inv_cancel₀ (pow_ne_zero _ ht.ne')
  rw [h1, one_smul]

include C in
/-- A word of the chart's bracket basis has weight at least one, so the
step is at least one. -/
theorem one_le_step : 1 ≤ s := by
  obtain ⟨hne, hle, -⟩ := C.basis_weight ⟨0, C.G.dimension_pos⟩
  have h1 := G3.length_le_weight w (C.B ⟨0, C.G.dimension_pos⟩)
  have h2 := List.length_pos_of_ne_nil hne
  omega

/-- A retained generator letter gives a nonzero model field: if `Y i`
vanished then its generator vector, hence the formal bracket `[i]`, would vanish. -/
theorem model_field_ne_zero (i : Fin k) (hi : (w i : ℕ) ≤ s) : C.Y i ≠ 0 := by
  intro h0
  have hv : C.v i = 0 := by rw [← C.model_field_zero i, h0]; rfl
  have hgen := C.generator_coords i
  rw [hv] at hgen
  simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero] at hgen
  have hJ : (0 : ℝ) = formalBracket [i] [i] :=
    congrFun hgen (G3.boundedWord w [i] (by simpa [wordWeight] using hi))
  simp [formalBracket] at hJ

/-- `n + m ≤ Q`: every coordinate weight is at least one. -/
theorem card_le_homogeneousDimension : n + m ≤ C.G.homogeneousDimension := by
  calc n + m = ∑ _j : Fin (n + m), 1 := by simp
    _ ≤ ∑ j, C.G.weight j := Finset.sum_le_sum fun j _ => C.G.weight_pos j

/-- The dimension condition `n ≥ 3` gives `Q ≥ 3`. -/
theorem three_le_homogeneousDimension (hn : 3 ≤ n) : 3 ≤ C.G.homogeneousDimension :=
  le_trans (by omega) C.card_le_homogeneousDimension

/-- The dimension condition `3 ≤ n` gives `Q > 2` for the chart group (after the padding that
reduces to `n ≥ 3`). -/
theorem two_lt_homogeneousDimension (hn : 3 ≤ n) :
    (2 : ℝ) < (C.G.homogeneousDimension : ℝ) :=
  (H1.dimension_gt_two_iff C.G).mpr (C.three_le_homogeneousDimension hn)

end LiftedChart

section Drift

variable {n q s m : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  (C : LiftedChart (fun i : Fin (q + 1) => if i = 0 then (2 : ℕ+) else 1) s Ω hΩ X x₀ m)

/-- The drift model of a lifted chart satisfies `H1.StandingHypotheses`: left-invariant fields,
`Y₀` two-homogeneous and the others
one-homogeneous, a nonzero horizontal field (this uses `0 < q`), and Hörmander's condition at the
origin, from `model_basis_origin` (BB Defs 6.5–6.8, pp. 254–256). -/
def LiftedChart.driftModel (hq : 0 < q) (ν : G2.HomogeneousNorm C.G) :
    H1.StandingHypotheses C.G q where
  q_pos := hq
  norm := ν
  fields := C.Y
  invariant := C.isLeftInvariantField
  homogeneous := fun i => by
    by_cases hi : i = 0 <;> simpa [hi] using C.isHomogeneousField i
  horizontal_nonzero := ⟨⟨0, hq⟩, C.model_field_ne_zero _ (by
    simpa using C.one_le_step)⟩
  span_origin := span_lieWord_origin_eq_top C.Y fun j =>
    ⟨C.B j, (C.basis_weight j).1, C.model_basis_origin j⟩

/-- The fields of the drift model are the chart fields. -/
@[simp] theorem LiftedChart.driftModel_fields (hq : 0 < q) (ν : G2.HomogeneousNorm C.G) :
    (C.driftModel hq ν).fields = C.Y := rfl

/-- The norm of the drift model is the one given. -/
@[simp] theorem LiftedChart.driftModel_norm (hq : 0 < q) (ν : G2.HomogeneousNorm C.G) :
    (C.driftModel hq ν).norm = ν := rfl

end Drift

section NoDrift

variable {n q s m : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  (C : LiftedChart (fun _ : Fin q => (1 : ℕ+)) s Ω hΩ X x₀ m)

/-- The no-drift model of a lifted chart satisfies `H1.StandingHypotheses` with zero drift
`Y₀ = 0`: the fields are `Fin.cons 0 Y`
(BB Defs 6.5–6.8, pp. 254–256). -/
def LiftedChart.noDriftModel (hq : 0 < q) (ν : G2.HomogeneousNorm C.G) :
    H1.StandingHypotheses C.G q where
  q_pos := hq
  norm := ν
  fields := (Fin.cons (0 : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ)) C.Y :
    Fin (q + 1) → (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ))
  invariant := fun i => by
    refine Fin.cases ?_ (fun j => ?_) i
    · intro u z
      simp
    · simpa using C.isLeftInvariantField j
  homogeneous := fun i => by
    refine Fin.cases ?_ (fun j => ?_) i
    · intro t ht x
      simp
    · simpa using C.isHomogeneousField j
  horizontal_nonzero := ⟨⟨0, hq⟩, C.model_field_ne_zero _ (by simpa using C.one_le_step)⟩
  span_origin := span_lieWord_origin_eq_top _ fun j =>
    ⟨(C.B j).map Fin.succ, by simpa using (C.basis_weight j).1, by
      rw [wordBracket_cons_zero_map_succ]
      exact C.model_basis_origin j⟩

/-- The fields of the no-drift model are `Fin.cons 0 Y`. -/
@[simp] theorem LiftedChart.noDriftModel_fields (hq : 0 < q) (ν : G2.HomogeneousNorm C.G) :
    (C.noDriftModel hq ν).fields =
      (Fin.cons (0 : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ)) C.Y :
        Fin (q + 1) → (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ)) := rfl

/-- The drift field of the no-drift model is zero. -/
@[simp] theorem LiftedChart.noDriftModel_fields_zero (hq : 0 < q)
    (ν : G2.HomogeneousNorm C.G) : (C.noDriftModel hq ν).fields 0 = 0 := rfl

/-- The horizontal fields of the no-drift model are the chart fields. -/
@[simp] theorem LiftedChart.noDriftModel_fields_succ (hq : 0 < q) (ν : G2.HomogeneousNorm C.G)
    (i : Fin q) : (C.noDriftModel hq ν).fields i.succ = C.Y i := rfl

/-- The norm of the no-drift model is the one given. -/
@[simp] theorem LiftedChart.noDriftModel_norm (hq : 0 < q) (ν : G2.HomogeneousNorm C.G) :
    (C.noDriftModel hq ν).norm = ν := rfl

end NoDrift

end RothschildStein.P1
