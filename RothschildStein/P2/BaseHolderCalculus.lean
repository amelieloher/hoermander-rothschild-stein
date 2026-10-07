-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.HolderInterpolationLeibniz

/-!
# Bookkeeping for the base Hölder estimate

Part of the base Hölder estimate (BB pp. 577, 600-602). Small calculus used by the `BaseHolder*` modules:

* `supNormE V f = ⨆ x ∈ V, |f x|` (the pointwise supremum on a set, in `ℝ≥0∞`);
* `BoundedBy x Y c : x ≤ c Y` for a real constant `c` (additivity, monotonicity, finite sums);
* `jetENorm d α V D = ∑_{|I|_w ≤ 2} ‖D I‖_{C^α(V)}` for a drift jet `D` (the Hölder norm of
  order two computed on a weak jet) and its bound by the norms of the entries `[]`, `[l]`, `[0]`,
  `[i, l]` (`jetENorm_le`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Filter
open scoped ENNReal BigOperators
namespace RothschildStein.P2

open RothschildStein.P1

section Sup

variable {N : ℕ}

/-- The pointwise supremum `⨆_{x ∈ V} |f x|` in `ℝ≥0∞`. -/
def supNormE (V : Set (Fin N → ℝ)) (f : (Fin N → ℝ) → ℝ) : ℝ≥0∞ :=
  ⨆ x : V, ENNReal.ofReal |f x|

theorem ofReal_abs_le_supNormE {V : Set (Fin N → ℝ)} {f : (Fin N → ℝ) → ℝ} {x : Fin N → ℝ}
    (hx : x ∈ V) : ENNReal.ofReal |f x| ≤ supNormE V f :=
  le_iSup (fun y : V => ENNReal.ofReal |f y|) ⟨x, hx⟩

theorem supNormE_le_of_forall {V : Set (Fin N → ℝ)} {f : (Fin N → ℝ) → ℝ} {B : ℝ≥0∞}
    (h : ∀ x ∈ V, ENNReal.ofReal |f x| ≤ B) : supNormE V f ≤ B :=
  iSup_le fun x => h x x.2

theorem supNormE_mono {V V' : Set (Fin N → ℝ)} (h : V' ⊆ V) (f : (Fin N → ℝ) → ℝ) :
    supNormE V' f ≤ supNormE V f :=
  supNormE_le_of_forall fun _ hx => ofReal_abs_le_supNormE (h hx)

theorem supNormE_congr {V : Set (Fin N → ℝ)} {f g : (Fin N → ℝ) → ℝ} (h : EqOn f g V) :
    supNormE V f = supNormE V g := by
  unfold supNormE
  exact iSup_congr fun x => by rw [h x.2]

theorem supNormE_le_holderENorm {d : (Fin N → ℝ) → (Fin N → ℝ) → ℝ≥0∞} {α : ℝ}
    (V : Set (Fin N → ℝ)) (f : (Fin N → ℝ) → ℝ) : supNormE V f ≤ holderENorm d α V f :=
  supNormE_le_of_forall fun _ hx => RothschildStein.S.enorm_le_holderENorm d α V f hx

end Sup

section Bounded

/-- `x ≤ c Y` for a real constant `c`. -/
def BoundedBy (x Y : ℝ≥0∞) (c : ℝ) : Prop :=
  x ≤ ENNReal.ofReal c * Y

namespace BoundedBy

variable {x x' y Y Y' : ℝ≥0∞} {c c' : ℝ}

theorem mono (h : BoundedBy x Y c) (hcc : c ≤ c') : BoundedBy x Y c' :=
  h.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hcc) le_rfl)

theorem mono_left (h : BoundedBy x Y c) (hx : x' ≤ x) : BoundedBy x' Y c :=
  hx.trans h

theorem add (h : BoundedBy x Y c) (h' : BoundedBy y Y c') (hc : 0 ≤ c) (hc' : 0 ≤ c') :
    BoundedBy (x + y) Y (c + c') := by
  unfold BoundedBy at *
  calc x + y ≤ ENNReal.ofReal c * Y + ENNReal.ofReal c' * Y := add_le_add h h'
    _ = ENNReal.ofReal (c + c') * Y := by rw [ENNReal.ofReal_add hc hc', add_mul]

theorem const_mul (h : BoundedBy x Y c) {k : ℝ} (hk : 0 ≤ k) : BoundedBy (ENNReal.ofReal k * x) Y (k * c) := by
  unfold BoundedBy at *
  calc ENNReal.ofReal k * x ≤ ENNReal.ofReal k * (ENNReal.ofReal c * Y) := mul_le_mul' le_rfl h
    _ = ENNReal.ofReal (k * c) * Y := by rw [← mul_assoc, ← ENNReal.ofReal_mul hk]

theorem of_le (h : x ≤ Y) : BoundedBy x Y 1 := by
  unfold BoundedBy
  rw [ENNReal.ofReal_one, one_mul]
  exact h

theorem zero (Y : ℝ≥0∞) : BoundedBy 0 Y 0 := by
  unfold BoundedBy
  exact bot_le

theorem sum {ι : Type*} (s : Finset ι) {f : ι → ℝ≥0∞} {c : ι → ℝ}
    (h : ∀ i ∈ s, BoundedBy (f i) Y (c i)) (hc : ∀ i ∈ s, 0 ≤ c i) :
    BoundedBy (∑ i ∈ s, f i) Y (∑ i ∈ s, c i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using zero Y
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
        (fun i hi => hc i (Finset.mem_insert_of_mem hi)))
      (hc a (Finset.mem_insert_self a s))
      (Finset.sum_nonneg fun i hi => hc i (Finset.mem_insert_of_mem hi))

theorem sum_const {ι : Type*} (s : Finset ι) {f : ι → ℝ≥0∞} {c : ℝ}
    (h : ∀ i ∈ s, BoundedBy (f i) Y c) (hc : 0 ≤ c) :
    BoundedBy (∑ i ∈ s, f i) Y (s.card * c) := by
  have := sum s h (fun _ _ => hc)
  rwa [Finset.sum_const, nsmul_eq_mul] at this

theorem of_const_mul_le {k : ℝ} (hk : 0 ≤ k) {x : ℝ≥0∞} (h : x ≤ Y) :
    BoundedBy (ENNReal.ofReal k * x) Y k := by
  have := (of_le h).const_mul hk
  rwa [mul_one] at this

end BoundedBy

end Bounded

section Jet

variable {N q : ℕ}

/-- The order-two Hölder norm computed on a drift jet:
`∑_{|I|_w ≤ 2} ‖D I‖_{C^α(V)}`. For a function with Hölder weak jet `D` on an open `V` this is
`holderXENorm` (`holderXENorm_eq_jetENorm`). -/
def jetENorm (d : (Fin N → ℝ) → (Fin N → ℝ) → ℝ≥0∞) (α : ℝ) (V : Set (Fin N → ℝ))
    (D : List (Fin (q + 1)) → (Fin N → ℝ) → ℝ) : ℝ≥0∞ :=
  ∑ I ∈ wordFamily driftWeight 2, holderENorm d α V (D I)

theorem jetENorm_mono_set {d : (Fin N → ℝ) → (Fin N → ℝ) → ℝ≥0∞} {α : ℝ}
    {V V' : Set (Fin N → ℝ)} (h : V' ⊆ V) (D : List (Fin (q + 1)) → (Fin N → ℝ) → ℝ) :
    jetENorm d α V' D ≤ jetENorm d α V D :=
  Finset.sum_le_sum fun _ _ => RothschildStein.S.holderENorm_mono d α V _ h

theorem jetENorm_congr {d : (Fin N → ℝ) → (Fin N → ℝ) → ℝ≥0∞} {α : ℝ} {V : Set (Fin N → ℝ)}
    {D D' : List (Fin (q + 1)) → (Fin N → ℝ) → ℝ}
    (h : ∀ I ∈ wordFamily driftWeight 2, EqOn (D I) (D' I) V) :
    jetENorm d α V D = jetENorm d α V D' :=
  Finset.sum_congr rfl fun I hI => RothschildStein.S.holderENorm_congr d α V _ (h I hI)

/-- The order-two norm of a drift jet is at most the norms of the entries `[]`, `[l+1]`, `[0]`
and `[i+1, l+1]`. -/
theorem jetENorm_le (d : (Fin N → ℝ) → (Fin N → ℝ) → ℝ≥0∞) (α : ℝ) (V : Set (Fin N → ℝ))
    (D : List (Fin (q + 1)) → (Fin N → ℝ) → ℝ) :
    jetENorm d α V D ≤ holderENorm d α V (D []) + holderENorm d α V (D [0]) +
      ∑ l : Fin q, holderENorm d α V (D [l.succ]) +
        ∑ i : Fin q, ∑ l : Fin q, holderENorm d α V (D [i.succ, l.succ]) := by
  classical
  set f : List (Fin (q + 1)) → ℝ≥0∞ := fun I => holderENorm d α V (D I) with hf
  have hsub : wordFamily driftWeight 2 ⊆
      (({[]} : Finset (List (Fin (q + 1)))) ∪ (Finset.univ.image fun i : Fin (q + 1) => [i])) ∪
        (Finset.univ.image fun p : Fin q × Fin q => [p.1.succ, p.2.succ]) := by
    intro K hK
    rcases wordFamily_drift_cases hK with rfl | ⟨i, rfl⟩ | ⟨j, i, rfl⟩
    · simp
    · simp
    · simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_image, Finset.mem_univ,
        true_and]
      exact Or.inr ⟨(j, i), rfl⟩
  have hinj1 : Function.Injective (fun i : Fin (q + 1) => ([i] : List (Fin (q + 1)))) := by
    intro i j h
    simpa using h
  have hinj2 : Function.Injective
      (fun p : Fin q × Fin q => ([p.1.succ, p.2.succ] : List (Fin (q + 1)))) := by
    intro p p' h
    simp only [List.cons.injEq, Fin.succ_inj, and_true] at h
    exact Prod.ext h.1 h.2
  have hd1 : Disjoint ({[]} : Finset (List (Fin (q + 1))))
      (Finset.univ.image fun i : Fin (q + 1) => [i]) := by
    rw [Finset.disjoint_left]
    intro K hK hK'
    simp only [Finset.mem_singleton] at hK
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hK'
    obtain ⟨i, rfl⟩ := hK'
    simp at hK
  have hd2 : Disjoint (({[]} : Finset (List (Fin (q + 1)))) ∪
      (Finset.univ.image fun i : Fin (q + 1) => [i]))
      (Finset.univ.image fun p : Fin q × Fin q => [p.1.succ, p.2.succ]) := by
    rw [Finset.disjoint_left]
    intro K hK hK'
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hK'
    obtain ⟨p, rfl⟩ := hK'
    simp at hK
  unfold jetENorm
  calc ∑ I ∈ wordFamily driftWeight 2, holderENorm d α V (D I)
      ≤ ∑ I ∈ (({[]} : Finset (List (Fin (q + 1)))) ∪
          (Finset.univ.image fun i : Fin (q + 1) => [i])) ∪
          (Finset.univ.image fun p : Fin q × Fin q => [p.1.succ, p.2.succ]), f I :=
        Finset.sum_le_sum_of_subset hsub
    _ = f [] + ∑ i : Fin (q + 1), f [i] + ∑ p : Fin q × Fin q, f [p.1.succ, p.2.succ] := by
        rw [Finset.sum_union hd2, Finset.sum_union hd1, Finset.sum_singleton,
          Finset.sum_image (fun i _ j _ h => hinj1 h), Finset.sum_image (fun p _ p' _ h => hinj2 h)]
    _ = _ := by
        rw [Fin.sum_univ_succ, Fintype.sum_prod_type]
        simp only [hf]
        ring

end Jet

end RothschildStein.P2
