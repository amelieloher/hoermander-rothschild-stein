-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.L1.JetLeibnizFormula
public import RothschildStein.L1.WeightedJetNegation
public import RothschildStein.L1.PartialJetSums
public import RothschildStein.P1.WeightedTaylorJetLoss
public import RothschildStein.P1.SmoothFieldHomogeneity
public import RothschildStein.G2.Algebra

/-!
# Parametrix error types: integer-order weighted jet calculus

`JetVan ω o f` says that every ordered coordinate jet `rsPartial I f 0` of weight `∑ ω I < o` vanishes at
the origin (`o : ℤ`; for `o ≤ 0` the condition is empty). These full-order weighted jet classes are
closed under sums (`JetVan.add`, `JetVan.sum`) on a smooth open domain, under products with
added orders (`JetVan.mul`, the ordered Leibniz formula `L1.rsPartial_mul_eq_leibniz`), and a coordinate
derivative lowers the order by its weight (`JetVan.coordPartial`). A globally smooth function homogeneous of
integer degree `β` has order `β` (`JetVan.of_homogeneous`): its jets of weight `< β` are homogeneous of
positive degree and continuous at the origin.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set TopologicalSpace
namespace RothschildStein.P1

variable {N : ℕ}

/-- Weighted jet vanishing of integer order: every ordered coordinate jet of
weight `< o` vanishes at the origin. -/
def JetVan (ω : Fin N → ℕ) (o : ℤ) (f : (Fin N → ℝ) → ℝ) : Prop :=
  ∀ I : List (Fin N), (((I.map ω).sum : ℕ) : ℤ) < o → rsPartial I f 0 = 0

namespace JetVan

variable {ω : Fin N → ℕ} {o o' a b : ℤ} {f g : (Fin N → ℝ) → ℝ}

/-- Lowering the order. -/
theorem mono (h : o' ≤ o) (hf : JetVan ω o f) : JetVan ω o' f :=
  fun I hI => hf I (lt_of_lt_of_le hI h)

/-- Orders are preserved by sums on a smooth open domain containing the origin. -/
theorem add (Ω : Opens (Fin N → ℝ)) (h0 : (0 : Fin N → ℝ) ∈ Ω)
    (hfs : ContDiffOn ℝ (⊤ : ℕ∞) f Ω) (hgs : ContDiffOn ℝ (⊤ : ℕ∞) g Ω)
    (hf : JetVan ω o f) (hg : JetVan ω o g) : JetVan ω o (fun u => f u + g u) := by
  intro I hI
  rw [L1.rsPartial_add_on Ω f g hfs hgs I h0, hf I hI, hg I hI, add_zero]

/-- Orders are preserved by negation. -/
theorem neg (hf : JetVan ω o f) : JetVan ω o (fun u => -f u) := by
  intro I hI
  rw [L1.rsPartial_neg]
  change -rsPartial I f 0 = 0
  rw [hf I hI, neg_zero]

/-- Orders are preserved by finite sums on a smooth open domain containing the origin. -/
theorem sum {ι : Type*} (T : Finset ι) (F : ι → (Fin N → ℝ) → ℝ) (Ω : Opens (Fin N → ℝ))
    (h0 : (0 : Fin N → ℝ) ∈ Ω) (hs : ∀ i ∈ T, ContDiffOn ℝ (⊤ : ℕ∞) (F i) Ω)
    (hF : ∀ i ∈ T, JetVan ω o (F i)) : JetVan ω o (fun u => ∑ i ∈ T, F i u) := by
  intro I hI
  rw [L1.rsPartial_finset_sum_on Ω T F hs I h0]
  exact Finset.sum_eq_zero fun i hi => hF i hi I hI

/-- Orders add under products (ordered Leibniz formula). -/
theorem mul (Ω : Opens (Fin N → ℝ)) (h0 : (0 : Fin N → ℝ) ∈ Ω)
    (hfs : ContDiffOn ℝ (⊤ : ℕ∞) f Ω) (hgs : ContDiffOn ℝ (⊤ : ℕ∞) g Ω)
    (hf : JetVan ω a f) (hg : JetVan ω b g) : JetVan ω (a + b) (fun u => f u * g u) := by
  intro J hJ
  rw [L1.rsPartial_mul_eq_leibniz Ω f g hfs hgs J 0 h0]
  apply List.sum_eq_zero
  intro v hv
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hv
  obtain ⟨-, hwq⟩ := L1.jetLeibnizPartitions_order_weight ω J q hq
  have hz : (((q.1.map ω).sum : ℕ) : ℤ) + (((q.2.map ω).sum : ℕ) : ℤ) =
      (((J.map ω).sum : ℕ) : ℤ) := by exact_mod_cast hwq
  by_cases hwa : (((q.1.map ω).sum : ℕ) : ℤ) < a
  · rw [hf q.1 hwa, zero_mul]
  · rw [hg q.2 (by omega), mul_zero]

/-- A coordinate derivative lowers the order by the weight of the coordinate. -/
theorem coordPartial (j : Fin N) (hf : JetVan ω a f) :
    JetVan ω (a - (ω j : ℤ)) (fun u => fderiv ℝ f u (Pi.single j 1)) := by
  intro I hI
  change rsPartial I (rsPartial [j] f) 0 = 0
  rw [rsPartial_concat]
  apply hf
  simp only [List.map_append, List.sum_append, List.map_singleton, List.sum_singleton,
    Nat.cast_add]
  omega

end JetVan

/-- The ordered coordinate jets of a globally smooth function homogeneous of degree `β` are
homogeneous of degree `β` minus their weight, at every point including the origin. -/
theorem rsPartial_global_homogeneous (G : HomogeneousGroup N) {f : (Fin N → ℝ) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) {β : ℝ}
    (hhom : ∀ t : ℝ, 0 < t → ∀ x, f (G.dilate t x) = t ^ β * f x) (J : List (Fin N)) :
    ∀ t : ℝ, 0 < t → ∀ x, rsPartial J f (G.dilate t x) =
      t ^ (β - (((J.map G.weight).sum : ℕ) : ℝ)) * rsPartial J f x := by
  induction J with
  | nil =>
    intro t ht x
    simpa [rsPartial] using hhom t ht x
  | cons j J ih =>
    intro t ht x
    have h := coordinatePartial_global_homogeneous G j (rsPartial_contDiff J hf) ih ht x
    change fderiv ℝ (rsPartial J f) (G.dilate t x) (Pi.single j 1) =
      t ^ (β - (((j :: J).map G.weight).sum : ℕ)) * fderiv ℝ (rsPartial J f) x (Pi.single j 1)
    rw [h]
    congr 2
    simp only [List.map_cons, List.sum_cons, Nat.cast_add]
    ring

/-- A globally smooth function homogeneous of integer degree `β` has order `β`: its jets of weight
`< β` are homogeneous of positive degree, so they vanish at the origin. -/
theorem JetVan.of_homogeneous (G : HomogeneousGroup N) {f : (Fin N → ℝ) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) {β : ℤ}
    (hhom : ∀ t : ℝ, 0 < t → ∀ x, f (G.dilate t x) = t ^ (β : ℝ) * f x) :
    JetVan G.weight β f := by
  intro I hI
  have h := rsPartial_global_homogeneous G hf hhom I 2 (by norm_num) 0
  rw [G2.dilate_zero] at h
  have hlt : (((I.map G.weight).sum : ℕ) : ℝ) < (β : ℝ) := by
    have hI' : (((I.map G.weight).sum : ℕ) : ℤ) < β := hI
    simpa only [Int.cast_natCast] using (Int.cast_lt (R := ℝ)).mpr hI'
  have hr : (1 : ℝ) < 2 ^ ((β : ℝ) - (((I.map G.weight).sum : ℕ) : ℝ)) :=
    Real.one_lt_rpow (by norm_num) (by linarith)
  have h2 : (2 ^ ((β : ℝ) - (((I.map G.weight).sum : ℕ) : ℝ)) - 1) * rsPartial I f 0 = 0 := by
    linarith
  rcases mul_eq_zero.mp h2 with h3 | h3
  · linarith
  · exact h3

end RothschildStein.P1
