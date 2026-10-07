-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.C.Assembly.WordsBridge
public import Hormander.C.SobolevNorm

@[expose] public section

noncomputable section
open MeasureTheory SchwartzMap
namespace Hormander.C
open Hormander.B
variable {N k : ℕ}

theorem list_sum_map_le {α : Type*} (c : List α) (f g : α → ℝ) (h : ∀ z ∈ c, f z ≤ g z) :
    (c.map f).sum ≤ (c.map g).sum := by
  induction c with
  | nil => simp
  | cons z rest ih =>
    simp only [List.map_cons, List.sum_cons]
    exact add_le_add (h z (by simp)) (ih fun y hy => h y (by simp [hy]))

/-- A binary word of at most `s` leaves acts on `u` through its
integer expansion in standard words, with the word estimate applying to each term. -/
theorem frame_word_bound {k : ℕ} (Xs : Fin (k + 1) → RealSchwartzVectorField N)
    (cs : SchwartzMap (Carrier N) ℝ) {s : ℕ} {ε C8 : ℝ} (hC8 : 0 ≤ C8)
    (hgain : ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ ≤ s → WordEstimate Xs cs ℓ ε C8)
    (w : Hormander.Interface.LieWord k) (hw : Hormander.lieWordLength w ≤ s) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ u : TestFunction N,
      sobolevNorm (ε - 1) (vectorFieldOperator (combField Xs (binaryExpansion w)) u) ^ 2 ≤
        M * (normSq (diffusionOperator Xs cs u) + normSq u) := by
  set c := binaryExpansion w with hc
  set A : ℝ := (c.map fun z => |(z.1 : ℝ)|).sum with hA
  have hA0 : 0 ≤ A := List.sum_nonneg (by
    intro x hx
    obtain ⟨z, _, rfl⟩ := List.mem_map.mp hx
    exact abs_nonneg _)
  refine ⟨A ^ 2 * C8, by positivity, fun u => ?_⟩
  set Q := normSq (diffusionOperator Xs cs u) + normSq u with hQ
  have hQ0 : 0 ≤ Q := add_nonneg (normSq_nonneg _) (normSq_nonneg _)
  have hterm : ∀ z ∈ c, sobolevNorm (ε - 1) (vectorFieldOperator (wordField Xs (nestedToList z.2)) u) ≤
      Real.sqrt (C8 * Q) := by
    intro z hz
    have hlen : nestedLength z.2 = Hormander.lieWordLength w := binaryExpansion_length w z hz
    have h1 : 1 ≤ nestedLength z.2 := nestedLength_pos z.2
    have h2 : nestedLength z.2 ≤ s := hlen ▸ hw
    have := hgain (nestedLength z.2) h1 h2 (nestedToList z.2) (nestedToList_length z.2) u
    exact Real.le_sqrt_of_sq_le this
  have h1 := comb_norm_le Xs (ε - 1) c u
  have h2 : (c.map fun z => |(z.1 : ℝ)| * sobolevNorm (ε - 1)
      (vectorFieldOperator (wordField Xs (nestedToList z.2)) u)).sum ≤
      (c.map fun z => |(z.1 : ℝ)| * Real.sqrt (C8 * Q)).sum :=
    list_sum_map_le c _ _ fun z hz =>
      mul_le_mul_of_nonneg_left (hterm z hz) (abs_nonneg _)
  have h3 : (c.map fun z => |(z.1 : ℝ)| * Real.sqrt (C8 * Q)).sum = A * Real.sqrt (C8 * Q) := by
    rw [hA, List.sum_map_mul_right]
  have hnn : 0 ≤ sobolevNorm (ε - 1) (vectorFieldOperator (combField Xs c) u) := sobolevNorm_nonneg _ _
  have h4 := h1.trans (h2.trans h3.le)
  calc _ ≤ (A * Real.sqrt (C8 * Q)) ^ 2 := pow_le_pow_left₀ hnn h4 2
    _ = A ^ 2 * C8 * Q := by
        rw [mul_pow, Real.sq_sqrt (by positivity)]; ring

end Hormander.C
