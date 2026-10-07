-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.B.WeightEstimates
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

@[expose] public section

noncomputable section

open scoped RealInnerProductSpace

namespace Hormander.B

section Weights

variable {E : Type*} [NormedAddCommGroup E]

theorem bracketSq_pos' (x : E) : 0 < bracketSq x := by
  unfold bracketSq
  positivity

theorem japBracket_pos (x : E) : 0 < japBracket x :=
  Real.sqrt_pos.2 (bracketSq_pos' x)

theorem one_le_japBracket (x : E) : 1 ≤ japBracket x := by
  unfold japBracket
  rw [Real.one_le_sqrt]
  unfold bracketSq
  nlinarith [sq_nonneg ‖x‖]

theorem norm_le_japBracket (x : E) : ‖x‖ ≤ japBracket x := by
  unfold japBracket
  apply Real.le_sqrt_of_sq_le
  unfold bracketSq
  nlinarith

theorem japBracket_sq (x : E) : japBracket x ^ 2 = bracketSq x :=
  Real.sq_sqrt (bracketSq_pos' x).le

theorem japBracket_rpow (x : E) (p : ℝ) : japBracket x ^ p = bracketSq x ^ (p / 2) := by
  unfold japBracket
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (bracketSq_pos' x).le]
  congr 1
  ring

variable [InnerProductSpace ℝ E]

/-- The squared bracket along an affine segment. -/
theorem hasDerivAt_bracketSq_segment (x a : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => bracketSq (x + s • a)) (2 * ⟪x + t • a, a⟫) t := by
  have hline : HasDerivAt (fun s : ℝ => x + s • a) a t := by
    simpa using ((hasDerivAt_id t).smul_const a).const_add x
  simpa [bracketSq] using hline.norm_sq.const_add 1

/-- Derivative of a bracket power along an affine segment. -/
theorem hasDerivAt_weight_segment (σ : ℝ) (x a : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => bracketSq (x + s • a) ^ (σ / 2))
      (σ * bracketSq (x + t • a) ^ ((σ - 2) / 2) * ⟪x + t • a, a⟫) t := by
  have hq := hasDerivAt_bracketSq_segment x a t
  have h := hq.rpow_const (p := σ / 2) (Or.inl (ne_of_gt (bracketSq_pos' (x + t • a))))
  convert h using 1
  rw [show σ / 2 - 1 = (σ - 2) / 2 by ring]
  ring

/-- Derivative along a segment of the gradient of a bracket power, paired with a vector. -/
theorem hasDerivAt_gradPair_segment (σ : ℝ) (x a b : E) (t : ℝ) :
    HasDerivAt (fun s : ℝ => σ * bracketSq (x + s • a) ^ ((σ - 2) / 2) * ⟪x + s • a, b⟫)
      (σ * ((σ - 2) * bracketSq (x + t • a) ^ ((σ - 4) / 2) *
          ⟪x + t • a, a⟫ * ⟪x + t • a, b⟫ +
        bracketSq (x + t • a) ^ ((σ - 2) / 2) * ⟪a, b⟫)) t := by
  have hq := hasDerivAt_bracketSq_segment x a t
  have h1 := hq.rpow_const (p := (σ - 2) / 2) (Or.inl (ne_of_gt (bracketSq_pos' (x + t • a))))
  have hline : HasDerivAt (fun s : ℝ => x + s • a) a t := by
    simpa using ((hasDerivAt_id t).smul_const a).const_add x
  have h2 : HasDerivAt (fun s : ℝ => ⟪x + s • a, b⟫) ⟪a, b⟫ t := by
    simpa using hline.inner ℝ (hasDerivAt_const t b)
  have h3 := (h1.const_mul σ).mul h2
  convert h3 using 1
  rw [show (σ - 2) / 2 - 1 = (σ - 4) / 2 by ring]
  ring

theorem abs_inner_le_japBracket_mul (z a : E) : |⟪z, a⟫| ≤ japBracket z * ‖a‖ :=
  (abs_real_inner_le_norm z a).trans
    (mul_le_mul_of_nonneg_right (norm_le_japBracket z) (norm_nonneg a))

/-- The second-order derivative of a bracket power along a segment is controlled by the
bracket power of order two less. -/
theorem gradPair_deriv_bound (σ : ℝ) (z a b : E) :
    |σ * ((σ - 2) * bracketSq z ^ ((σ - 4) / 2) * ⟪z, a⟫ * ⟪z, b⟫ +
        bracketSq z ^ ((σ - 2) / 2) * ⟪a, b⟫)| ≤
      |σ| * (|σ - 2| + 1) * bracketSq z ^ ((σ - 2) / 2) * (‖a‖ * ‖b‖) := by
  have hq := bracketSq_pos' z
  have hsplit : bracketSq z ^ ((σ - 4) / 2) = bracketSq z ^ ((σ - 2) / 2) / bracketSq z := by
    rw [show (σ - 4) / 2 = (σ - 2) / 2 - 1 by ring, Real.rpow_sub hq, Real.rpow_one]
  have hP : 0 < bracketSq z ^ ((σ - 2) / 2) := Real.rpow_pos_of_pos hq _
  have hza : |⟪z, a⟫| ≤ japBracket z * ‖a‖ := abs_inner_le_japBracket_mul z a
  have hzb : |⟪z, b⟫| ≤ japBracket z * ‖b‖ := abs_inner_le_japBracket_mul z b
  have hab : |⟪a, b⟫| ≤ ‖a‖ * ‖b‖ := abs_real_inner_le_norm a b
  have hprod : |⟪z, a⟫ * ⟪z, b⟫| ≤ bracketSq z * (‖a‖ * ‖b‖) := by
    rw [abs_mul]
    calc |⟪z, a⟫| * |⟪z, b⟫| ≤ (japBracket z * ‖a‖) * (japBracket z * ‖b‖) :=
          mul_le_mul hza hzb (abs_nonneg _) (by have := japBracket_pos z; positivity)
      _ = japBracket z ^ 2 * (‖a‖ * ‖b‖) := by ring
      _ = _ := by rw [japBracket_sq]
  have hterm1 : |(σ - 2) * bracketSq z ^ ((σ - 4) / 2) * ⟪z, a⟫ * ⟪z, b⟫| ≤
      |σ - 2| * bracketSq z ^ ((σ - 2) / 2) * (‖a‖ * ‖b‖) := by
    have : (σ - 2) * bracketSq z ^ ((σ - 4) / 2) * ⟪z, a⟫ * ⟪z, b⟫ =
        (σ - 2) * (bracketSq z ^ ((σ - 2) / 2) / bracketSq z) * (⟪z, a⟫ * ⟪z, b⟫) := by
      rw [hsplit]; ring
    rw [this, abs_mul, abs_mul, abs_div, abs_of_pos hP, abs_of_pos hq]
    calc |σ - 2| * (bracketSq z ^ ((σ - 2) / 2) / bracketSq z) * |⟪z, a⟫ * ⟪z, b⟫|
        ≤ |σ - 2| * (bracketSq z ^ ((σ - 2) / 2) / bracketSq z) *
            (bracketSq z * (‖a‖ * ‖b‖)) :=
          mul_le_mul_of_nonneg_left hprod (by positivity)
      _ = _ := by field_simp
  have hterm2 : |bracketSq z ^ ((σ - 2) / 2) * ⟪a, b⟫| ≤
      bracketSq z ^ ((σ - 2) / 2) * (‖a‖ * ‖b‖) := by
    rw [abs_mul, abs_of_pos hP]
    exact mul_le_mul_of_nonneg_left hab hP.le
  rw [abs_mul]
  calc |σ| * |(σ - 2) * bracketSq z ^ ((σ - 4) / 2) * ⟪z, a⟫ * ⟪z, b⟫ +
          bracketSq z ^ ((σ - 2) / 2) * ⟪a, b⟫|
      ≤ |σ| * (|σ - 2| * bracketSq z ^ ((σ - 2) / 2) * (‖a‖ * ‖b‖) +
          bracketSq z ^ ((σ - 2) / 2) * (‖a‖ * ‖b‖)) :=
        mul_le_mul_of_nonneg_left ((abs_add_le _ _).trans (add_le_add hterm1 hterm2))
          (abs_nonneg _)
    _ = _ := by ring

/-- Weights along a segment whose length is at most half the larger endpoint weight. -/
theorem segment_weight_bounds (x a : E) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (h : 2 * ‖a‖ ≤ max (japBracket x) (japBracket (x + a))) :
    max (japBracket x) (japBracket (x + a)) / 2 ≤ japBracket (x + t • a) ∧
      japBracket (x + t • a) ≤ 2 * max (japBracket x) (japBracket (x + a)) := by
  have hn1 : ‖(x + t • a) - x‖ ≤ ‖a‖ := by
    simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0]
    exact mul_le_of_le_one_left (norm_nonneg a) ht1
  have hn2 : ‖(x + t • a) - (x + a)‖ ≤ ‖a‖ := by
    have : (x + t • a) - (x + a) = (t - 1) • a := by
      rw [sub_smul, one_smul]; abel
    rw [this, norm_smul, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    nlinarith [norm_nonneg a]
  have l1 := japBracketLipschitz (x + t • a) x
  have l2 := japBracketLipschitz (x + t • a) (x + a)
  have l1' := (abs_le.1 (l1.trans hn1))
  have l2' := (abs_le.1 (l2.trans hn2))
  have hM := le_max_left (japBracket x) (japBracket (x + a))
  have hM' := le_max_right (japBracket x) (japBracket (x + a))
  constructor
  · rcases le_total (japBracket x) (japBracket (x + a)) with hle | hle
    · rw [max_eq_right hle] at h ⊢
      linarith [l2'.1, l2'.2]
    · rw [max_eq_left hle] at h ⊢
      linarith [l1'.1, l1'.2]
  · rcases le_total (japBracket x) (japBracket (x + a)) with hle | hle
    · rw [max_eq_right hle] at h ⊢
      linarith [l2'.1, l2'.2]
    · rw [max_eq_left hle] at h ⊢
      linarith [l1'.1, l1'.2]

theorem max_rpow_le_sum (p : ℝ) (u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    (max u v) ^ p ≤ u ^ p + v ^ p := by
  have hu' := Real.rpow_nonneg hu.le p
  have hv' := Real.rpow_nonneg hv.le p
  rcases le_total u v with h | h
  · rw [max_eq_right h]; linarith
  · rw [max_eq_left h]; linarith

/-- Bracket powers along a short segment are controlled by the endpoint powers. -/
theorem segment_weight_pow_le (p : ℝ) (x a : E) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (h : 2 * ‖a‖ ≤ max (japBracket x) (japBracket (x + a))) :
    japBracket (x + t • a) ^ p ≤
      2 ^ |p| * (japBracket x ^ p + japBracket (x + a) ^ p) := by
  obtain ⟨hlo, hhi⟩ := segment_weight_bounds x a t ht0 ht1 h
  set M := max (japBracket x) (japBracket (x + a)) with hMdef
  have hxpos := japBracket_pos x
  have hapos := japBracket_pos (x + a)
  have hMpos : 0 < M := lt_max_of_lt_left hxpos
  have hLpos := japBracket_pos (x + t • a)
  have hMp : M ^ p ≤ japBracket x ^ p + japBracket (x + a) ^ p :=
    max_rpow_le_sum p _ _ hxpos hapos
  have h2pos : (0 : ℝ) < 2 ^ |p| := by positivity
  by_cases hp : 0 ≤ p
  · calc japBracket (x + t • a) ^ p ≤ (2 * M) ^ p := Real.rpow_le_rpow hLpos.le hhi hp
      _ = 2 ^ p * M ^ p := Real.mul_rpow (by norm_num) hMpos.le
      _ ≤ 2 ^ |p| * M ^ p := by
          rw [abs_of_nonneg hp]
      _ ≤ _ := mul_le_mul_of_nonneg_left hMp h2pos.le
  · have hp' : p ≤ 0 := (not_le.1 hp).le
    calc japBracket (x + t • a) ^ p ≤ (M / 2) ^ p :=
          Real.rpow_le_rpow_of_nonpos (by positivity) hlo hp'
      _ = M ^ p / 2 ^ p := Real.div_rpow hMpos.le (by norm_num) p
      _ = 2 ^ |p| * M ^ p := by
          rw [abs_of_nonpos hp', Real.rpow_neg (by norm_num)]
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hMp h2pos.le

/-- The constant in the gradient endpoint estimate. -/
def gradConst (σ : ℝ) : ℝ := |σ| * (|σ - 2| + 1) * 2 ^ |σ - 2| + 2 * |σ|

theorem gradConst_nonneg (σ : ℝ) : 0 ≤ gradConst σ := by unfold gradConst; positivity

/-- The scalar-valued gradient pairing `σ ⟨z⟩^(σ-2) ⟪z, b⟫`. -/
def gradPair (σ : ℝ) (b z : E) : ℝ := σ * bracketSq z ^ ((σ - 2) / 2) * ⟪z, b⟫

omit [InnerProductSpace ℝ E] in
theorem bracketSq_rpow_half (z : E) (p : ℝ) : bracketSq z ^ (p / 2) = japBracket z ^ p :=
  (japBracket_rpow z p).symm

/-- Derivative bound for the gradient pairing along a short segment, at interior points. -/
theorem gradPair_segment_deriv_bound (σ : ℝ) (x a b : E) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (h : 2 * ‖a‖ ≤ max (japBracket x) (japBracket (x + a))) :
    |σ * ((σ - 2) * bracketSq (x + t • a) ^ ((σ - 4) / 2) * ⟪x + t • a, a⟫ *
        ⟪x + t • a, b⟫ + bracketSq (x + t • a) ^ ((σ - 2) / 2) * ⟪a, b⟫)| ≤
      |σ| * (|σ - 2| + 1) * 2 ^ |σ - 2| * (‖a‖ * ‖b‖) *
        (japBracket x ^ (σ - 2) + japBracket (x + a) ^ (σ - 2)) := by
  refine (gradPair_deriv_bound σ (x + t • a) a b).trans ?_
  rw [bracketSq_rpow_half]
  have := segment_weight_pow_le (σ - 2) x a t ht0 ht1 h
  have hc : 0 ≤ |σ| * (|σ - 2| + 1) * (‖a‖ * ‖b‖) := by positivity
  calc |σ| * (|σ - 2| + 1) * japBracket (x + t • a) ^ (σ - 2) * (‖a‖ * ‖b‖)
      = (|σ| * (|σ - 2| + 1) * (‖a‖ * ‖b‖)) * japBracket (x + t • a) ^ (σ - 2) := by ring
    _ ≤ (|σ| * (|σ - 2| + 1) * (‖a‖ * ‖b‖)) *
          (2 ^ |σ - 2| * (japBracket x ^ (σ - 2) + japBracket (x + a) ^ (σ - 2))) :=
        mul_le_mul_of_nonneg_left this hc
    _ = _ := by ring

theorem gradPair_endpoint_crude (σ : ℝ) (x b : E) :
    |gradPair σ b x| ≤ |σ| * japBracket x ^ (σ - 2) * (japBracket x * ‖b‖) := by
  unfold gradPair
  rw [bracketSq_rpow_half, abs_mul, abs_mul]
  have hpos : 0 < japBracket x ^ (σ - 2) := Real.rpow_pos_of_pos (japBracket_pos x) _
  rw [abs_of_pos hpos]
  exact mul_le_mul_of_nonneg_left (abs_inner_le_japBracket_mul x b) (by positivity)

/-- Global endpoint estimate for the gradient of the bracket power
`G(x)=⟨x⟩^(σ-2)x`:
the difference of `σ ⟨z⟩^(σ-2) z` between two points is controlled by the endpoint weights,
including segments that pass near the origin. -/
theorem gradPair_difference_bound (σ : ℝ) (x a b : E) :
    |gradPair σ b (x + a) - gradPair σ b x| ≤
      gradConst σ * ‖a‖ * ‖b‖ * (japBracket x ^ (σ - 2) + japBracket (x + a) ^ (σ - 2)) := by
  set M := max (japBracket x) (japBracket (x + a)) with hM
  have hxpos := japBracket_pos x
  have hapos := japBracket_pos (x + a)
  have hxp : 0 < japBracket x ^ (σ - 2) := Real.rpow_pos_of_pos hxpos _
  have hap : 0 < japBracket (x + a) ^ (σ - 2) := Real.rpow_pos_of_pos hapos _
  by_cases hsmall : 2 * ‖a‖ ≤ M
  · set f : ℝ → ℝ := fun s => σ * bracketSq (x + s • a) ^ ((σ - 2) / 2) * ⟪x + s • a, b⟫ with hf
    have hd : ∀ s : ℝ, HasDerivAt f
        (σ * ((σ - 2) * bracketSq (x + s • a) ^ ((σ - 4) / 2) * ⟪x + s • a, a⟫ *
          ⟪x + s • a, b⟫ + bracketSq (x + s • a) ^ ((σ - 2) / 2) * ⟪a, b⟫)) s :=
      fun s => hasDerivAt_gradPair_segment σ x a b s
    obtain ⟨c, hc, hceq⟩ := exists_hasDerivAt_eq_slope f _ (zero_lt_one)
      (fun s _ => (hd s).continuousAt.continuousWithinAt) (fun s _ => hd s)
    have hf1 : f 1 = gradPair σ b (x + a) := by simp [hf, gradPair]
    have hf0 : f 0 = gradPair σ b x := by simp [hf, gradPair]
    rw [hf1, hf0] at hceq
    have hb := gradPair_segment_deriv_bound σ x a b c hc.1.le hc.2.le hsmall
    simp only [sub_zero, div_one] at hceq
    rw [← hceq]
    refine hb.trans ?_
    have hC : |σ| * (|σ - 2| + 1) * 2 ^ |σ - 2| ≤ gradConst σ := by
      unfold gradConst; nlinarith [abs_nonneg σ]
    have hmul : 0 ≤ (‖a‖ * ‖b‖) * (japBracket x ^ (σ - 2) + japBracket (x + a) ^ (σ - 2)) := by
      positivity
    nlinarith [mul_le_mul_of_nonneg_right hC hmul]
  · have hlt : M < 2 * ‖a‖ := not_le.1 hsmall
    have h1 := gradPair_endpoint_crude σ x b
    have h2 := gradPair_endpoint_crude σ (x + a) b
    have hx : japBracket x ≤ 2 * ‖a‖ := (le_max_left _ _).trans hlt.le
    have hxa : japBracket (x + a) ≤ 2 * ‖a‖ := (le_max_right _ _).trans hlt.le
    have e1 : |gradPair σ b x| ≤ 2 * |σ| * ‖a‖ * ‖b‖ * japBracket x ^ (σ - 2) := by
      refine h1.trans ?_
      have : japBracket x * ‖b‖ ≤ 2 * ‖a‖ * ‖b‖ :=
        mul_le_mul_of_nonneg_right hx (norm_nonneg b)
      calc |σ| * japBracket x ^ (σ - 2) * (japBracket x * ‖b‖)
          ≤ |σ| * japBracket x ^ (σ - 2) * (2 * ‖a‖ * ‖b‖) :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = _ := by ring
    have e2 : |gradPair σ b (x + a)| ≤ 2 * |σ| * ‖a‖ * ‖b‖ * japBracket (x + a) ^ (σ - 2) := by
      refine h2.trans ?_
      have : japBracket (x + a) * ‖b‖ ≤ 2 * ‖a‖ * ‖b‖ :=
        mul_le_mul_of_nonneg_right hxa (norm_nonneg b)
      calc |σ| * japBracket (x + a) ^ (σ - 2) * (japBracket (x + a) * ‖b‖)
          ≤ |σ| * japBracket (x + a) ^ (σ - 2) * (2 * ‖a‖ * ‖b‖) :=
            mul_le_mul_of_nonneg_left this (by positivity)
        _ = _ := by ring
    calc |gradPair σ b (x + a) - gradPair σ b x|
        ≤ |gradPair σ b (x + a)| + |gradPair σ b x| := abs_sub _ _
      _ ≤ 2 * |σ| * ‖a‖ * ‖b‖ * (japBracket x ^ (σ - 2) + japBracket (x + a) ^ (σ - 2)) := by
          nlinarith [mul_nonneg (mul_nonneg (mul_nonneg (by positivity : (0:ℝ) ≤ 2 * |σ|)
            (norm_nonneg a)) (norm_nonneg b)) hxp.le,
            mul_nonneg (mul_nonneg (mul_nonneg (by positivity : (0:ℝ) ≤ 2 * |σ|)
            (norm_nonneg a)) (norm_nonneg b)) hap.le]
      _ ≤ _ := by
          have hC : 2 * |σ| ≤ gradConst σ := by
            unfold gradConst; nlinarith [mul_nonneg (mul_nonneg (abs_nonneg σ)
              (by positivity : (0:ℝ) ≤ |σ - 2| + 1)) (by positivity : (0:ℝ) ≤ 2 ^ |σ - 2|)]
          have hmul : 0 ≤ ‖a‖ * ‖b‖ *
              (japBracket x ^ (σ - 2) + japBracket (x + a) ^ (σ - 2)) := by positivity
          nlinarith [mul_le_mul_of_nonneg_right hC hmul]

end Weights

end Hormander.B
