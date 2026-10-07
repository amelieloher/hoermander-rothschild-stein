-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib

/-!
# Restricted-error bounds: dyadic shell integrals on a small ball

Abstract setting of the small-ball estimates for the restricted error (BB pp. 606–607):
a measurable set `S` (the control ball `U_r`) with a real pseudo-distance `dr` on `S`, of diameter
`< 2ρ`, whose balls `S ∩ {dr x · < t}` have measure at most `Cv t^(q+1)` (the homogeneous volume
bound, `q + 1 = Q`). For radial weights `c / dr^n` the integral over `S` of a closed dyadic shell
`{a ≤ dr x y ≤ 2a}` is at most the weight at `a` times the volume of the `2a`-ball
(`lintegral_shell_le`); summing shells gives the ball integral `∫_{dr ≤ b} dr^(-q) ≤ C b`
(`lintegral_ball_le`, infinitely many shells down to the pole) and the far integral
`∫_{a ≤ dr} dr^(-(q+1)) ≤ J C` over at most `J` shells (`lintegral_far_le`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology
namespace RothschildStein.P1

variable {E : Type*} [MeasurableSpace E]

/-- The abstract small-ball data of the restricted-error estimates: a measurable set `S`
with a real pseudo-distance `dr` of diameter `< 2ρ`, symmetric, satisfying the triangle inequality
on `S`, and the homogeneous ball bound `μ(S ∩ {dr x · < t}) ≤ Cv t^(q+1)` for `0 < t ≤ 2ρ`
(`q + 1` is the homogeneous dimension). -/
structure ShellData (μ : Measure E) (S : Set E) (dr : E → E → ℝ) (q : ℕ) (ρ Cv : ℝ) : Prop where
  measurableSet : MeasurableSet S
  ρ_pos : 0 < ρ
  Cv_nonneg : 0 ≤ Cv
  dr_nonneg : ∀ x ∈ S, ∀ y ∈ S, 0 ≤ dr x y
  dr_self : ∀ x ∈ S, dr x x = 0
  dr_symm : ∀ x ∈ S, ∀ y ∈ S, dr x y = dr y x
  dr_tri : ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, dr x z ≤ dr x y + dr y z
  dr_lt : ∀ x ∈ S, ∀ y ∈ S, dr x y < 2 * ρ
  measurableSet_ball : ∀ x ∈ S, ∀ t : ℝ, 0 < t → t ≤ 2 * ρ → MeasurableSet (S ∩ {y | dr x y < t})
  measure_ball_le : ∀ x ∈ S, ∀ t : ℝ, 0 < t → t ≤ 2 * ρ →
    μ (S ∩ {y | dr x y < t}) ≤ ENNReal.ofReal (Cv * t ^ (q + 1))

/-- The closed dyadic shell `{a ≤ dr x y ≤ 2a}` in `S`. -/
def shell (S : Set E) (dr : E → E → ℝ) (x : E) (a : ℝ) : Set E :=
  S ∩ {y | a ≤ dr x y ∧ dr x y ≤ 2 * a}

namespace ShellData

variable {μ : Measure E} {S : Set E} {dr : E → E → ℝ} {q : ℕ} {ρ Cv : ℝ}
  (h : ShellData μ S dr q ρ Cv) {x : E}

include h

/-- Open balls of every radius are measurable. -/
theorem measurableSet_ball_all (hx : x ∈ S) (t : ℝ) : MeasurableSet (S ∩ {y | dr x y < t}) := by
  by_cases ht0 : t ≤ 0
  · have : S ∩ {y | dr x y < t} = ∅ := by
      ext y
      simp only [mem_inter_iff, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and, not_lt]
      intro hy
      exact ht0.trans (h.dr_nonneg x hx y hy)
    rw [this]
    exact MeasurableSet.empty
  · by_cases ht1 : t ≤ 2 * ρ
    · exact h.measurableSet_ball x hx t (not_le.mp ht0) ht1
    · have : S ∩ {y | dr x y < t} = S := by
        ext y
        simp only [mem_inter_iff, mem_ofPred_eq, and_iff_left_iff_imp]
        intro hy
        exact (h.dr_lt x hx y hy).trans (not_le.mp ht1)
      rw [this]
      exact h.measurableSet

/-- The ball bound holds for every positive radius. -/
theorem measure_ball_le_all (hx : x ∈ S) {t : ℝ} (ht : 0 < t) :
    μ (S ∩ {y | dr x y < t}) ≤ ENNReal.ofReal (Cv * t ^ (q + 1)) := by
  by_cases ht1 : t ≤ 2 * ρ
  · exact h.measure_ball_le x hx t ht ht1
  · have h2ρ : 0 < 2 * ρ := by linarith [h.ρ_pos]
    have hsub : S ∩ {y | dr x y < t} ⊆ S ∩ {y | dr x y < 2 * ρ} := fun y hy =>
      ⟨hy.1, h.dr_lt x hx y hy.1⟩
    calc μ (S ∩ {y | dr x y < t}) ≤ μ (S ∩ {y | dr x y < 2 * ρ}) := measure_mono hsub
      _ ≤ ENNReal.ofReal (Cv * (2 * ρ) ^ (q + 1)) := h.measure_ball_le x hx _ h2ρ le_rfl
      _ ≤ ENNReal.ofReal (Cv * t ^ (q + 1)) := by
        apply ENNReal.ofReal_le_ofReal
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h2ρ.le (not_le.mp ht1).le _)
          h.Cv_nonneg

/-- Closed balls are measurable. -/
theorem measurableSet_closedBall (hx : x ∈ S) (t : ℝ) : MeasurableSet (S ∩ {y | dr x y ≤ t}) := by
  have : S ∩ {y | dr x y ≤ t} = ⋂ n : ℕ, (S ∩ {y | dr x y < t + 1 / ((n : ℝ) + 1)}) := by
    ext y
    simp only [mem_inter_iff, mem_ofPred_eq, mem_iInter]
    constructor
    · rintro ⟨hy, hyt⟩ n
      have hn0 : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      exact ⟨hy, lt_of_le_of_lt hyt (by linarith)⟩
    · intro hn
      refine ⟨(hn 0).1, ?_⟩
      by_contra hlt
      rw [not_le] at hlt
      obtain ⟨n, hn1⟩ := exists_nat_one_div_lt (sub_pos.mpr hlt)
      have := (hn n).2
      linarith
  rw [this]
  exact MeasurableSet.iInter fun n => h.measurableSet_ball_all hx _

/-- The closed ball bound `μ(S ∩ {dr x · ≤ t}) ≤ Cv t^(q+1)`
(`t = 0` gives that `{dr x · = 0}` is null). -/
theorem measure_closedBall_le (hx : x ∈ S) {t : ℝ} (ht : 0 ≤ t) :
    μ (S ∩ {y | dr x y ≤ t}) ≤ ENNReal.ofReal (Cv * t ^ (q + 1)) := by
  have hT : Tendsto (fun s : ℝ => ENNReal.ofReal (Cv * s ^ (q + 1))) (𝓝[>] t)
      (𝓝 (ENNReal.ofReal (Cv * t ^ (q + 1)))) :=
    ((ENNReal.continuous_ofReal.comp
      (continuous_const.mul (continuous_id.pow (q + 1)))).tendsto t).mono_left nhdsWithin_le_nhds
  refine ge_of_tendsto hT ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hs' : t < s := hs
  calc μ (S ∩ {y | dr x y ≤ t}) ≤ μ (S ∩ {y | dr x y < s}) :=
        measure_mono fun y hy => ⟨hy.1, lt_of_le_of_lt hy.2 hs'⟩
    _ ≤ ENNReal.ofReal (Cv * s ^ (q + 1)) := h.measure_ball_le_all hx (by linarith)

/-- The pole set `{dr x · ≤ 0}` is null. -/
theorem measure_pole_eq_zero (hx : x ∈ S) : μ (S ∩ {y | dr x y ≤ 0}) = 0 := by
  have := h.measure_closedBall_le hx (le_refl (0 : ℝ))
  simpa using this

/-- The shell is measurable. -/
theorem measurableSet_shell (hx : x ∈ S) (a : ℝ) : MeasurableSet (shell S dr x a) := by
  have : shell S dr x a = (S ∩ {y | dr x y ≤ 2 * a}) \ (S ∩ {y | dr x y < a}) := by
    ext y
    constructor
    · rintro ⟨hy, h1, h2⟩
      exact ⟨⟨hy, h2⟩, fun h3 => absurd h3.2 (not_lt.mpr h1)⟩
    · rintro ⟨⟨hy, h2⟩, h1⟩
      exact ⟨hy, not_lt.mp (fun h3 => h1 ⟨hy, h3⟩), h2⟩
  rw [this]
  exact (h.measurableSet_closedBall hx _).diff (h.measurableSet_ball_all hx _)

/-- A shell of scale `a` has measure at most `Cv (2a)^(q+1)`. -/
theorem measure_shell_le (hx : x ∈ S) {a : ℝ} (ha : 0 ≤ a) :
    μ (shell S dr x a) ≤ ENNReal.ofReal (Cv * (2 * a) ^ (q + 1)) :=
  (measure_mono (s := shell S dr x a) (t := S ∩ {y | dr x y ≤ 2 * a})
    (fun y hy => ⟨hy.1, hy.2.2⟩)).trans (h.measure_closedBall_le hx (by linarith))

/-- **One dyadic shell.** The integral of the radial weight
`c / dr^n` over the shell `{a ≤ dr ≤ 2a}` is at most the weight at `a` times the volume of the
`2a`-ball. -/
theorem lintegral_shell_le (hx : x ∈ S) {a c : ℝ} (ha : 0 < a) (hc : 0 ≤ c) (n : ℕ) :
    ∫⁻ y in shell S dr x a, ENNReal.ofReal (c / dr x y ^ n) ∂μ ≤
      ENNReal.ofReal (c / a ^ n * (Cv * (2 * a) ^ (q + 1))) := by
  calc ∫⁻ y in shell S dr x a, ENNReal.ofReal (c / dr x y ^ n) ∂μ
      ≤ ∫⁻ y in shell S dr x a, ENNReal.ofReal (c / a ^ n) ∂μ :=
        setLIntegral_mono' (h.measurableSet_shell hx a) fun y hy =>
          ENNReal.ofReal_le_ofReal
            (div_le_div_of_nonneg_left hc (pow_pos ha n) (pow_le_pow_left₀ ha.le hy.2.1 n))
    _ = ENNReal.ofReal (c / a ^ n) * μ (shell S dr x a) := setLIntegral_const _ _
    _ ≤ ENNReal.ofReal (c / a ^ n) * ENNReal.ofReal (Cv * (2 * a) ^ (q + 1)) :=
        mul_le_mul_right (h.measure_shell_le hx ha.le) _
    _ = ENNReal.ofReal (c / a ^ n * (Cv * (2 * a) ^ (q + 1))) :=
        (ENNReal.ofReal_mul (div_nonneg hc (pow_nonneg ha.le n))).symm

/-- **Ball integral** (row/column integrals, near parts): over the
closed ball `{dr x · ≤ b}` the weight `c / dr^q` has integral at most `c Cv 2^(q+1) b` (infinitely
many dyadic shells, geometric sum; the pole is null). -/
theorem lintegral_ball_le (hx : x ∈ S) {c b : ℝ} (hc : 0 ≤ c) (hb : 0 ≤ b) :
    ∫⁻ y in S ∩ {y | dr x y ≤ b}, ENNReal.ofReal (c / dr x y ^ q) ∂μ ≤
      ENNReal.ofReal (c * (Cv * 2 ^ (q + 1)) * b) := by
  have h0 := h.measure_pole_eq_zero hx
  rcases hb.eq_or_lt with rfl | hb'
  · have hb0 : S ∩ {y | dr x y ≤ 0} = S ∩ {y | dr x y ≤ 0} := rfl
    rw [Measure.restrict_eq_zero.mpr h0, lintegral_zero_measure]
    exact bot_le
  · set a : ℕ → ℝ := fun j => b / 2 ^ (j + 1) with ha
    have hapos : ∀ j, 0 < a j := fun j => by simp only [ha]; positivity
    have hcover : S ∩ {y | dr x y ≤ b} ⊆
        (S ∩ {y | dr x y ≤ 0}) ∪ ⋃ j, shell S dr x (a j) := by
      rintro y ⟨hyS, hyb⟩
      by_cases hy0 : dr x y ≤ 0
      · exact Or.inl ⟨hyS, hy0⟩
      · right
        have hy0 : 0 < dr x y := not_le.mp hy0
        obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near (x := b / dr x y) (y := (2 : ℝ))
          ((one_le_div hy0).mpr hyb) one_lt_two
        refine mem_iUnion.mpr ⟨n, hyS, ?_, ?_⟩
        · have h1 : b < 2 ^ (n + 1) * dr x y := (div_lt_iff₀ hy0).mp hn2
          simp only [ha]
          rw [div_le_iff₀ (by positivity)]
          linarith
        · have h1 : 2 ^ n * dr x y ≤ b := (le_div_iff₀ hy0).mp hn1
          simp only [ha]
          rw [pow_succ]
          have hp : (0 : ℝ) < 2 ^ n := by positivity
          have : dr x y ≤ b / 2 ^ n := by rw [le_div_iff₀ hp]; linarith
          calc dr x y ≤ b / 2 ^ n := this
            _ = 2 * (b / (2 ^ n * 2)) := by field_simp
    set K : ℝ := c * (Cv * 2 ^ (q + 1)) with hK
    have hK0 : 0 ≤ K := mul_nonneg hc (mul_nonneg h.Cv_nonneg (by positivity))
    have hterm : ∀ j, ∫⁻ y in shell S dr x (a j), ENNReal.ofReal (c / dr x y ^ q) ∂μ ≤
        ENNReal.ofReal (K * b / 2 / 2 ^ j) := by
      intro j
      refine (h.lintegral_shell_le hx (hapos j) hc q).trans (le_of_eq ?_)
      congr 1
      simp only [ha, hK]
      have : (0 : ℝ) < b / 2 ^ (j + 1) := hapos j
      rw [mul_pow, pow_succ (b / 2 ^ (j + 1)) q]
      have hq : (0 : ℝ) < (b / 2 ^ (j + 1)) ^ q := by positivity
      field_simp
      ring
    calc ∫⁻ y in S ∩ {y | dr x y ≤ b}, ENNReal.ofReal (c / dr x y ^ q) ∂μ
        ≤ ∫⁻ y in (S ∩ {y | dr x y ≤ 0}) ∪ ⋃ j, shell S dr x (a j),
            ENNReal.ofReal (c / dr x y ^ q) ∂μ := lintegral_mono_set hcover
      _ ≤ ∫⁻ y in S ∩ {y | dr x y ≤ 0}, ENNReal.ofReal (c / dr x y ^ q) ∂μ +
            ∫⁻ y in ⋃ j, shell S dr x (a j), ENNReal.ofReal (c / dr x y ^ q) ∂μ :=
          lintegral_union_le _ _ _
      _ ≤ 0 + ∑' j, ∫⁻ y in shell S dr x (a j), ENNReal.ofReal (c / dr x y ^ q) ∂μ := by
          gcongr
          · exact (setLIntegral_measure_zero _ _ h0).le
          · exact lintegral_iUnion_le _ _
      _ ≤ ∑' j : ℕ, ENNReal.ofReal (K * b / 2 / 2 ^ j) := by
          rw [zero_add]
          exact ENNReal.tsum_le_tsum hterm
      _ = ENNReal.ofReal (K * b) := by
          rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => by positivity)
            (summable_geometric_two' _), tsum_geometric_two']

/-- **Far integral** (far parts of the Hölder estimate): if `S`
lies in `{dr x · < 2^J a}`, the weight `c / dr^(q+1)` has integral at most `J c Cv 2^(q+1)` over
`{a ≤ dr x ·}`, one bound `c Cv 2^(q+1)` per dyadic shell. -/
theorem lintegral_far_le (hx : x ∈ S) {c a : ℝ} (hc : 0 ≤ c) (ha : 0 < a) (J : ℕ)
    (hJ : ∀ y ∈ S, dr x y < 2 ^ J * a) :
    ∫⁻ y in S ∩ {y | a ≤ dr x y}, ENNReal.ofReal (c / dr x y ^ (q + 1)) ∂μ ≤
      ENNReal.ofReal (J * (c * (Cv * 2 ^ (q + 1)))) := by
  set K : ℝ := c * (Cv * 2 ^ (q + 1)) with hK
  have hK0 : 0 ≤ K := mul_nonneg hc (mul_nonneg h.Cv_nonneg (by positivity))
  have key : ∀ J' : ℕ, ∫⁻ y in S ∩ {y | a ≤ dr x y ∧ dr x y < 2 ^ J' * a},
      ENNReal.ofReal (c / dr x y ^ (q + 1)) ∂μ ≤ ENNReal.ofReal (J' * K) := by
    intro J'
    induction J' with
    | zero =>
      have : S ∩ {y | a ≤ dr x y ∧ dr x y < 2 ^ 0 * a} = ∅ := by
        refine Set.eq_empty_of_forall_notMem ?_
        rintro y ⟨_, h1, h2⟩
        rw [pow_zero, one_mul] at h2
        exact absurd h2 (not_lt.mpr h1)
      rw [this]
      simp
    | succ J' ih =>
      have hapos : 0 < 2 ^ J' * a := by positivity
      have hsub : S ∩ {y | a ≤ dr x y ∧ dr x y < 2 ^ (J' + 1) * a} ⊆
          (S ∩ {y | a ≤ dr x y ∧ dr x y < 2 ^ J' * a}) ∪ shell S dr x (2 ^ J' * a) := by
        rintro y ⟨hyS, h1, h2⟩
        by_cases hlt : dr x y < 2 ^ J' * a
        · exact Or.inl ⟨hyS, h1, hlt⟩
        · right
          refine ⟨hyS, not_lt.mp hlt, ?_⟩
          rw [pow_succ] at h2
          linarith
      have hshell := h.lintegral_shell_le hx hapos hc (q + 1)
      have hval : c / (2 ^ J' * a) ^ (q + 1) * (Cv * (2 * (2 ^ J' * a)) ^ (q + 1)) = K := by
        have hp : (0 : ℝ) < (2 ^ J' * a) ^ (q + 1) := by positivity
        rw [mul_pow 2 (2 ^ J' * a), hK]
        field_simp
      calc ∫⁻ y in S ∩ {y | a ≤ dr x y ∧ dr x y < 2 ^ (J' + 1) * a},
            ENNReal.ofReal (c / dr x y ^ (q + 1)) ∂μ
          ≤ ∫⁻ y in (S ∩ {y | a ≤ dr x y ∧ dr x y < 2 ^ J' * a}) ∪ shell S dr x (2 ^ J' * a),
              ENNReal.ofReal (c / dr x y ^ (q + 1)) ∂μ := lintegral_mono_set hsub
        _ ≤ _ + _ := lintegral_union_le _ _ _
        _ ≤ ENNReal.ofReal (J' * K) + ENNReal.ofReal K := by
            gcongr
            rw [hval] at hshell
            exact hshell
        _ = ENNReal.ofReal (((J' + 1 : ℕ) : ℝ) * K) := by
            rw [← ENNReal.ofReal_add (mul_nonneg (Nat.cast_nonneg _) hK0) hK0]
            congr 1
            push_cast
            ring
  refine le_trans (lintegral_mono_set ?_) (key J)
  rintro y ⟨hyS, hy⟩
  exact ⟨hyS, hy, hJ y hyS⟩

/-- The row integral of `c / dr^q` over all of `S` is at most
`c Cv 2^(q+1) (2ρ)`. -/
theorem lintegral_row_le (hx : x ∈ S) {c : ℝ} (hc : 0 ≤ c) :
    ∫⁻ y in S, ENNReal.ofReal (c / dr x y ^ q) ∂μ ≤
      ENNReal.ofReal (c * (Cv * 2 ^ (q + 1)) * (2 * ρ)) := by
  refine le_trans (lintegral_mono_set (t := S ∩ {y | dr x y ≤ 2 * ρ}) ?_)
    (h.lintegral_ball_le hx hc (by linarith [h.ρ_pos]))
  exact fun y hy => ⟨hy, (h.dr_lt x hx y hy).le⟩

end ShellData

end RothschildStein.P1
