-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.HoleFillingSequence

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set
namespace RothschildStein.H3

/-- The explicit constant in the hole-filling estimate, including β = 0. -/
def holeFillingConstant (β : ℝ) : ℝ :=
  if β = 0 then 3 / 2 else
    max (2 * (1 - (2 / 3 : ℝ) ^ (1 / β)) ^ (-β)) (3 / 2)

/-- The constant is at least 3/2. -/
theorem holeFillingConstant_ge (β : ℝ) : 3 / 2 ≤ holeFillingConstant β := by
  unfold holeFillingConstant
  split_ifs
  · exact le_rfl
  · exact le_max_right _ _

/-- The explicit ratio is strictly between zero and one and
has inverse-beta power 3/2. -/
theorem holeFilling_ratio {β : ℝ} (hβ : 0 < β) :
    let τ := (2 / 3 : ℝ) ^ (1 / β)
    0 < τ ∧ τ < 1 ∧ τ ^ (-β) = 3 / 2 := by
  refine ⟨Real.rpow_pos_of_pos (by norm_num) _,
    Real.rpow_lt_one (by norm_num) (by norm_num) (by positivity), ?_⟩
  rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2 / 3),
    show (1 / β) * -β = -1 by field_simp, Real.rpow_neg_one]
  norm_num

/-- The beta-zero case has the same constant for both forcing
terms, without dividing by beta. -/
theorem holeFilling_zero {ψ : ℝ → ℝ} {T₀ T₁ ρ R θ A B : ℝ}
    (hρ : T₀ ≤ ρ) (hρR : ρ < R) (hR : R ≤ T₁)
    (hθ : 0 ≤ θ) (hθ3 : θ < 1 / 3) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hb : ∃ M : ℝ, ∀ t ∈ Icc T₀ T₁, ψ t ≤ M)
    (hstep : ∀ t s : ℝ, T₀ ≤ t → t < s → s ≤ T₁ →
      ψ t ≤ θ * ψ s + A + B) :
    ψ ρ ≤ (3 / 2) * (A + B) := by
  let t := fun i : ℕ => ρ + (1 - (1 / 2 : ℝ) ^ i) * (R - ρ)
  have hg (n : ℕ) := holeFilling_radii hρR (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1) n
  obtain ⟨M, hM⟩ := hb
  have hbound : ∀ n, ψ (t n) ≤ M := fun n =>
    hM (t n) ⟨hρ.trans (hg n).1, (hg n).2.1.le.trans hR⟩
  have hs : ∀ n, ψ (t n) ≤ θ * ψ (t (n + 1)) + (0 : ℝ) * (1 : ℝ) ^ n + (A + B) := by
    intro n
    have hh := hstep (t n) (t (n + 1)) (hρ.trans (hg n).1)
      (hg n).2.2.1 ((hg (n + 1)).2.1.le.trans hR)
    simpa only [zero_mul, add_zero, add_assoc] using hh
  have hh := holeFilling_recursive_bound hθ hθ3 (by norm_num : (0 : ℝ) ≤ 1)
    (by simpa only [mul_one] using (hθ3.le.trans (by norm_num : (1 / 3 : ℝ) ≤ 1 / 2)))
    le_rfl (add_nonneg hA hB) hbound hs
  simpa only [t, pow_zero, sub_self, zero_mul, mul_zero, add_zero, zero_add] using hh

/-- The hole-filling estimate includes the explicit constant, boundedness,
nonnegative data, and the β = 0 case. BB Lemma 8.55, p. 385; see also
BB Theorems 11.53 and 11.57. -/
theorem holeFilling {ψ : ℝ → ℝ} {T₀ T₁ θ A B β : ℝ}
    (_hT₀ : 0 ≤ T₀) (_hT : T₀ < T₁)
    (_hψ : ∀ t ∈ Icc T₀ T₁, 0 ≤ ψ t)
    (hb : ∃ M : ℝ, ∀ t ∈ Icc T₀ T₁, ψ t ≤ M)
    (hθ : 0 ≤ θ) (hθ3 : θ < 1 / 3) (hA : 0 ≤ A) (hB : 0 ≤ B) (hβ : 0 ≤ β)
    (hstep : ∀ t s : ℝ, T₀ ≤ t → t < s → s ≤ T₁ →
      ψ t ≤ θ * ψ s + A / (s - t) ^ β + B)
    {ρ R : ℝ} (hρ : T₀ ≤ ρ) (hρR : ρ < R) (hR : R ≤ T₁) :
    ψ ρ ≤ holeFillingConstant β * (A / (R - ρ) ^ β + B) := by
  by_cases hz : β = 0
  · subst β
    simp only [holeFillingConstant, Real.rpow_zero, div_one] at *
    exact holeFilling_zero hρ hρR hR hθ hθ3 hA hB hb hstep
  · have hβp : 0 < β := lt_of_le_of_ne hβ (Ne.symm hz)
    let τ := (2 / 3 : ℝ) ^ (1 / β)
    obtain ⟨hτ, hτ1, hp⟩ := holeFilling_ratio hβp
    have hθτ : θ * τ ^ (-β) ≤ 1 / 2 := by rw [hp]; linarith
    have hh := holeFilling_of_ratio hρ hρR hR hτ hτ1 hθ hθ3 hθτ hA hB hb hstep
    have hd : 0 < R - ρ := sub_pos.mpr hρR
    have he : 2 * A * ((1 - τ) * (R - ρ)) ^ (-β) =
        (2 * (1 - τ) ^ (-β)) * (A / (R - ρ) ^ β) := by
      rw [Real.mul_rpow (sub_pos.mpr hτ1).le hd.le, Real.rpow_neg hd.le]
      ring
    rw [he] at hh
    have hcost : 0 ≤ A / (R - ρ) ^ β := div_nonneg hA (Real.rpow_nonneg hd.le β)
    have hC₁ : 2 * (1 - τ) ^ (-β) ≤ holeFillingConstant β := by
      simpa only [holeFillingConstant, ite_eq_right hz, τ] using le_max_left
        (2 * (1 - (2 / 3 : ℝ) ^ (1 / β)) ^ (-β)) (3 / 2)
    have hC₂ := holeFillingConstant_ge β
    exact hh.trans (by nlinarith [mul_le_mul_of_nonneg_right hC₁ hcost,
      mul_le_mul_of_nonneg_right hC₂ hB])

end RothschildStein.H3
