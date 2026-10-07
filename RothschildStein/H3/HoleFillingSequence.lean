-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.HoleFillingRecursion

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3

/-- The explicit geometric radii and their positive gaps. -/
theorem holeFilling_radii {ρ R τ : ℝ} (hρR : ρ < R) (hτ : 0 < τ) (hτ1 : τ < 1) (n : ℕ) :
    let t := fun i : ℕ => ρ + (1 - τ ^ i) * (R - ρ)
    ρ ≤ t n ∧ t n < R ∧ t n < t (n + 1) ∧
      t (n + 1) - t n = ((1 - τ) * (R - ρ)) * τ ^ n := by
  have hn : 0 < τ ^ n := pow_pos hτ n
  have hn1 : τ ^ n ≤ 1 := pow_le_one₀ hτ.le hτ1.le
  dsimp only
  have he : (ρ + (1 - τ ^ (n + 1)) * (R - ρ)) -
      (ρ + (1 - τ ^ n) * (R - ρ)) = ((1 - τ) * (R - ρ)) * τ ^ n := by
    rw [pow_succ]; ring
  have hgap : 0 < ((1 - τ) * (R - ρ)) * τ ^ n := by positivity
  exact ⟨by nlinarith, by nlinarith, by linarith, he⟩

/-- The geometric gap has the exact inverse-power factor
needed by the finite iteration. -/
theorem holeFilling_gap_power {d τ β : ℝ} (hd : 0 < d) (hτ : 0 < τ) (n : ℕ) :
    (d * τ ^ n) ^ (-β) = d ^ (-β) * (τ ^ (-β)) ^ n := by
  rw [Real.mul_rpow hd.le (pow_nonneg hτ.le n), ← Real.rpow_natCast_mul hτ.le,
    show (n : ℝ) * -β = -β * n by ring, Real.rpow_mul_natCast hτ.le]

/-- A geometric choice of radii yields the precise two-term
bound, uniformly over theta < 1/3 (BB Lemma 8.55, p. 385). -/
theorem holeFilling_of_ratio {ψ : ℝ → ℝ} {T₀ T₁ ρ R τ θ A B β : ℝ}
    (hρ : T₀ ≤ ρ) (hρR : ρ < R) (hR : R ≤ T₁)
    (hτ : 0 < τ) (hτ1 : τ < 1) (hθ : 0 ≤ θ) (hθ3 : θ < 1 / 3)
    (hθτ : θ * τ ^ (-β) ≤ 1 / 2) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hb : ∃ M : ℝ, ∀ t ∈ Set.Icc T₀ T₁, ψ t ≤ M)
    (hstep : ∀ t s : ℝ, T₀ ≤ t → t < s → s ≤ T₁ →
      ψ t ≤ θ * ψ s + A / (s - t) ^ β + B) :
    ψ ρ ≤ 2 * A * ((1 - τ) * (R - ρ)) ^ (-β) + (3 / 2) * B := by
  let t := fun i : ℕ => ρ + (1 - τ ^ i) * (R - ρ)
  have hgeom (n : ℕ) := holeFilling_radii hρR hτ hτ1 n
  have hd : 0 < (1 - τ) * (R - ρ) := by positivity
  obtain ⟨M, hM⟩ := hb
  have hbound : ∀ n, ψ (t n) ≤ M := fun n =>
    hM (t n) ⟨hρ.trans (hgeom n).1, (hgeom n).2.1.le.trans hR⟩
  have hs : ∀ n, ψ (t n) ≤ θ * ψ (t (n + 1)) +
      (A * ((1 - τ) * (R - ρ)) ^ (-β)) * (τ ^ (-β)) ^ n + B := by
    intro n
    have hh := hstep (t n) (t (n + 1)) (hρ.trans (hgeom n).1)
      (hgeom n).2.2.1 ((hgeom (n + 1)).2.1.le.trans hR)
    rw [(hgeom n).2.2.2, div_eq_mul_inv, ← Real.rpow_neg (by positivity :
      0 ≤ ((1 - τ) * (R - ρ)) * τ ^ n), holeFilling_gap_power hd hτ n] at hh
    convert hh using 1
    ring
  have hh := holeFilling_recursive_bound hθ hθ3 (Real.rpow_nonneg hτ.le (-β))
    hθτ (mul_nonneg hA (Real.rpow_nonneg hd.le (-β))) hB hbound hs
  simpa only [t, pow_zero, sub_self, zero_mul, add_zero, mul_assoc] using hh

end RothschildStein.H3
