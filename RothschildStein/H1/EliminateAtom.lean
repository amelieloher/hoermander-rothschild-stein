-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.ShrinkingPairing
public import RothschildStein.H1.TestOperator

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped Topology
namespace RothschildStein.H1
variable {N q : ℕ} (G : HomogeneousGroup N)

/-- Pulling a compact test back by an expanding dilation preserves
its domain when that domain is star-shaped for the group dilations
(BB pp. 251–253). -/
def expandingDilatedTest (Ω : Opens (Fin N → ℝ))
    (hΩ : ∀ t : ℝ, 0 < t → t ≤ 1 → ∀ x ∈ Ω, G.dilate t x ∈ Ω)
    {s : ℝ} (hs : 1 ≤ s) (φ : TestFunction Ω ℝ (⊤ : ℕ∞)) :
    TestFunction Ω ℝ (⊤ : ℕ∞) := by
  have hpos : 0 < s := zero_lt_one.trans_le hs
  let e : (Fin N → ℝ) ≃ₜ (Fin N → ℝ) :=
    { toFun := G.dilate s
      invFun := G.dilate s⁻¹
      left_inv := G2.dilate_inv_dilate G hpos.ne'
      right_inv := by intro x; rw [G2.dilate_dilate, mul_inv_cancel₀ hpos.ne', G2.dilate_one]
      continuous_toFun := (G2.contDiff_dilate G s).continuous
      continuous_invFun := (G2.contDiff_dilate G s⁻¹).continuous }
  refine ⟨φ ∘ G.dilate s, φ.contDiff.comp (G2.contDiff_dilate G s),
    φ.hasCompactSupport.comp_homeomorph e, ?_⟩
  intro x hx
  have hd : G.dilate s x ∈ tsupport (φ : (Fin N → ℝ) → ℝ) := by
    exact (Set.ext_iff.mp (tsupport_comp_eq_preimage (φ : (Fin N → ℝ) → ℝ) e) x).mp hx
  have H := hΩ s⁻¹ (inv_pos.mpr hpos) (inv_le_one_of_one_le₀ hs)
    (G.dilate s x) (φ.tsupport_subset hd)
  rw [G2.dilate_inv_dilate G hpos.ne'] at H
  exact H

/-- The residual atom vanishes once the local L1 representative
is obtained. The hypotheses retain the full weak equation on every test
and the degree-two operator identity, and use an actual test with nonzero
operator value at zero (BB (6.6)–(6.8), pp. 251–253). -/
theorem residual_atom_eq_zero
    (Ω : Opens (Fin N → ℝ))
    (hΩ : ∀ t : ℝ, 0 < t → t ≤ 1 → ∀ x ∈ Ω, G.dilate t x ∈ Ω)
    (X : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin N → ℝ)))
    (hP : G2.IsHomogeneousOperator G (sumSquaresWithDrift X) 2)
    {γ : (Fin N → ℝ) → ℝ} (hγ : Integrable γ) {α : ℝ}
    (hidentity : ∀ φ : TestFunction Ω ℝ (⊤ : ℕ∞),
      (∫ x, γ x * sumSquaresWithDrift X φ x) + α * sumSquaresWithDrift X φ 0 = φ 0)
    (φ₁ : TestFunction Ω ℝ (⊤ : ℕ∞)) (hφzero : φ₁ 0 = 0)
    (hφop : sumSquaresWithDrift X φ₁ 0 ≠ 0) : α = 0 := by
  let ψ := sumSquaresTest Ω X hX φ₁
  have he (x : Fin N → ℝ) : ψ x = sumSquaresWithDrift X φ₁ x :=
    sumSquaresTest_apply Ω X hX φ₁ x
  have hpair (n : ℕ) : (∫ x, γ x * ψ (G.dilate ((2 : ℝ) ^ n) x)) =
      -α * ψ 0 := by
    have hs : 1 ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
    let φn := expandingDilatedTest G Ω hΩ hs φ₁
    have H := hidentity φn
    have hfun : (φn : (Fin N → ℝ) → ℝ) = φ₁ ∘ G.dilate ((2 : ℝ) ^ n) := rfl
    have hpoint (x : Fin N → ℝ) : sumSquaresWithDrift X φn x =
        ((2 : ℝ) ^ n) ^ 2 * ψ (G.dilate ((2 : ℝ) ^ n) x) := by
      rw [hfun, hP φ₁ φ₁.contDiff ((2 : ℝ) ^ n) (pow_pos (by norm_num) n) x,
        Real.rpow_two, he]
    have hint : (∫ x, γ x * sumSquaresWithDrift X φn x) =
        ((2 : ℝ) ^ n) ^ 2 * ∫ x, γ x * ψ (G.dilate ((2 : ℝ) ^ n) x) := by
      simp_rw [hpoint]
      have hf : (fun x => γ x * (((2 : ℝ) ^ n) ^ 2 * ψ (G.dilate ((2 : ℝ) ^ n) x))) =
          (fun x => ((2 : ℝ) ^ n) ^ 2 * (γ x * ψ (G.dilate ((2 : ℝ) ^ n) x))) := by
        funext x; ring
      rw [hf, integral_const_mul]
    have hnzero : φn 0 = 0 := by change φ₁ (G.dilate ((2 : ℝ) ^ n) 0) = 0; rw [G2.dilate_zero, hφzero]
    rw [hint, hpoint 0, G2.dilate_zero, hnzero] at H
    have hp : 0 < ((2 : ℝ) ^ n) ^ 2 := pow_pos (pow_pos (by norm_num) n) 2
    nlinarith
  have ht := tendsto_integral_shrinking_test_zero G hγ ψ.contDiff.continuous ψ.hasCompactSupport
  have hconst : Tendsto (fun _ : ℕ => -α * ψ 0) atTop (𝓝 0) :=
    ht.congr' (Eventually.of_forall hpair)
  have hz : -α * ψ 0 = 0 := tendsto_nhds_unique tendsto_const_nhds hconst
  have hn : ψ 0 ≠ 0 := by rw [he]; exact hφop
  exact neg_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right hn)

end RothschildStein.H1
