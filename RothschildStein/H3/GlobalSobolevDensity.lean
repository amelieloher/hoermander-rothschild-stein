-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.ExpandingCutoffSobolev
public import RothschildStein.H3.SobolevZeroDiagonal
public import RothschildStein.H3.SobolevZeroApproximation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped Topology ENNReal
namespace RothschildStein.H3

/-- Global homogeneous Sobolev functions have compact smooth test
approximations in the literal full weighted Sobolev norm (BB Theorem 3.49, p. 123). -/
theorem memSobolevXZero_global {N q : ℕ}
    (G : HomogeneousGroup N) (H : H1.StandingHypotheses G q)
    (ν : G2.HomogeneousNorm G) (hν : ν.Smooth)
    (k : ℕ) {p : ℝ} (hp : 1 ≤ p) {u : (Fin N → ℝ) → ℝ}
    (hu : memSobolevX driftWeight H.fields ⊤ k (ENNReal.ofReal p) u) :
    memSobolevXZero driftWeight H.fields ⊤ k (ENNReal.ofReal p) u := by
  have hp' : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hp
  let hpFact : Fact (1 ≤ ENNReal.ofReal p) := ⟨hp'⟩
  let φ : ℕ → TestFunction (⊤ : Opens (Fin N → ℝ)) ℝ (⊤ : ℕ∞) := fun j =>
    ⟨smoothQuasiballCutoff G ν 0 ((j : ℝ)+1) (2*((j : ℝ)+1)),
      smoothQuasiballCutoff_contDiff G ν hν 0 (by positivity) (by nlinarith [Nat.cast_nonneg (α := ℝ) j]),
      smoothQuasiballCutoff_compact G ν 0 (by nlinarith [Nat.cast_nonneg (α := ℝ) j]), subset_univ _⟩
  apply memSobolevXZero_of_approximating_zero driftWeight H.fields ⊤
    (fun i => (H.fields_smooth G i).contDiffOn) k (ENNReal.ofReal p) hp' hu
    (fun j x => u x * φ j x)
    (fun j => S.memSobolevXZero_mul_test driftWeight H.fields ⊤
      (fun i => (H.fields_smooth G i).contDiffOn) k ENNReal.ofReal_ne_top hu (φ j))
  have ht := tendsto_expandingCutoff_sobolevXENorm G H ν hν k hp hu
  have hR : Tendsto (fun j : ℕ => (j : ℝ)+1) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    obtain ⟨n,hn⟩ := exists_nat_gt b
    filter_upwards [eventually_ge_atTop n] with j hj
    have hc : (n : ℝ) ≤ j := by exact_mod_cast hj
    linarith
  exact ht.comp hR

/-- Global Sobolev density follows from homogeneity and compact Sobolev
approximation. -/
theorem exists_sobolevWordApproximation_global {N q : ℕ}
    (G : HomogeneousGroup N) (H : H1.StandingHypotheses G q)
    (ν : G2.HomogeneousNorm G) (hν : ν.Smooth)
    {p : ℝ} (hp : 1 ≤ p) [Fact (1 ≤ ENNReal.ofReal p)]
    {u : (Fin N → ℝ) → ℝ}
    (hu : memSobolevX driftWeight H.fields ⊤ 2 (ENNReal.ofReal p) u) :
    Nonempty (SobolevWordApproximation driftWeight H.fields (ENNReal.ofReal p) u) :=
  exists_sobolevWordApproximation_of_memSobolevXZero driftWeight H.fields
    (H.fields_smooth G) (memSobolevXZero_global G H ν hν 2 hp hu)

/-- Global word density in the ENNReal exponent interface used by the
regularity estimates; the proved smooth homogeneous norm supplies cutoffs. -/
theorem exists_sobolevWordApproximation_global_ennreal {N q : ℕ}
    (G : HomogeneousGroup N) (H : H1.StandingHypotheses G q)
    {p : ℝ≥0∞} [Fact (1 ≤ p)] (hpt : p ≠ ⊤) (hp : 1 ≤ p.toReal)
    {u : (Fin N → ℝ) → ℝ}
    (hu : memSobolevX driftWeight H.fields ⊤ 2 p u) :
    Nonempty (SobolevWordApproximation driftWeight H.fields p u) := by
  have hp' : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p.toReal := by
    simpa only [ENNReal.ofReal_toReal hpt] using (Fact.out : 1 ≤ p)
  let hpRealFact : Fact (1 ≤ ENNReal.ofReal p.toReal) := ⟨hp'⟩
  have hu' : memSobolevX driftWeight H.fields ⊤ 2 (ENNReal.ofReal p.toReal) u := by
    simpa only [ENNReal.ofReal_toReal hpt] using hu
  simpa only [ENNReal.ofReal_toReal hpt] using
    exists_sobolevWordApproximation_global G H (G2.smoothNorm G)
      (G2.smoothNorm_smooth G) hp hu'

end RothschildStein.H3
