-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.QuasiballDomain
public import RothschildStein.S.Sobolev

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set TopologicalSpace
open scoped ENNReal

/-- Increasing a quasiball radius increases its open domain. -/
theorem quasiballDomain_subset_of_le {n : ℕ} (G : HomogeneousGroup n)
    (ν : G2.HomogeneousNorm G) (x₀ : Fin n → ℝ) {t s : ℝ} (hts : t ≤ s) :
    (quasiballDomain G ν x₀ t : Set (Fin n → ℝ)) ⊆ quasiballDomain G ν x₀ s := by
  intro x hx
  change G2.gaugeDistance G ν x x₀ < t at hx
  change G2.gaugeDistance G ν x x₀ < s
  exact hx.trans_le hts

/-- Local Sobolev data restrict to any smaller concentric quasiball. -/
theorem memSobolevX_quasiball_restrict {n m : ℕ} (G : HomogeneousGroup n)
    (ν : G2.HomogeneousNorm G) (x₀ : Fin n → ℝ) {t s : ℝ} (hts : t ≤ s)
    (w : Fin m → ℕ+) (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (k : ℕ) (p : ℝ≥0∞) (u : (Fin n → ℝ) → ℝ)
    (hu : memSobolevX w X (quasiballDomain G ν x₀ s) k p u) :
    memSobolevX w X (quasiballDomain G ν x₀ t) k p u :=
  S.memSobolevX_restrict w X _ _ (quasiballDomain_subset_of_le G ν x₀ hts) hu

end RothschildStein.H3
