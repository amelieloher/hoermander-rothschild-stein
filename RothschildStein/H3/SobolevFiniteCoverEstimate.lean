-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.FiniteCoverSobolevNorm
public import RothschildStein.H3.SobolevFixedNormEstimate
public import RothschildStein.H3.WeakDriftOperatorRestriction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory TopologicalSpace
open scoped ENNReal BigOperators

/-- a finite half-ball cover yields the interior fixed
Sobolev estimate, with its geometric constant explicitly counted. -/
theorem finite_cover_estimate_of_halfRadius {n q : ℕ} {ι : Type*}
    (G : HomogeneousGroup n) (ν : G2.HomogeneousNorm G)
    (X : Fin (q+1) → (Fin n → ℝ) → (Fin n → ℝ))
    (Ω U : Opens (Fin n → ℝ)) (hU : (U : Set (Fin n → ℝ)) ⊆ Ω)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (A : ℝ) (hA : 0 ≤ A)
    (hest : HalfRadiusEstimate G ν X p A)
    (s : Finset ι) (centers : ι → Fin n → ℝ) (r : ℝ) (hr : 0 < r)
    (hballs : ∀ i ∈ s, (quasiballDomain G ν (centers i) r : Set (Fin n → ℝ)) ⊆ Ω)
    (hcover : ∀ x ∈ U, ∃ i ∈ s, x ∈ quasiballDomain G ν (centers i) (r/2))
    (u : (Fin n → ℝ) → ℝ) (hu : memSobolevX driftWeight X Ω 2 p u)
    (D : WeakDriftOperatorData X Ω p u) :
    (sobolevXENorm driftWeight X U 2 p u).toReal ≤
      (s.card : ℝ)*((wordFamily (driftWeight (q := q)) 2).card : ℝ)*(1+r+r^2)*A*
        ((eLpNorm D.operator p (volume.restrict (Ω : Set (Fin n → ℝ)))).toReal+
          r⁻¹^2*(eLpNorm u p (volume.restrict (Ω : Set (Fin n → ℝ)))).toReal) := by
  classical
  have hhalf : ∀ i ∈ s, (quasiballDomain G ν (centers i) (r/2) : Set (Fin n → ℝ)) ⊆ Ω := by
    intro i hi
    exact (quasiballDomain_subset_of_le G ν (centers i) (show r/2 ≤ r by linarith)).trans (hballs i hi)
  have hc : 0 ≤ ((wordFamily (driftWeight (q := q)) 2).card : ℝ)*(1+r+r^2)*A := by positivity
  have hlocal : ∀ i ∈ s,
      (sobolevXENorm driftWeight X (quasiballDomain G ν (centers i) (r/2)) 2 p u).toReal ≤
        ((wordFamily (driftWeight (q := q)) 2).card : ℝ)*(1+r+r^2)*A*
          ((eLpNorm D.operator p (volume.restrict (Ω : Set (Fin n → ℝ)))).toReal+
            r⁻¹^2*(eLpNorm u p (volume.restrict (Ω : Set (Fin n → ℝ)))).toReal) := by
    intro i hi
    have hb := fixed_norm_estimate_of_halfRadius G ν X p A hest (centers i) r hr u
      (S.memSobolevX_restrict driftWeight X Ω _ (hballs i hi) hu)
      (D.restrict _ (hballs i hi))
    have hop := D.restrict_operator_realNorm_le _ (hballs i hi)
    have hin := ENNReal.toReal_mono hu.1.eLpNorm_ne_top
      (eLpNorm_mono_measure u (Measure.restrict_mono_set volume (hballs i hi)))
    have hsum := add_le_add hop (mul_le_mul_of_nonneg_left hin (sq_nonneg r⁻¹))
    have hmul := mul_le_mul_of_nonneg_left hsum hc
    exact hb.trans (by simpa only [quasiballDomain, Opens.coe_mk] using hmul)
  have hb := sobolevXENorm_toReal_le_finite_open_cover driftWeight X Ω U s
    (fun i => quasiballDomain G ν (centers i) (r/2)) hU hhalf hcover 2 p hp u hu
  exact hb.trans (by
    simpa only [Finset.sum_const, nsmul_eq_mul, mul_assoc] using Finset.sum_le_sum hlocal)

end RothschildStein.H3
