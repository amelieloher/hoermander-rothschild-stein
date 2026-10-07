-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.HalfRadiusConditional
public import RothschildStein.H3.QuasiballDomainRestriction
public import RothschildStein.H3.WeakWordWeightCases

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set TopologicalSpace MeasureTheory
open scoped ENNReal BigOperators
namespace RothschildStein.H3

/-- The exact fixed first-order filter consists of the horizontal
singletons, each with multiplicity one. -/
theorem sum_drift_weight_one_family {q : ℕ}
    (f : List (Fin (q + 1)) → ℝ≥0∞) :
    (∑ I ∈ (wordFamily (driftWeight (q := q)) 2).filter
      (fun I => wordWeight driftWeight I = 1), f I) = ∑ i : Fin q, f [i.succ] := by
  classical
  let e := fun i : Fin q => [i.succ]
  have hinj : Function.Injective e := by
    intro i j h
    simpa [e] using h
  have hs : (wordFamily (driftWeight (q := q)) 2).filter
      (fun I => wordWeight driftWeight I = 1) = (Finset.univ : Finset (Fin q)).image e := by
    ext I
    rw [Finset.mem_filter, S.mem_wordFamily_iff, Finset.mem_image]
    constructor
    · rintro ⟨_, hw⟩
      obtain ⟨i, rfl⟩ := drift_word_weight_one I hw
      exact ⟨i, Finset.mem_univ _, rfl⟩
    · rintro ⟨i, _, rfl⟩
      simp [e, wordWeight, driftWeight]
  rw [hs, Finset.sum_image (fun a _ b _ h => hinj h)]

/-- Convert the actual real half-radius
estimate to the literal fixed extended-real weighted sum. All norm
finiteness is derived from the actual Sobolev membership. -/
theorem halfRadius_frozen_ennreal_estimate {N q : ℕ}
    (G : HomogeneousGroup N) (ν : G2.HomogeneousNorm G)
    (X : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ))
    (p : ℝ≥0∞) {A : ℝ} (hA : 0 ≤ A) (hest : HalfRadiusEstimate G ν X p A)
    (z : Fin N → ℝ) {r : ℝ} (hr : 0 < r) (u : (Fin N → ℝ) → ℝ)
    (hu : memSobolevX driftWeight X (quasiballDomain G ν z r) 2 p u)
    (D : WeakDriftOperatorData X (quasiballDomain G ν z r) p u) :
    (∑ I ∈ (wordFamily (driftWeight (q := q)) 2).filter
      (fun I => wordWeight driftWeight I = 2),
        weakWordENorm X (quasiballDomain G ν z (r / 2)) I p u) +
      ENNReal.ofReal r⁻¹ * (∑ I ∈ (wordFamily (driftWeight (q := q)) 2).filter
        (fun I => wordWeight driftWeight I = 1),
          weakWordENorm X (quasiballDomain G ν z (r / 2)) I p u) +
      ENNReal.ofReal (r⁻¹ ^ 2) * eLpNorm u p (volume.restrict (G2.gaugeBall G ν z (r / 2))) ≤
    ENNReal.ofReal A * (eLpNorm D.operator p (volume.restrict (G2.gaugeBall G ν z r)) +
      ENNReal.ofReal (r⁻¹ ^ 2) * eLpNorm u p (volume.restrict (G2.gaugeBall G ν z r))) := by
  rw [sum_drift_weight_one_family]
  change driftSecondWeakENorm X (quasiballDomain G ν z (r / 2)) p u +
      ENNReal.ofReal r⁻¹ * horizontalWeakENorm X (quasiballDomain G ν z (r / 2)) p u +
      ENNReal.ofReal (r⁻¹ ^ 2) * eLpNorm u p (volume.restrict (G2.gaugeBall G ν z (r / 2))) ≤ _
  have hv := memSobolevX_quasiball_restrict G ν z (by linarith : r / 2 ≤ r) driftWeight X 2 p u hu
  have h2 := driftSecondWeakENorm_lt_top X _ p u hv
  have h1 := horizontalWeakENorm_lt_top X _ p u hv
  have h0 := hv.1.eLpNorm_ne_top
  have hF := D.operator_memLp.eLpNorm_ne_top
  have hU := hu.1.eLpNorm_ne_top
  have hi : 0 ≤ r⁻¹ := inv_nonneg.mpr hr.le
  have hi2 : 0 ≤ r⁻¹ ^ 2 := sq_nonneg _
  apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
  rw [ENNReal.toReal_add (by finiteness) (by finiteness),
    ENNReal.toReal_add (by finiteness) (by finiteness)]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hi,
    ENNReal.toReal_ofReal hi2, ENNReal.toReal_ofReal hA]
  rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hi2]
  exact hest z r hr u hu D

end RothschildStein.H3
