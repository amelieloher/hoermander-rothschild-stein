-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.ZeroCenteredPhiInterpolation
public import RothschildStein.H3.FirstWordBoundFromGlobalSecondWords
public import RothschildStein.H3.GlobalWeakWordFromUniformLocalBounds
public import RothschildStein.H3.LocalWeakWordBoundCofinality
public import RothschildStein.H3.QuasiballZeroSublevelDomain

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory TopologicalSpace
open scoped ENNReal
variable {n q : ℕ}

/-- Second-word representatives and interpolation give global first weak
derivatives with a fixed norm bound. -/
theorem exists_global_firstWord_of_secondWords_and_interpolation
    (G : HomogeneousGroup n) (ν : G2.HomogeneousNorm G)
    (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞)
    {u : (Fin n → ℝ) → ℝ} (hu : MemLp u p (volume : Measure (Fin n → ℝ)))
    (hlocal : ∀ R : ℝ, 0 < R → memSobolevX driftWeight X (quasiballDomain G ν 0 R) 2 p u)
    (B : ℝ) (hB : 0 ≤ B)
    (hwords : ∀ I : List (Fin (q + 1)), wordWeight driftWeight I = 2 →
      ∃ d : (Fin n → ℝ) → ℝ, hasWeakWordDeriv X ⊤ I u d ∧
        MemLp d p volume ∧ eLpNorm d p volume ≤ ENNReal.ofReal B)
    (cE δE : ℝ) (hcE : 0 ≤ cE) (hδE : 0 < δE)
    (hinterp : ZeroCenteredPhiInterpolation G ν X p u cE δE) (i : Fin q) :
    ∃ d : (Fin n → ℝ) → ℝ, hasWeakWordDeriv X ⊤ [i.succ] u d ∧
      MemLp d p volume ∧ eLpNorm d p volume ≤
        ENNReal.ofReal ((driftSecondWordFamily q).card * B / 2 +
          2 * cE * (eLpNorm u p volume).toReal) := by
  have hfamily : [i.succ] ∈ wordFamily driftWeight 2 := by
    simp [S.mem_wordFamily_iff, wordWeight, driftWeight, Fin.succ_ne_zero]
  have hl (r : ℝ) (hr : 0 < r) : ∃ d : (Fin n → ℝ) → ℝ,
      hasWeakWordDeriv X (continuousSublevelDomain ν ν.gauge.1 r) [i.succ] u d ∧
      MemLp d p (volume.restrict {x | ν x < r}) := by
    have hh := (hlocal r hr).2 [i.succ] hfamily
    simpa only [quasiballDomain_zero_eq_sublevel, continuousSublevelDomain, Opens.coe_mk] using hh
  let A := (driftSecondWordFamily q).card * B / 2 + 2 * cE * (eLpNorm u p volume).toReal
  have hlarge (r : ℝ) (hr : 0 < r) (hrad : δE⁻¹ ≤ r) :
      weakWordENorm X (continuousSublevelDomain ν ν.gauge.1 r) [i.succ] p u ≤ ENNReal.ofReal A := by
    have hR : 0 < 2 * r := by positivity
    have had := inverseRadius_interpolation_parameter hR hδE (by linarith : δE⁻¹ ≤ 2 * r)
    have hh := horizontalWeakENorm_halfRadius_bound_of_global_second_words G ν X hu B hB hwords hR
      (hlocal (2 * r) hR) cE hcE
      (hinterp (2 * r) hR (hlocal (2 * r) hR) (2 * r)⁻¹ had.1 had.2)
    have he : (2 * r) / 2 = r := by ring
    rw [he] at hh
    have hw : weakWordENorm X (quasiballDomain G ν 0 r) [i.succ] p u ≤
        horizontalWeakENorm X (quasiballDomain G ν 0 r) p u := by
      unfold horizontalWeakENorm
      exact Finset.single_le_sum
        (f := fun j : Fin q => weakWordENorm X (quasiballDomain G ν 0 r) [j.succ] p u)
        (fun _ _ => by positivity) (Finset.mem_univ i)
    simpa only [quasiballDomain_zero_eq_sublevel] using hw.trans hh
  have hb := weakWordENorm_uniform_of_large_sublevel_bounds X [i.succ] ν ν.gauge.1 u p A δE⁻¹
    (fun r hr => by obtain ⟨d, hw, _⟩ := hl r hr; exact ⟨d, hw⟩) hlarge
  exact exists_global_weakWord_of_uniform_local_bounds X [i.succ] ν ν.gauge.1 hp hpt hu hl A hb

end RothschildStein.H3
