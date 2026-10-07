-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.SecondWordBoundFromHalfRadius
public import RothschildStein.H3.QuasiballZeroSublevelDomain
public import RothschildStein.H3.GlobalWeakWordFromLocalScaleBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory
open scoped ENNReal
variable {n q : ℕ}

/-- The local half-radius estimate gives every global second weak
derivative with no input-norm remainder. -/
theorem exists_global_secondWord_of_halfRadiusEstimate
    (G : HomogeneousGroup n) (ν : G2.HomogeneousNorm G)
    (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞)
    (K : ℝ) (hK : 0 ≤ K) (hest : HalfRadiusEstimate G ν X p K)
    {u g : (Fin n → ℝ) → ℝ} (hu : MemLp u p (volume : Measure (Fin n → ℝ)))
    (hg : MemLp g p (volume : Measure (Fin n → ℝ)))
    (hlocal : ∀ R : ℝ, 0 < R →
      memSobolevX driftWeight X (quasiballDomain G ν 0 R) 2 p u ∧
      ∃ D : WeakDriftOperatorData X (quasiballDomain G ν 0 R) p u,
        D.operator =ᵐ[volume.restrict (G2.gaugeBall G ν 0 R)] g)
    (I : List (Fin (q + 1))) (hI : wordWeight driftWeight I = 2) :
    ∃ d : (Fin n → ℝ) → ℝ, hasWeakWordDeriv X ⊤ I u d ∧
      MemLp d p volume ∧ eLpNorm d p volume ≤
        ENNReal.ofReal (K * (eLpNorm g p volume).toReal) := by
  apply exists_global_weakWord_of_scaleInvariant_local_bounds X I ν ν.gauge.1 hp hpt hu
    (A := K * (eLpNorm g p volume).toReal) (B := K * (eLpNorm u p volume).toReal)
  · intro R hR
    have hfamily : I ∈ wordFamily driftWeight 2 := by
      simp only [S.mem_wordFamily_iff]
      omega
    have hh := (hlocal R hR).1.2 I hfamily
    simpa only [quasiballDomain_zero_eq_sublevel, continuousSublevelDomain, TopologicalSpace.Opens.coe_mk] using hh
  · intro R hR
    obtain ⟨hloc, D, hop⟩ := hlocal R hR
    have hb := secondWord_bound_of_halfRadiusEstimate G ν X p K hK hest hu hg hR hloc D hop I hI
    have he : K * ((eLpNorm g p volume).toReal + R⁻¹ ^ 2 * (eLpNorm u p volume).toReal) =
        K * (eLpNorm g p volume).toReal + (K * (eLpNorm u p volume).toReal) * R⁻¹ ^ 2 := by ring
    rw [he] at hb
    simpa only [quasiballDomain_zero_eq_sublevel] using hb

end RothschildStein.H3
