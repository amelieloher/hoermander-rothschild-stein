-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.ContinuousSublevelDomain
public import RothschildStein.H3.WeakCoverRepresentative
public import RothschildStein.H3.WeakWordGlobalFromCompactPatches
public import RothschildStein.H3.ScaleInvariantLpExhaustion
public import RothschildStein.S.Sobolev

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory TopologicalSpace
open scoped ENNReal
variable {n m : ℕ}

/-- Local weak derivatives and the exact scale-invariant second-word
estimate produce an actual global weak derivative with the sharp Lp bound. -/
theorem exists_global_weakWord_of_scaleInvariant_local_bounds
    (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)) (I : List (Fin m))
    (ν : (Fin n → ℝ) → ℝ) (hν : Continuous ν)
    {f : (Fin n → ℝ) → ℝ} {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞)
    (hf : MemLp f p (volume : Measure (Fin n → ℝ)))
    (hlocal : ∀ R : ℝ, 0 < R → ∃ g : (Fin n → ℝ) → ℝ,
      hasWeakWordDeriv X (continuousSublevelDomain ν hν R) I f g ∧
      MemLp g p (volume.restrict {x | ν x < R})) (A B : ℝ)
    (hb : ∀ R : ℝ, 0 < R →
      weakWordENorm X (continuousSublevelDomain ν hν (R / 2)) I p f ≤
        ENNReal.ofReal (A + B * (R⁻¹) ^ 2)) :
    ∃ g : (Fin n → ℝ) → ℝ, hasWeakWordDeriv X ⊤ I f g ∧
      MemLp g p volume ∧ eLpNorm g p volume ≤ ENNReal.ofReal A := by
  classical
  let U : ℕ → Opens (Fin n → ℝ) := fun j => continuousSublevelDomain ν hν ((j : ℝ) + 1)
  have hloc (j : ℕ) := hlocal ((j : ℝ) + 1) (by positivity)
  let gs : ℕ → (Fin n → ℝ) → ℝ := fun j => Classical.choose (hloc j)
  have hgs (j : ℕ) : hasWeakWordDeriv X (U j) I f (gs j) ∧
      MemLp (gs j) p (volume.restrict (U j : Set (Fin n → ℝ))) :=
    Classical.choose_spec (hloc j)
  have hcover : ∀ x, ∃ j : ℕ, x ∈ (U j : Set (Fin n → ℝ)) := by
    intro x
    obtain ⟨j, hj⟩ := exists_nat_gt (ν x)
    refine ⟨j, ?_⟩
    change ν x < (j : ℝ) + 1
    linarith
  let g := coverRepresentative (fun j => (U j : Set (Fin n → ℝ))) gs hcover
  have hgU (j : ℕ) : hasWeakWordDeriv X (U j) I f g :=
    coverRepresentative_hasWeakWordDeriv X I U f gs hcover (fun j => (hgs j).1) j
  have hgR (R : ℝ) : hasWeakWordDeriv X (continuousSublevelDomain ν hν R) I f g := by
    obtain ⟨j, hj⟩ := exists_nat_gt R
    apply S.hasWeakWordDeriv_restrict X (U j) _ _ (hgU j)
    intro x hx
    change ν x < (j : ℝ) + 1
    change ν x < R at hx
    linarith
  have hgm : AEStronglyMeasurable g (volume : Measure (Fin n → ℝ)) :=
    coverRepresentative_aestronglyMeasurable volume (fun j => (U j : Set (Fin n → ℝ)))
      gs hcover (fun j => (U j).isOpen.measurableSet)
      (weakWord_cover_compatible X I U f gs (fun j => (hgs j).1))
      (fun j => (hgs j).2.aestronglyMeasurable)
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le (by norm_num) hp)
  obtain ⟨hgp, hgn⟩ := memLp_of_scaleInvariant_halfRadius_bounds volume ν g hp0 hpt hgm A B
    (fun R hR => by
      change eLpNorm g p (volume.restrict
        (continuousSublevelDomain ν hν (R / 2) : Set (Fin n → ℝ))) ≤ _
      rw [← S.weakWordENorm_eq X (continuousSublevelDomain ν hν (R / 2)) I p f g (hgR _)]
      exact hb R hR)
  refine ⟨g, ?_, hgp, hgn⟩
  apply hasWeakWordDeriv_global_of_compact_patches X I hp hf hgp
  intro K hK
  obtain ⟨R, _, hKR⟩ := continuousSublevelDomain_compact_cofinal ν hν hK
  exact ⟨continuousSublevelDomain ν hν R, hKR, hgR R⟩

end RothschildStein.H3
