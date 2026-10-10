-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Bridge.ParabolicEnergyGradient
public import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Tactic.Linter

/-! # Compact time exhaustion for spatial square integrability -/

@[expose] public section
open Set MeasureTheory TopologicalSpace RothschildStein
namespace HeatKernel

/-- An almost-everywhere property on every compact subset of an open time set
holds almost everywhere on the whole time set. -/
theorem ae_restrict_open_of_forall_compact (I : Opens ℝ) {P : ℝ → Prop}
    (hP : ∀ J : Set ℝ, IsCompact J → J ⊆ (I : Set ℝ) →
      ∀ᵐ t ∂(volume.restrict J), P t) :
    ∀ᵐ t ∂(volume.restrict (I : Set ℝ)), P t := by
  let : LocallyCompactSpace (I : Set ℝ) := I.isOpen.isOpenEmbedding_subtypeVal.locallyCompactSpace
  let K : ℕ → Set (I : Set ℝ) := compactCovering (I : Set ℝ)
  let J : ℕ → Set ℝ := fun n => Subtype.val '' K n
  have hcover : ⋃ n, J n = (I : Set ℝ) := by
    ext t
    constructor
    · intro ht
      obtain ⟨n, hn⟩ := mem_iUnion.mp ht
      obtain ⟨y, _, rfl⟩ := hn
      exact y.property
    · intro ht
      obtain ⟨n, hn⟩ := exists_mem_compactCovering (⟨t, ht⟩ : (I : Set ℝ))
      exact mem_iUnion.mpr ⟨n, ⟨⟨t, ht⟩, hn, rfl⟩⟩
  rw [← hcover, ae_restrict_iUnion_iff]
  intro n
  apply hP (J n) ((isCompact_compactCovering (I : Set ℝ) n).image continuous_subtype_val)
  rintro t ⟨y, _, rfl⟩
  exact y.property

/-- The compact-cylinder bounds in the parabolic weak predicate give square
integrability of the value and its gradient on almost every spatial slice. -/
theorem IsLocalWeakSolution.exists_square_integrable_compact_slices {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (a : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ)
    (I : Opens ℝ) (U : Opens (Fin N → ℝ))
    {u : ℝ → (Fin N → ℝ) → ℝ}
    (hu : IsLocalWeakSolution G hq hqpos hw hspan a I U u) :
    ∃ g : Fin q → ℝ → (Fin N → ℝ) → ℝ,
      (∀ᵐ t ∂(volume.restrict (I : Set ℝ)), ∀ i,
        hasWeakWordDeriv (G.horizontalFields hq) U [i] (u t) (g i t)) ∧
      ∀ K : Set (Fin N → ℝ), IsCompact K → K ⊆ (U : Set (Fin N → ℝ)) →
        ∀ᵐ t ∂(volume.restrict (I : Set ℝ)),
          MemLp (u t) 2 (volume.restrict K) ∧ ∀ i, MemLp (g i t) 2 (volume.restrict K) := by
  obtain ⟨_, g, hg, hbound, _⟩ := hu
  refine ⟨g, hg, ?_⟩
  intro K hK hKU
  apply ae_restrict_open_of_forall_compact I
  intro J hJ hJI
  have hval := (hbound J K hJ hJI hK hKU).1
  have hgrad : ∀ᵐ t ∂(volume.restrict J), ∀ i, MemLp (g i t) 2 (volume.restrict K) := by
    rw [ae_all_iff]
    intro i
    apply ae_memLp_two_slice_restrict (f := fun z => g i z.1 z.2)
    simpa only [Measure.volume_eq_prod] using (hbound J K hJ hJI hK hKU).2 i
  filter_upwards [ENNReal.ae_le_essSup (μ := volume.restrict J)
    (fun t => eLpNorm (u t) 2 (volume.restrict K)), hgrad] with t ht hgt
  exact ⟨ht.trans_lt hval, hgt⟩

end HeatKernel
