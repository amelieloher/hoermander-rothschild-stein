-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Bridge.BoundedSquareIntegrableSlices
public import HeatKernel.Definitions.IsLocalWeakSolution
import Mathlib.Tactic.Linter

/-! # Space-time square integrability of the value in the parabolic weak predicate -/

@[expose] public section
open Set MeasureTheory TopologicalSpace RothschildStein
namespace HeatKernel

/-- The value of a local weak solution is square integrable on each compact cylinder. -/
theorem IsLocalWeakSolution.memLp_two_on_compact_cylinder {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (a : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ)
    (I : Opens ℝ) (U : Opens (Fin N → ℝ))
    {u : ℝ → (Fin N → ℝ) → ℝ}
    (hu : IsLocalWeakSolution G hq hqpos hw hspan a I U u)
    {J : Set ℝ} {K : Set (Fin N → ℝ)}
    (hJ : IsCompact J) (hJI : J ⊆ (I : Set ℝ))
    (hK : IsCompact K) (hKU : K ⊆ (U : Set (Fin N → ℝ))) :
    MemLp (fun z : ℝ × (Fin N → ℝ) => u z.1 z.2) 2 (volume.restrict (J ×ˢ K)) := by
  obtain ⟨hm, _, _, hbound, _⟩ := hu
  let : IsFiniteMeasure (volume.restrict J) := ⟨by simpa using hJ.measure_lt_top⟩
  have hmJK := hm.mono_measure (Measure.restrict_mono (prod_mono hJI hKU) le_rfl)
  have hmp : AEStronglyMeasurable (fun z : ℝ × (Fin N → ℝ) => u z.1 z.2)
      ((volume.restrict J).prod (volume.restrict K)) := by
    simpa only [Measure.prod_restrict, Measure.volume_eq_prod] using hmJK
  have h := memLp_two_prod_of_essSup_slice_lt_top hmp (hbound J K hJ hJI hK hKU).1
  simpa only [Measure.prod_restrict, Measure.volume_eq_prod] using h

end HeatKernel
