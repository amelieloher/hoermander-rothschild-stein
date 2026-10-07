-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory
variable {X : Type*} [MeasurableSpace X]

/-- Select one representative on a countable cover; compatibility is proved
almost everywhere rather than imposed pointwise. -/
def coverRepresentative (s : ℕ → Set X) (g : ℕ → X → ℝ)
    (hcover : ∀ x, ∃ n, x ∈ s n) (x : X) : ℝ :=
  g (Classical.choose (hcover x)) x

/-- Pairwise agreement on overlaps makes the selected function agree with
every member of the cover almost everywhere on that member. -/
theorem coverRepresentative_ae_eq (μ : Measure X) (s : ℕ → Set X)
    (g : ℕ → X → ℝ) (hcover : ∀ x, ∃ n, x ∈ s n)
    (hs : ∀ n, MeasurableSet (s n))
    (hcompat : ∀ i j, g i =ᵐ[μ.restrict (s i ∩ s j)] g j) (n : ℕ) :
    coverRepresentative s g hcover =ᵐ[μ.restrict (s n)] g n := by
  have hall : ∀ᵐ x ∂μ, ∀ i : ℕ, x ∈ s i ∩ s n → g i x = g n x := by
    apply ae_all_iff.mpr
    intro i
    exact (ae_restrict_iff' ((hs i).inter (hs n))).mp (hcompat i n)
  apply (ae_restrict_iff' (hs n)).mpr
  filter_upwards [hall] with x hx hxn
  exact hx (Classical.choose (hcover x)) ⟨Classical.choose_spec (hcover x), hxn⟩

/-- The selected compatible representative is globally AE strongly measurable
if each local representative has that property on its patch. -/
theorem coverRepresentative_aestronglyMeasurable (μ : Measure X) (s : ℕ → Set X)
    (g : ℕ → X → ℝ) (hcover : ∀ x, ∃ n, x ∈ s n)
    (hs : ∀ n, MeasurableSet (s n))
    (hcompat : ∀ i j, g i =ᵐ[μ.restrict (s i ∩ s j)] g j)
    (hg : ∀ n, AEStronglyMeasurable (g n) (μ.restrict (s n))) :
    AEStronglyMeasurable (coverRepresentative s g hcover) μ := by
  have hu : (⋃ n, s n) = univ := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨n, hn⟩ := hcover x
    exact mem_iUnion.mpr ⟨n, hn⟩
  have hm : AEStronglyMeasurable (coverRepresentative s g hcover)
      (μ.restrict (⋃ n, s n)) := AEStronglyMeasurable.iUnion (fun n =>
    (hg n).congr (coverRepresentative_ae_eq μ s g hcover hs hcompat n).symm)
  simpa only [hu, Measure.restrict_univ] using hm

end RothschildStein.H3
