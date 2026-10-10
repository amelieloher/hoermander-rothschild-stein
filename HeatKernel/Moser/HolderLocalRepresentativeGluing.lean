-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.HolderMeasuredDomain
public import Mathlib.Topology.Compactness.Lindelof
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.Topology.ContinuousOn

/-! # Gluing local continuous representatives on a countable open cover -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open MeasureTheory Set Filter
namespace HeatKernel

/-- Continuous representatives of the same measurable function agree on open
intersections. A countable open cover therefore glues them to one continuous
almost-everywhere equal function, without a global boundedness assumption. -/
theorem exists_continuous_representative_of_countable_open_cover
    {A I : Type*} [TopologicalSpace A] [MeasurableSpace A] [Countable I]
    (μ : Measure A) [μ.IsOpenPosMeasure] (Q : I → Set A)
    (hopen : ∀ i, IsOpen (Q i)) (hcover : ∀ x, ∃ i, x ∈ Q i)
    (u : A → ℝ) (f : I → A → ℝ)
    (hf : ∀ i, ContinuousOn (f i) (Q i))
    (he : ∀ i, f i =ᵐ[μ.restrict (Q i)] u) :
    ∃ v : A → ℝ, Continuous v ∧ v =ᵐ[μ] u ∧ ∀ i, EqOn v (f i) (Q i) := by
  have hoverlap (i j : I) : EqOn (f i) (f j) (Q i ∩ Q j) := by
    have hei : f i =ᵐ[μ.restrict (Q i ∩ Q j)] u :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_left (he i)
    have hej : f j =ᵐ[μ.restrict (Q i ∩ Q j)] u :=
      ae_restrict_of_ae_restrict_of_subset inter_subset_right (he j)
    exact Measure.eqOn_open_of_ae_eq (hei.trans hej.symm)
      ((hopen i).inter (hopen j))
      ((hf i).mono inter_subset_left) ((hf j).mono inter_subset_right)
  let idx : A → I := fun x => Classical.choose (hcover x)
  have hidx (x : A) : x ∈ Q (idx x) := Classical.choose_spec (hcover x)
  let v : A → ℝ := fun x => f (idx x) x
  have hvlocal (i : I) : EqOn v (f i) (Q i) := by
    intro x hx
    exact hoverlap (idx x) i ⟨hidx x, hx⟩
  have hv : Continuous v := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact ((hf (idx x)).congr (hvlocal (idx x))).continuousAt
      ((hopen (idx x)).mem_nhds (hidx x))
  have heall : ∀ᵐ x ∂μ, ∀ i, x ∈ Q i → f i x = u x :=
    ae_all_iff.mpr (fun i => ae_imp_of_ae_restrict (he i))
  refine ⟨v, hv, ?_, hvlocal⟩
  filter_upwards [heall] with x hx
  exact hx (idx x) (hidx x)

/-- Local continuous representatives on an open domain give one continuous
representative on the whole domain. Second countability supplies a countable
subcover, so the almost-everywhere assertions glue as well. -/
theorem exists_continuousOn_representative_of_local_representatives
    {A : Type*} [TopologicalSpace A] [SecondCountableTopology A]
    [MeasurableSpace A] [BorelSpace A] (μ : Measure A) [μ.IsOpenPosMeasure]
    (Ω : Set A) (hΩ : IsOpen Ω) (u : A → ℝ)
    (hlocal : ∀ x ∈ Ω, ∃ (Q : Set A) (f : A → ℝ),
      IsOpen Q ∧ x ∈ Q ∧ ContinuousOn f Q ∧ f =ᵐ[μ.restrict Q] u) :
    ∃ v : A → ℝ, ContinuousOn v Ω ∧ v =ᵐ[μ.restrict Ω] u := by
  classical
  choose Q f hQ hxQ hf heq using fun x : Ω => hlocal x.val x.property
  let Q' : Ω → Set Ω := fun x => Subtype.val ⁻¹' Q x
  have hopen (x : Ω) : IsOpen (Q' x) := (hQ x).preimage continuous_subtype_val
  have hcover : (univ : Set Ω) ⊆ ⋃ x, Q' x := by
    intro x _
    exact mem_iUnion.mpr ⟨x, hxQ x⟩
  obtain ⟨J, hJ, hJcover⟩ := isLindelof_univ.elim_countable_subcover Q' hopen hcover
  let : Countable J := hJ.to_subtype
  let μΩ := μ.comap (Subtype.val : Ω → A)
  have he := hΩ.isOpenEmbedding_subtypeVal
  let : μΩ.IsOpenPosMeasure := Measure.IsOpenPosMeasure.comap μ he
  have hcover' (x : Ω) : ∃ j : J, x ∈ Q' j.val := by
    obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.mp (hJcover (mem_univ x))
    exact ⟨⟨j, hj⟩, hxj⟩
  have heq' (j : J) : (fun x : Ω => f j.val x.val) =ᵐ[μΩ.restrict (Q' j.val)]
      (fun x => u x.val) := by
    rw [show μΩ.restrict (Q' j.val) =
      (μ.restrict (Q j.val)).comap (Subtype.val : Ω → A) from
        (he.measurableEmbedding.comap_restrict μ (Q j.val)).symm]
    exact ae_comap_of_ae he.measurableEmbedding (heq j.val)
  obtain ⟨v, hv, heqv, _⟩ := exists_continuous_representative_of_countable_open_cover
    μΩ (fun j : J => Q' j.val) (fun j => hopen j.val) hcover'
    (fun x : Ω => u x.val) (fun j x => f j.val x.val)
    (fun j => (hf j.val).comp continuous_subtype_val.continuousOn (fun _ hx => hx)) heq'
  obtain ⟨w, hw, heqw, _⟩ := exists_representative_on_embedding_range
    he.isEmbedding he.measurableEmbedding μ u v hv heqv
  rw [Subtype.range_coe] at hw heqw
  exact ⟨w, hw, heqw⟩

end HeatKernel
