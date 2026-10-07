-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.HolderTransferTopology
public import RothschildStein.G1.ControlSeparation
public import RothschildStein.G1.ControlledReparam
public import RothschildStein.G1.WeightedTriangle
public import RothschildStein.G1.ControlledBasics

/-!
# The truncated control metric on a Euclidean open set

H2's Campanato converse is stated on a metric space with a Borel measure. For the base `ℝⁿ` with
the control distance `d` (extended-valued, possibly infinite) we use the truncation
`min(1, d)` on a Euclidean open set `N ⊆ Ω` at whose points Euclidean convergence implies
convergence of `d` (`BaseData.close`; for `N = π(U)` this is the chart statement
`exists_controlDistance_lt_of_euclid_close`). The metric has the Euclidean subspace topology and the
Euclidean Borel structure and the measure is the restriction of Lebesgue measure to `N`; its balls
of radius `≤ 1` are the control balls.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Filter TopologicalSpace Metric
open scoped ENNReal Topology BigOperators
namespace RothschildStein.P2
variable {n k : ℕ} {w : Fin k → ℕ+} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)}

/-- The data for the truncated control metric: an open domain `Ω` with continuous fields, a
Euclidean open `N ⊆ Ω`, and `d(x, y) → 0` as `y → x` for `x ∈ N` (Euclidean topology finer than
the control topology on `N`). -/
structure BaseData (w : Fin k → ℕ+) (X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)) where
  Ω : Set (Fin n → ℝ)
  isOpen_Ω : IsOpen Ω
  cont : ∀ i, ContinuousOn (X i) Ω
  N : Set (Fin n → ℝ)
  isOpen_N : IsOpen N
  N_subset : N ⊆ Ω
  close : ∀ x ∈ N, ∀ ε : ℝ, 0 < ε → ∃ δ' : ℝ, 0 < δ' ∧ ∀ y, ‖y - x‖ < δ' →
    controlDistance Ω w X x y < ENNReal.ofReal ε

namespace BaseData
variable (D : BaseData w X)

/-- `close`, with also `y ∈ N` (`N` is open). -/
theorem close' (x : Fin n → ℝ) (hx : x ∈ D.N) (ε : ℝ) (hε : 0 < ε) :
    ∃ δ' : ℝ, 0 < δ' ∧ ∀ y, ‖y - x‖ < δ' →
      y ∈ D.N ∧ controlDistance D.Ω w X x y < ENNReal.ofReal ε := by
  obtain ⟨δ₁, hδ₁, h₁⟩ := D.close x hx ε hε
  obtain ⟨δ₂, hδ₂, h₂⟩ := Metric.isOpen_iff.mp D.isOpen_N x hx
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun y hy => ⟨h₂ ?_, h₁ y (hy.trans_le (min_le_left _ _))⟩⟩
  rw [mem_ball, dist_eq_norm]
  exact hy.trans_le (min_le_right _ _)

/-- The truncated control distance `min(1, d)` on `N`. -/
def tdist (x y : D.N) : ℝ := (min 1 (controlDistance D.Ω w X x.1 y.1)).toReal

theorem min_one_ne_top (a : ℝ≥0∞) : min 1 a ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (min_le_left _ _)

theorem tdist_lt_iff {x y : D.N} {ε : ℝ} (hε1 : ε ≤ 1) :
    D.tdist x y < ε ↔ controlDistance D.Ω w X x.1 y.1 < ENNReal.ofReal ε := by
  unfold tdist
  constructor
  · intro h
    have h1 : min 1 (controlDistance D.Ω w X x.1 y.1) < ENNReal.ofReal ε :=
      (ENNReal.lt_ofReal_iff_toReal_lt (min_one_ne_top _)).mpr h
    by_contra hcon
    exact absurd h1 (not_lt.mpr (le_min (ENNReal.ofReal_le_one.mpr hε1) (not_lt.mp hcon)))
  · intro h
    exact ENNReal.toReal_lt_of_lt_ofReal (lt_of_le_of_lt (min_le_right _ _) h)

theorem tdist_self (x : D.N) : D.tdist x x = 0 := by
  unfold tdist
  rw [G1.controlDistance_self w X (D.N_subset x.2)]
  simp

theorem tdist_comm (x y : D.N) : D.tdist x y = D.tdist y x := by
  unfold tdist
  rw [G1.controlDistance_symm]

theorem min_one_le_add {a b c : ℝ≥0∞} (h : a ≤ b + c) : min 1 a ≤ min 1 b + min 1 c := by
  rcases le_or_gt 1 b with hb | hb
  · calc min 1 a ≤ 1 := min_le_left _ _
      _ = min 1 b := (min_eq_left hb).symm
      _ ≤ _ := le_self_add
  rcases le_or_gt 1 c with hc | hc
  · calc min 1 a ≤ 1 := min_le_left _ _
      _ = min 1 c := (min_eq_left hc).symm
      _ ≤ _ := le_add_self
  · calc min 1 a ≤ a := min_le_right _ _
      _ ≤ b + c := h
      _ = min 1 b + min 1 c := by rw [min_eq_right hb.le, min_eq_right hc.le]

theorem tdist_triangle (x y z : D.N) : D.tdist x z ≤ D.tdist x y + D.tdist y z := by
  unfold tdist
  have h := min_one_le_add (G1.controlDistance_triangle D.Ω w X x.1 y.1 z.1)
  have h2 := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨min_one_ne_top _, min_one_ne_top _⟩) h
  rwa [ENNReal.toReal_add (min_one_ne_top _) (min_one_ne_top _)] at h2

theorem eq_of_tdist_eq_zero (x y : D.N) (h : D.tdist x y = 0) : x = y := by
  unfold tdist at h
  rcases (ENNReal.toReal_eq_zero_iff _).mp h with h0 | h0
  · have hd : controlDistance D.Ω w X x.1 y.1 = 0 := by
      by_contra hne
      have : 0 < min 1 (controlDistance D.Ω w X x.1 y.1) :=
        lt_min one_pos (pos_iff_ne_zero.mpr hne)
      exact absurd h0 this.ne'
    exact Subtype.ext ((G1.controlDistance_eq_zero_iff D.isOpen_Ω w X D.cont (D.N_subset x.2)).mp hd)
  · exact absurd h0 (min_one_ne_top _)

/-- The topology of the truncated control metric is the Euclidean subspace topology on `N`. -/
theorem isOpen_iff_tdist (s : Set D.N) :
    IsOpen s ↔ ∀ x ∈ s, ∃ ε > 0, ∀ y, D.tdist x y < ε → y ∈ s := by
  constructor
  · intro hs x hx
    obtain ⟨t, ht, rfl⟩ := isOpen_induced_iff.mp hs
    obtain ⟨ε₁, hε₁, hball⟩ := Metric.isOpen_iff.mp ht x.1 hx
    obtain ⟨r, hr, hclose⟩ := exists_norm_lt_of_controlDistance_lt (w := w) D.isOpen_Ω D.cont
      (isCompact_singleton (x := x.1)) (singleton_subset_iff.mpr (D.N_subset x.2)) hε₁
    refine ⟨min r 1, lt_min hr one_pos, fun y hy => ?_⟩
    have hd : controlDistance D.Ω w X x.1 y.1 < ENNReal.ofReal (min r 1) :=
      (D.tdist_lt_iff (min_le_right _ _)).mp hy
    have := hclose x.1 rfl y.1 (hd.trans_le (ENNReal.ofReal_le_ofReal (min_le_left _ _)))
    exact hball (by rwa [mem_ball, dist_eq_norm])
  · intro h
    rw [isOpen_iff_mem_nhds]
    intro x hx
    obtain ⟨ε, hε, hεs⟩ := h x hx
    obtain ⟨δ', hδ', hcl⟩ := D.close x.1 x.2 (min ε 1) (lt_min hε one_pos)
    rw [Metric.mem_nhds_iff]
    refine ⟨δ', hδ', fun y hy => hεs y ?_⟩
    have hy' : ‖y.1 - x.1‖ < δ' := by
      rw [mem_ball, Subtype.dist_eq, dist_eq_norm] at hy
      exact hy
    have h2 : D.tdist x y < min ε 1 := (D.tdist_lt_iff (min_le_right _ _)).mpr (hcl y.1 hy')
    exact lt_of_lt_of_le h2 (min_le_left _ _)

/-- The truncated control metric on `N`, with the Euclidean subspace topology. -/
@[instance_reducible]
def tdistMetric : MetricSpace D.N :=
  MetricSpace.ofDistTopology D.tdist D.tdist_self D.tdist_comm D.tdist_triangle
    D.isOpen_iff_tdist D.eq_of_tdist_eq_zero

end BaseData

/-- The carrier `N` of a `BaseData`, with the truncated control metric. -/
def BaseCarrier (D : BaseData w X) : Type := ↥D.N

instance baseCarrierMetricSpace (D : BaseData w X) : MetricSpace (BaseCarrier D) :=
  D.tdistMetric
instance baseCarrierMeasurableSpace (D : BaseData w X) : MeasurableSpace (BaseCarrier D) :=
  inferInstanceAs (MeasurableSpace ↥D.N)
instance baseCarrierBorelSpace (D : BaseData w X) : BorelSpace (BaseCarrier D) :=
  ⟨(inferInstance : BorelSpace ↥D.N).measurable_eq⟩

namespace BaseCarrier
variable {D : BaseData w X}

/-- The underlying point of `ℝⁿ`. -/
def val (x : BaseCarrier D) : Fin n → ℝ := Subtype.val (p := (· ∈ D.N)) x

/-- The carrier point of a point of `N`. -/
def mk (x : Fin n → ℝ) (hx : x ∈ D.N) : BaseCarrier D := ⟨x, hx⟩

theorem val_mk (x : Fin n → ℝ) (hx : x ∈ D.N) : (mk x hx : BaseCarrier D).val = x := rfl

theorem val_mem (x : BaseCarrier D) : x.val ∈ D.N := Subtype.property (p := (· ∈ D.N)) x

theorem continuous_val : Continuous (val : BaseCarrier D → Fin n → ℝ) := continuous_subtype_val

theorem measurable_val : Measurable (val : BaseCarrier D → Fin n → ℝ) := measurable_subtype_coe

theorem dist_eq (x y : BaseCarrier D) :
    dist x y = (min 1 (controlDistance D.Ω w X x.val y.val)).toReal := rfl

theorem dist_lt_iff {x y : BaseCarrier D} {r : ℝ} (hr1 : r ≤ 1) :
    dist x y < r ↔ controlDistance D.Ω w X x.val y.val < ENNReal.ofReal r :=
  D.tdist_lt_iff hr1

theorem mem_ball_iff {x y : BaseCarrier D} {r : ℝ} (hr1 : r ≤ 1) :
    y ∈ Metric.ball x r ↔ controlDistance D.Ω w X x.val y.val < ENNReal.ofReal r := by
  rw [mem_ball, dist_comm, dist_lt_iff hr1]

/-- The measure: Lebesgue measure restricted to `N`, as a measure on the carrier. -/
def measure (D : BaseData w X) : Measure (BaseCarrier D) :=
  Measure.comap (Subtype.val (p := (· ∈ D.N))) (volume : Measure (Fin n → ℝ))

theorem measure_apply (A : Set (BaseCarrier D)) :
    measure D A = volume (val '' A) :=
  (MeasurableEmbedding.subtype_coe D.isOpen_N.measurableSet).comap_apply volume A

instance isOpenPosMeasure_measure (D : BaseData w X) : Measure.IsOpenPosMeasure (measure D) :=
  ⟨fun U hU hne => by
    rw [measure_apply]
    have hopen : IsOpen (val '' U) := D.isOpen_N.isOpenMap_subtype_val U hU
    obtain ⟨x, hx⟩ := hne
    exact (hopen.measure_pos volume ⟨x.val, x, hx, rfl⟩).ne'⟩

/-- Control balls of radius `≤ 1` inside `N` are the metric balls of the carrier. -/
theorem image_ball {x : BaseCarrier D} {r : ℝ} (hr1 : r ≤ 1)
    (hsub : rsBall D.Ω w X x.val r ⊆ D.N) :
    val '' Metric.ball x r = rsBall D.Ω w X x.val r := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨D.N_subset z.val_mem, (mem_ball_iff hr1).mp hz⟩
  · intro hy
    exact ⟨mk y (hsub hy), (mem_ball_iff hr1).mpr hy.2, rfl⟩

theorem measure_ball {x : BaseCarrier D} {r : ℝ} (hr1 : r ≤ 1)
    (hsub : rsBall D.Ω w X x.val r ⊆ D.N) :
    measure D (Metric.ball x r) = volume (rsBall D.Ω w X x.val r) := by
  rw [measure_apply, image_ball hr1 hsub]

end BaseCarrier

end RothschildStein.P2
