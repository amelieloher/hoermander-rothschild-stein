-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.LiftedChart
public import RothschildStein.G1.ControlEMetric
public import Mathlib.Topology.MetricSpace.Basic
public import RothschildStein.G2.EuclideanComparison
public import RothschildStein.G2.MaxGauge

/-!
# Metric-measure carrier of the lifted chart

This is the carrier of the metric-measure certificate (BB pp. 295-296, 568). The chart
domain `U` of a `LiftedChart` is a type `C.Carrier` carrying

* the distance `d(x, y) = (d̃(x, y)).toReal`, where `d̃ = C.dl` is the ambient lifted control
  distance on `O = π⁻¹ Ω` (finite on `U × U` by the upper half of `gauge_comparison`; no
  Chow-type connectivity input is needed because the chart supplies it);
* the Euclidean subspace topology (the metric topology equals it by the chart, via
  `gauge_comparison` and the homeomorphism `e η`), hence the Borel structure and the Lebesgue
  measure `volume = comap Subtype.val volume` of the ambient space `ℝ^{n+m}`.

The localization certificate is stated with `d = d̃_W` for a connected free-field neighbourhood `W`. Here the
ambient distance of the chart is used (`d̃ = d̃_O ≤ d̃_W`): it is the distance of the lifted-chart
fields `gauge_comparison` and `ball_bounds`, so no comparison `d̃_W = d̃_O` near the diagonal is
needed, and `W = U` is a legitimate coordinate neighbourhood.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ENNReal Topology
namespace RothschildStein.P1

/-- A neighbourhood of `0` contains a sublevel `{ν < r}` of every homogeneous gauge
(BB Thm 3.12, pp. 101-102; local comparison with the coordinate norm). -/
theorem exists_gauge_lt_subset_of_mem_nhds_zero {N : ℕ} (G : HomogeneousGroup N)
    {ν : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν) {t : Set (Fin N → ℝ)}
    (ht : t ∈ 𝓝 (0 : Fin N → ℝ)) : ∃ r : ℝ, 0 < r ∧ ∀ u, ν u < r → u ∈ t := by
  obtain ⟨ε, hε, hεt⟩ := Metric.mem_nhds_iff.mp ht
  obtain ⟨a, b, ha, hb, hcomp⟩ := G2.gauge_sublevel_norm_comparison hν 1
  refine ⟨min 1 (a * ε), lt_min one_pos (mul_pos ha hε), fun u hu => hεt ?_⟩
  have h1 : ν u ≤ 1 := (hu.trans_le (min_le_left _ _)).le
  have h2 : ν u < a * ε := hu.trans_le (min_le_right _ _)
  have h3 := (hcomp u h1).1
  rw [Metric.mem_ball, dist_zero_right]
  by_contra hcon
  have : a * ε ≤ a * ‖u‖ := mul_le_mul_of_nonneg_left (not_lt.mp hcon) ha.le
  linarith

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}

namespace LiftedChart

variable (C : LiftedChart w s Ω hΩ X x₀ m)

/-- The carrier of the metric-measure certificate: the chart domain `U`, with the
ambient lifted control metric. A type synonym, so that the Euclidean `Subtype` instances stay
separate from the control-metric instances below. -/
def Carrier : Type := {ξ : Fin (n + m) → ℝ // ξ ∈ C.U}

/-- The lifted domain `O = π⁻¹ Ω` is open. -/
theorem isOpen_O_of_chart : IsOpen C.O :=
  hΩ.preimage (continuous_pi fun j => continuous_apply (Fin.castAdd m j))

/-- The chart domain lies in the lifted domain. -/
theorem mem_O_of_mem_U {ξ : Fin (n + m) → ℝ} (hξ : ξ ∈ C.U) : ξ ∈ C.O :=
  C.closure_U_subset (subset_closure hξ)

/-- The ambient lifted control distance is finite on `U × U`: the upper half of the
lifted-chart field `gauge_comparison`. -/
theorem dl_finite_on_U {η ξ : Fin (n + m) → ℝ} (hη : η ∈ C.U) (hξ : ξ ∈ C.U) :
    C.dl η ξ ≠ ⊤ := by
  obtain ⟨Cρ, -, h⟩ := C.gauge_comparison
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (h η hη ξ hξ).2

/-- Real form of the lifted-chart field `gauge_comparison`: the real control distance
is comparable to the max gauge of `Θ` on `U × U`. -/
theorem exists_dist_comparison_U :
    ∃ Cρ : ℝ, 1 ≤ Cρ ∧ ∀ η ∈ C.U, ∀ ξ ∈ C.U,
      rsGauge C.G.weight C.G.weight_pos (C.Θ η ξ) / Cρ ≤ (C.dl η ξ).toReal ∧
      (C.dl η ξ).toReal ≤ Cρ * rsGauge C.G.weight C.G.weight_pos (C.Θ η ξ) := by
  obtain ⟨Cρ, hC, h⟩ := C.gauge_comparison
  refine ⟨Cρ, hC, fun η hη ξ hξ => ?_⟩
  obtain ⟨h1, h2⟩ := h η hη ξ hξ
  have hne := C.dl_finite_on_U hη hξ
  have hg : 0 ≤ rsGauge C.G.weight C.G.weight_pos (C.Θ η ξ) := G2.gauge_nonneg C.G _
  have hCρ : 0 ≤ Cρ := zero_le_one.trans hC
  exact ⟨(ENNReal.ofReal_le_iff_le_toReal hne).mp h1,
    ENNReal.toReal_le_of_le_ofReal (mul_nonneg hCρ hg) h2⟩

/-- For `η ∈ U` the map `ξ ↦ Θ(η, ξ)` is continuous on `U`. -/
theorem continuousOn_Θ_right {η : Fin (n + m) → ℝ} (hη : η ∈ C.U) :
    ContinuousOn (fun ξ => C.Θ η ξ) C.U := by
  have h := C.theta_smooth.continuousOn.comp
    (Continuous.continuousOn (f := fun ξ : Fin (n + m) → ℝ => (η, ξ))
      (continuous_const.prodMk continuous_id)) (fun ξ hξ => (⟨hη, hξ⟩ : (η, ξ) ∈ C.U ×ˢ C.U))
  exact h

/-- The real-valued ambient lifted control distance on the chart domain. -/
def carrierDist (x y : {ξ : Fin (n + m) → ℝ // ξ ∈ C.U}) : ℝ := (C.dl x.1 y.1).toReal

theorem carrierDist_self (x : {ξ : Fin (n + m) → ℝ // ξ ∈ C.U}) : C.carrierDist x x = 0 := by
  unfold carrierDist
  rw [show C.dl x.1 x.1 = 0 from G1.controlDistance_self w C.Xl (C.mem_O_of_mem_U x.2)]
  rfl

theorem carrierDist_comm (x y : {ξ : Fin (n + m) → ℝ // ξ ∈ C.U}) :
    C.carrierDist x y = C.carrierDist y x := by
  unfold carrierDist
  rw [show C.dl x.1 y.1 = C.dl y.1 x.1 from G1.controlDistance_symm C.O w C.Xl x.1 y.1]

theorem carrierDist_triangle (x y z : {ξ : Fin (n + m) → ℝ // ξ ∈ C.U}) :
    C.carrierDist x z ≤ C.carrierDist x y + C.carrierDist y z := by
  have h : C.dl x.1 z.1 ≤ C.dl x.1 y.1 + C.dl y.1 z.1 :=
    G1.controlDistance_triangle C.O w C.Xl x.1 y.1 z.1
  have hxy := C.dl_finite_on_U x.2 y.2
  have hyz := C.dl_finite_on_U y.2 z.2
  unfold carrierDist
  rw [← ENNReal.toReal_add hxy hyz]
  exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨hxy, hyz⟩) h

theorem eq_of_carrierDist_eq_zero {x y : {ξ : Fin (n + m) → ℝ // ξ ∈ C.U}}
    (h : C.carrierDist x y = 0) : x = y := by
  have h0 : C.dl x.1 y.1 = 0 := by
    rcases (ENNReal.toReal_eq_zero_iff _).mp h with h0 | h0
    · exact h0
    · exact absurd h0 (C.dl_finite_on_U x.2 y.2)
  exact Subtype.ext ((G1.controlDistance_eq_zero_iff C.isOpen_O_of_chart w C.Xl
    (fun i => (C.lift_smooth i).continuousOn) (C.mem_O_of_mem_U x.2)).mp h0)

/-- The metric topology of `carrierDist` is the Euclidean subspace topology of `U`
(BB Prop 1.41 and Thm 1.53, pp. 22-36, in the chart form: the max gauge of `Θ(η, ·)`
is comparable to `d̃(η, ·)` and `e η` is a homeomorphism of `U` onto its image). -/
theorem isOpen_iff_forall_carrierDist (t : Set {ξ : Fin (n + m) → ℝ // ξ ∈ C.U}) :
    IsOpen t ↔ ∀ x ∈ t, ∃ ε > 0, ∀ y : {ξ : Fin (n + m) → ℝ // ξ ∈ C.U},
      C.carrierDist x y < ε → y ∈ t := by
  obtain ⟨Cρ, hC1, hcomp⟩ := C.exists_dist_comparison_U
  have hCρ : 0 < Cρ := zero_lt_one.trans_le hC1
  constructor
  · intro ht x hx
    obtain ⟨t', ht', rfl⟩ := isOpen_induced_iff.mp ht
    obtain ⟨hsrc, hval, -, -, hΘ⟩ := C.chart x.1 x.2
    have ht''o : IsOpen (t' ∩ C.U) := ht'.inter C.isOpen_U
    have himg : IsOpen ((C.e x.1) '' (t' ∩ C.U)) :=
      (C.e x.1).isOpen_image_of_subset_source ht''o (by rw [hsrc]; exact inter_subset_right)
    have h0 : (0 : Fin (n + m) → ℝ) ∈ (C.e x.1) '' (t' ∩ C.U) :=
      ⟨x.1, ⟨hx, x.2⟩, by rw [hval x.1 x.2]; exact hΘ⟩
    obtain ⟨r, hr, hrsub⟩ := exists_gauge_lt_subset_of_mem_nhds_zero C.G
      (G2.isHomogeneousGauge_max C.G) (himg.mem_nhds h0)
    refine ⟨r / Cρ, div_pos hr hCρ, fun y hy => ?_⟩
    have hg : rsGauge C.G.weight C.G.weight_pos (C.Θ x.1 y.1) < r := by
      have h1 := (hcomp x.1 x.2 y.1 y.2).1
      have h2 : rsGauge C.G.weight C.G.weight_pos (C.Θ x.1 y.1) / Cρ < r / Cρ :=
        lt_of_le_of_lt h1 hy
      exact (div_lt_div_iff_of_pos_right hCρ).mp h2
    obtain ⟨ξ, hξ, hξy⟩ := hrsub _ hg
    have hξeq : ξ = y.1 := (C.e x.1).injOn (by rw [hsrc]; exact hξ.2)
      (by rw [hsrc]; exact y.2) (hξy.trans (hval y.1 y.2).symm)
    rw [hξeq] at hξ
    exact hξ.1
  · intro h
    rw [isOpen_iff_mem_nhds]
    intro x hx
    obtain ⟨ε, hε, hεt⟩ := h x hx
    have hf : Continuous (fun y : {ξ : Fin (n + m) → ℝ // ξ ∈ C.U} =>
        rsGauge C.G.weight C.G.weight_pos (C.Θ x.1 y.1)) :=
      (G2.continuous_gauge C.G).comp
        ((C.continuousOn_Θ_right x.2).comp_continuous continuous_subtype_val (fun y => y.2))
    have hopen : IsOpen {y : {ξ : Fin (n + m) → ℝ // ξ ∈ C.U} |
        rsGauge C.G.weight C.G.weight_pos (C.Θ x.1 y.1) < ε / Cρ} :=
      isOpen_lt hf continuous_const
    refine Filter.mem_of_superset (hopen.mem_nhds ?_) ?_
    · show rsGauge C.G.weight C.G.weight_pos (C.Θ x.1 x.1) < ε / Cρ
      rw [(C.chart x.1 x.2).2.2.2.2, (G2.gauge_eq_zero_iff C.G 0).mpr rfl]
      exact div_pos hε hCρ
    · intro y hy
      apply hεt
      have h1 := (hcomp x.1 x.2 y.1 y.2).2
      have h2 : Cρ * rsGauge C.G.weight C.G.weight_pos (C.Θ x.1 y.1) < ε := by
        have := mul_lt_mul_of_pos_left (show rsGauge C.G.weight C.G.weight_pos
          (C.Θ x.1 y.1) < ε / Cρ from hy) hCρ
        rwa [mul_div_cancel₀ _ hCρ.ne'] at this
      exact lt_of_le_of_lt h1 h2

/-- The control metric on the chart domain, with the Euclidean subspace topology
(a local Euclidean comparison, here supplied by the chart). -/
instance carrierMetricSpace : MetricSpace C.Carrier :=
  letI : TopologicalSpace C.Carrier :=
    inferInstanceAs (TopologicalSpace {ξ : Fin (n + m) → ℝ // ξ ∈ C.U})
  MetricSpace.ofDistTopology (C.carrierDist) C.carrierDist_self C.carrierDist_comm
    C.carrierDist_triangle C.isOpen_iff_forall_carrierDist (fun _ _ h => C.eq_of_carrierDist_eq_zero h)

/-- The Borel structure of the chart domain, from the ambient Euclidean space. -/
instance carrierMeasurableSpace : MeasurableSpace C.Carrier :=
  inferInstanceAs (MeasurableSpace {ξ : Fin (n + m) → ℝ // ξ ∈ C.U})

/-- The metric topology of the carrier is the Euclidean one, so its Borel structure is
the metric Borel structure. -/
instance carrierBorelSpace : BorelSpace C.Carrier :=
  ⟨(inferInstance : BorelSpace {ξ : Fin (n + m) → ℝ // ξ ∈ C.U}).measurable_eq⟩

instance carrierSecondCountable : SecondCountableTopology C.Carrier :=
  inferInstanceAs (SecondCountableTopology {ξ : Fin (n + m) → ℝ // ξ ∈ C.U})

namespace Carrier

variable {C}

/-- The underlying point of the ambient space. -/
def val (x : C.Carrier) : Fin (n + m) → ℝ := Subtype.val x

/-- The point of the carrier over a point of `U`. -/
def mk (ξ : Fin (n + m) → ℝ) (h : ξ ∈ C.U) : C.Carrier := Subtype.mk ξ h

theorem val_mem (x : C.Carrier) : x.val ∈ C.U := Subtype.property x

@[simp] theorem val_mk (ξ : Fin (n + m) → ℝ) (h : ξ ∈ C.U) : (mk ξ h : C.Carrier).val = ξ := rfl

@[simp] theorem mk_val (x : C.Carrier) : mk x.val x.val_mem = x := rfl

theorem val_injective : Function.Injective (val : C.Carrier → Fin (n + m) → ℝ) :=
  fun _ _ h => Subtype.ext h

theorem dist_def (x y : C.Carrier) : dist x y = (C.dl x.val y.val).toReal := rfl

theorem continuous_val : Continuous (val : C.Carrier → Fin (n + m) → ℝ) :=
  continuous_subtype_val

theorem isOpenEmbedding_val : Topology.IsOpenEmbedding (val : C.Carrier → Fin (n + m) → ℝ) :=
  C.isOpen_U.isOpenEmbedding_subtypeVal

theorem measurableEmbedding_val : MeasurableEmbedding (val : C.Carrier → Fin (n + m) → ℝ) :=
  MeasurableEmbedding.subtype_coe C.isOpen_U.measurableSet

theorem range_val : Set.range (val : C.Carrier → Fin (n + m) → ℝ) = C.U := by
  ext ξ
  exact ⟨fun ⟨x, hx⟩ => hx ▸ x.val_mem, fun h => ⟨mk ξ h, rfl⟩⟩

theorem image_preimage_val {K : Set (Fin (n + m) → ℝ)} (hK : K ⊆ C.U) :
    val '' (val ⁻¹' K : Set C.Carrier) = K :=
  image_preimage_eq_of_subset (by rw [range_val]; exact hK)

theorem isCompact_preimage_val {K : Set (Fin (n + m) → ℝ)} (hK : IsCompact K) (hKU : K ⊆ C.U) :
    IsCompact (val ⁻¹' K : Set C.Carrier) := by
  rw [isOpenEmbedding_val.isInducing.isCompact_iff, image_preimage_val hKU]
  exact hK

end Carrier

/-- Lebesgue measure on the chart domain: the restriction of the Lebesgue measure of
`ℝ^{n+m}` (so Borel, nonatomic and finite on relatively compact regions). -/
instance carrierMeasureSpace : MeasureSpace C.Carrier where
  volume := Measure.comap Carrier.val volume

namespace Carrier

variable {C}

theorem volume_apply (t : Set C.Carrier) :
    (volume : Measure C.Carrier) t = volume (val '' t) :=
  measurableEmbedding_val.comap_apply volume t

theorem measure_singleton_eq_zero (x : C.Carrier) : (volume : Measure C.Carrier) {x} = 0 := by
  have : Nonempty (Fin (n + m)) := ⟨⟨0, C.G.dimension_pos⟩⟩
  rw [volume_apply, Set.image_singleton]
  exact measure_singleton _

theorem dist_comm_dl (x y : C.Carrier) : C.dl x.val y.val = C.dl y.val x.val :=
  G1.controlDistance_symm C.O w C.Xl x.val y.val

theorem mem_ball_iff {x y : C.Carrier} {t : ℝ} :
    y ∈ ball x t ↔ C.dl x.val y.val < ENNReal.ofReal t := by
  rw [mem_ball, dist_def, ← dist_comm_dl x y]
  exact (ENNReal.lt_ofReal_iff_toReal_lt (C.dl_finite_on_U x.val_mem y.val_mem)).symm

end Carrier

end LiftedChart

end RothschildStein.P1
