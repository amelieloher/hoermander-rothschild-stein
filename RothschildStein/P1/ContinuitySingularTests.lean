-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.ContinuitySingularLp
public import Mathlib.Analysis.Normed.Lp.SmoothApprox
public import Mathlib.Geometry.Manifold.PartitionOfUnity

/-!
# Continuity: principal values, tests and `L^p`-density of tests

Tools for the bounded extension of the principal value from tests to `L^p(V)`:

* `rhoPV`, `HasRhoPV.add`, `HasRhoPV.sub`, `HasRhoPV.unique`: the `ρ`-principal value as a limit,
  additive in the input;
* `testFunction_memLp`, `testToLp`: tests `C_c^∞(V)` as elements of `L^p(V)` (`V` of finite measure);
* `exists_testFunction_eLpNorm_sub_le` (**localized smooth density**, "unique by localized smooth
  density", BB pp. 325-326): every `L^p(V)` function, `1 ≤ p < ∞`, is within `ε` in `L^p(V)` of a
  test function with compact support in the open set `V`: approximate by a smooth compactly
  supported function of the whole space (Mathlib), and cut off by a test function equal to one on
  a compact `K ⊆ V` with `|V ∖ K|` small;
* `holderENorm_sub_le`: the Hölder norm is subadditive;
* `memLp_of_holderENorm_ne_top`: a measurable function of finite Hölder norm on `V` is in `L^p(V)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Metric Filter TopologicalSpace
open scoped ENNReal NNReal Topology
namespace RothschildStein.P1

section PV

variable {N : ℕ} {ρ κ : (Fin N → ℝ) → (Fin N → ℝ) → ℝ} {f g : (Fin N → ℝ) → ℝ}
  {ξ : Fin N → ℝ} {v w : ℝ}

/-- The `ρ`-principal value of `κ` against `f` at `ξ` as a limit (`limUnder`; it is the
value of `TypeOperator.apply` at type 0 up to the multiplier). -/
def rhoPV (ρ κ : (Fin N → ℝ) → (Fin N → ℝ) → ℝ) (f : (Fin N → ℝ) → ℝ) (ξ : Fin N → ℝ) : ℝ :=
  limUnder (𝓝[>] (0 : ℝ)) (fun ε => rhoTruncated ρ κ f ε ξ)

/-- The action of a type-0 operator is the `ρ`-principal value of its kernel plus the
multiplier term (`TypeOperator.apply` at type `0`). -/
theorem typeOperator_apply_eq_rhoPV {F : KernelFrame N} (T : TypeOperator F 0)
    (f : (Fin N → ℝ) → ℝ) (ξ : Fin N → ℝ) :
    T.apply f ξ = rhoPV F.rho T.kernel f ξ + T.mult ξ * f ξ := by
  simp [TypeOperator.apply, rhoPV, rhoTruncated, TypeOperator.truncated]

/-- If the principal value exists with value `v`, `rhoPV` is `v`. -/
theorem HasRhoPV.rhoPV_eq (h : HasRhoPV ρ κ f ξ v) : rhoPV ρ κ f ξ = v := h.2.limUnder_eq

/-- The principal value is additive in the input. -/
theorem HasRhoPV.add (h1 : HasRhoPV ρ κ f ξ v) (h2 : HasRhoPV ρ κ g ξ w) :
    HasRhoPV ρ κ (fun η => f η + g η) ξ (v + w) := by
  refine ⟨fun ε hε => ?_, ?_⟩
  · refine ((h1.1 ε hε).add (h2.1 ε hε)).congr (ae_of_all _ fun η => ?_)
    simp [mul_add]
  · refine (h1.2.add h2.2).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε' : 0 < ε := hε
    simp only [rhoTruncated, mul_add]
    exact (integral_add (h1.1 ε hε') (h2.1 ε hε')).symm

/-- The principal value is subtractive in the input. -/
theorem HasRhoPV.sub (h1 : HasRhoPV ρ κ f ξ v) (h2 : HasRhoPV ρ κ g ξ w) :
    HasRhoPV ρ κ (fun η => f η - g η) ξ (v - w) := by
  refine ⟨fun ε hε => ?_, ?_⟩
  · refine ((h1.1 ε hε).sub (h2.1 ε hε)).congr (ae_of_all _ fun η => ?_)
    simp [mul_sub]
  · refine (h1.2.sub h2.2).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε' : 0 < ε := hε
    simp only [rhoTruncated, mul_sub]
    exact (integral_sub (h1.1 ε hε') (h2.1 ε hε')).symm

/-- The principal value is homogeneous in the input. -/
theorem HasRhoPV.const_mul (c : ℝ) (h : HasRhoPV ρ κ f ξ v) :
    HasRhoPV ρ κ (fun η => c * f η) ξ (c * v) := by
  refine ⟨fun ε hε => ?_, ?_⟩
  · refine ((h.1 ε hε).const_mul c).congr (ae_of_all _ fun η => ?_)
    simp only [mul_left_comm]
  · refine (h.2.const_mul c).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with ε hε
    simp only [rhoTruncated, mul_left_comm (κ ξ _) c]
    rw [integral_const_mul]

end PV

section Tests

variable {N : ℕ}

/-- A test function with compact support in an open set of finite measure is in every
`L^P`. -/
theorem testFunction_memLp (V : Opens (Fin N → ℝ)) (hfin : volume (V : Set (Fin N → ℝ)) < ⊤)
    (φ : TestFunction V ℝ (⊤ : ℕ∞)) (P : ℝ≥0∞) : MemLp φ P (volume.restrict (V : Set _)) := by
  have : IsFiniteMeasure (volume.restrict (V : Set (Fin N → ℝ))) :=
    ⟨by rwa [Measure.restrict_apply_univ]⟩
  obtain ⟨M, hM⟩ := φ.continuous.bounded_above_of_compact_support φ.hasCompactSupport
  exact MemLp.of_bound φ.continuous.aestronglyMeasurable M (ae_of_all _ hM)

/-- Test functions as elements of `L^P(V)`. -/
def testToLp (V : Opens (Fin N → ℝ)) (hfin : volume (V : Set (Fin N → ℝ)) < ⊤) (P : ℝ≥0∞)
    [Fact (1 ≤ P)] :
    TestFunction V ℝ (⊤ : ℕ∞) →ₗ[ℝ] Lp ℝ P (volume.restrict (V : Set (Fin N → ℝ))) where
  toFun φ := (testFunction_memLp V hfin φ P).toLp φ
  map_add' _ _ := MemLp.toLp_add _ _
  map_smul' c _ := MemLp.toLp_const_smul c _

/-- **Localized smooth density.** For an open set `V` of finite measure and `1 ≤ P < ∞`, every
function of `L^P(V)` is within `ε` in `L^P(V)` of a test function with compact support in `V`
(BB pp. 325-326, uniqueness of the bounded extension "by localized smooth density"). -/
theorem exists_testFunction_eLpNorm_sub_le (V : Opens (Fin N → ℝ))
    (hfin : volume (V : Set (Fin N → ℝ)) < ⊤) {P : ℝ≥0∞} (hP1 : 1 ≤ P) (hP : P ≠ ⊤)
    {f : (Fin N → ℝ) → ℝ} (hf : MemLp f P (volume.restrict (V : Set _))) {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : TestFunction V ℝ (⊤ : ℕ∞),
      eLpNorm (fun x => f x - φ x) P (volume.restrict (V : Set _)) ≤ ENNReal.ofReal ε := by
  classical
  have hε2 : 0 < ε / 2 := half_pos hε
  obtain ⟨g, hgc, hgs, hg⟩ := hf.exist_eLpNorm_sub_le hP hP1 hε2
  obtain ⟨Mg, hMg⟩ := hgs.continuous.bounded_above_of_compact_support hgc
  have hMg0 : 0 ≤ Mg := (norm_nonneg _).trans (hMg 0)
  have hP0 : P ≠ 0 := (zero_lt_one.trans_le hP1).ne'
  have hpr : 0 < P.toReal := ENNReal.toReal_pos hP0 hP
  set t : ℝ := ε / (2 * (Mg + 1)) with ht
  have htpos : 0 < t := by rw [ht]; positivity
  set η : ℝ≥0∞ := ENNReal.ofReal (t ^ P.toReal) with hη
  have hη0 : η ≠ 0 := by
    rw [hη]
    exact (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos htpos _)).ne'
  obtain ⟨K, hKV, hKc, hKη⟩ := V.isOpen.measurableSet.exists_isCompact_sdiff_lt hfin.ne hη0
  obtain ⟨s, hs_open, hKs, hs_cl, hs_cpt⟩ :=
    exists_open_between_and_isCompact_closure hKc V.isOpen hKV
  obtain ⟨θ, hθ, hθrange, hθsupp, hθone⟩ :=
    exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hs_open hKc.isClosed hKs
  have hθc : HasCompactSupport θ := by
    refine HasCompactSupport.intro hs_cpt (fun x hx => ?_)
    by_contra hne
    exact hx (subset_closure (hθsupp ▸ Function.mem_support.mpr hne))
  have hθV : tsupport θ ⊆ (V : Set (Fin N → ℝ)) := by
    rw [tsupport, hθsupp]
    exact hs_cl
  let φ : TestFunction V ℝ (⊤ : ℕ∞) :=
    ⟨fun x => θ x * g x, hθ.mul hgs, hθc.mul_right, (tsupport_mul_subset_left).trans hθV⟩
  refine ⟨φ, ?_⟩
  have hpt : ∀ x ∈ (V : Set (Fin N → ℝ)),
      ‖g x - θ x * g x‖ ≤ ‖((V : Set (Fin N → ℝ)) \ K).indicator (fun _ => Mg) x‖ := by
    intro x hx
    by_cases hxK : x ∈ K
    · have h1 : θ x = 1 := (hθone x).mp hxK
      simp [h1]
    · have h01 := hθrange ⟨x, rfl⟩
      rw [indicator_of_mem (show x ∈ (V : Set (Fin N → ℝ)) \ K from ⟨hx, hxK⟩)]
      have : g x - θ x * g x = (1 - θ x) * g x := by ring
      rw [this, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith [h01.2])]
      have h2 : |g x| ≤ Mg := by simpa using hMg x
      calc (1 - θ x) * |g x| ≤ 1 * |g x| :=
            mul_le_mul_of_nonneg_right (by linarith [h01.1]) (abs_nonneg _)
        _ ≤ |Mg| := by rw [one_mul]; exact h2.trans (le_abs_self _)
  have hind : eLpNorm (fun x => g x - φ x) P (volume.restrict (V : Set (Fin N → ℝ))) ≤
      ENNReal.ofReal (ε / 2) := by
    calc eLpNorm (fun x => g x - φ x) P (volume.restrict (V : Set (Fin N → ℝ)))
        ≤ eLpNorm (((V : Set (Fin N → ℝ)) \ K).indicator (fun _ => Mg)) P
            (volume.restrict (V : Set (Fin N → ℝ))) :=
          eLpNorm_mono_ae ((hgs.continuous.sub (hθ.continuous.mul hgs.continuous)).aestronglyMeasurable)
            (ae_restrict_of_forall_mem V.isOpen.measurableSet hpt)
      _ = ‖Mg‖ₑ * (volume.restrict (V : Set (Fin N → ℝ))) ((V : Set (Fin N → ℝ)) \ K) ^
            (1 / P.toReal) :=
          eLpNorm_indicator_const (V.isOpen.measurableSet.diff
            hKc.isClosed.measurableSet).nullMeasurableSet hP0 hP
      _ ≤ ‖Mg‖ₑ * η ^ (1 / P.toReal) := by
          gcongr
          calc (volume.restrict (V : Set (Fin N → ℝ))) ((V : Set (Fin N → ℝ)) \ K)
              ≤ volume ((V : Set (Fin N → ℝ)) \ K) := Measure.restrict_apply_le _ _
            _ ≤ η := hKη.le
      _ = ENNReal.ofReal Mg * ENNReal.ofReal t := by
          rw [Real.enorm_eq_ofReal hMg0, hη, ENNReal.ofReal_rpow_of_nonneg
            (Real.rpow_nonneg htpos.le _) (by positivity),
            ← Real.rpow_mul htpos.le, mul_one_div_cancel hpr.ne', Real.rpow_one]
      _ = ENNReal.ofReal (Mg * t) := (ENNReal.ofReal_mul hMg0).symm
      _ ≤ ENNReal.ofReal (ε / 2) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [ht]
          have h1 : Mg * (ε / (2 * (Mg + 1))) = ε / 2 * (Mg / (Mg + 1)) := by
            field_simp
          rw [h1]
          have h2 : Mg / (Mg + 1) ≤ 1 := by
            rw [div_le_one (by linarith)]; linarith
          nlinarith [half_pos hε]
  have hfg : AEStronglyMeasurable (fun x => f x - g x) (volume.restrict (V : Set _)) :=
    hf.aestronglyMeasurable.sub hgs.continuous.aestronglyMeasurable
  have hgφ : AEStronglyMeasurable (fun x => g x - φ x) (volume.restrict (V : Set _)) :=
    (hgs.continuous.sub φ.continuous).aestronglyMeasurable
  have hsplit : (fun x => f x - φ x) = (fun x => f x - g x) + (fun x => g x - φ x) := by
    funext x; simp
  rw [hsplit]
  calc eLpNorm ((fun x => f x - g x) + (fun x => g x - φ x)) P (volume.restrict (V : Set _))
      ≤ eLpNorm (fun x => f x - g x) P (volume.restrict (V : Set _)) +
        eLpNorm (fun x => g x - φ x) P (volume.restrict (V : Set _)) := eLpNorm_add_le hP1
    _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) :=
        add_le_add (show eLpNorm (fun x => f x - g x) P (volume.restrict (V : Set _)) ≤ _ from hg)
          hind
    _ = ENNReal.ofReal ε := by
        rw [← ENNReal.ofReal_add hε2.le hε2.le]
        congr 1
        ring

/-- **Tests are dense in `L^P(V)`** for `1 ≤ P < ∞` (`V` open of finite measure): the unique
bounded extension from tests is determined (BB pp. 325-326). -/
theorem denseRange_testToLp (V : Opens (Fin N → ℝ)) (hfin : volume (V : Set (Fin N → ℝ)) < ⊤)
    {P : ℝ≥0∞} [Fact (1 ≤ P)] (hP : P ≠ ⊤) : DenseRange (testToLp V hfin P) := by
  rw [Metric.denseRange_iff]
  intro v r hr
  obtain ⟨φ, hφ⟩ := exists_testFunction_eLpNorm_sub_le V hfin Fact.out hP (Lp.memLp v)
    (half_pos hr)
  refine ⟨φ, ?_⟩
  rw [dist_eq_norm, Lp.norm_def]
  have hae : ⇑(v - testToLp V hfin P φ) =ᵐ[volume.restrict (V : Set (Fin N → ℝ))]
      fun x => v x - φ x := by
    filter_upwards [Lp.coeFn_sub v (testToLp V hfin P φ),
      (testFunction_memLp V hfin φ P).coeFn_toLp] with x h1 h2
    rw [h1]
    exact congrArg₂ (· - ·) rfl h2
  rw [eLpNorm_congr_ae hae]
  have h1 : (eLpNorm (fun x => v x - φ x) P (volume.restrict (V : Set _))).toReal ≤ r / 2 := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hφ
    rwa [ENNReal.toReal_ofReal (half_pos hr).le] at this
  linarith

end Tests

section HolderNorm

variable {n' : ℕ}

/-- The Hölder norm is subadditive (for differences). -/
theorem holderENorm_sub_le {d : (Fin n' → ℝ) → (Fin n' → ℝ) → ℝ≥0∞} {α : ℝ} (hα : 0 ≤ α)
    {V : Set (Fin n' → ℝ)} (f g : (Fin n' → ℝ) → ℝ) :
    holderENorm d α V (fun x => f x - g x) ≤ holderENorm d α V f + holderENorm d α V g := by
  by_cases hf : holderENorm d α V f = ⊤
  · rw [hf, top_add]; exact le_top
  by_cases hg : holderENorm d α V g = ⊤
  · rw [hg, add_top]; exact le_top
  have hsf : holderSeminorm d α V f ≠ ⊤ := ne_top_of_le_ne_top hf le_add_self
  have hsg : holderSeminorm d α V g ≠ ⊤ := ne_top_of_le_ne_top hg le_add_self
  unfold holderENorm at *
  have hsup : (⨆ x : V, ENNReal.ofReal |f x - g x|) ≤
      (⨆ x : V, ENNReal.ofReal |f x|) + ⨆ x : V, ENNReal.ofReal |g x| := by
    refine iSup_le fun x => ?_
    calc ENNReal.ofReal |f x - g x| ≤ ENNReal.ofReal (|f x| + |g x|) :=
          ENNReal.ofReal_le_ofReal (abs_sub _ _)
      _ = ENNReal.ofReal |f x| + ENNReal.ofReal |g x| :=
          ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
      _ ≤ _ := add_le_add (le_iSup (fun x : V => ENNReal.ofReal |f x|) x)
          (le_iSup (fun x : V => ENNReal.ofReal |g x|) x)
  have hsem : holderSeminorm d α V (fun x => f x - g x) ≤
      holderSeminorm d α V f + holderSeminorm d α V g := by
    have h := frozenHolderSeminorm_le_of_bound (d := d) (V := V) (f := fun x => f x - g x) hα
      (C := (holderSeminorm d α V f).toReal + (holderSeminorm d α V g).toReal)
      (add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg) (by
        intro x hx y hy hxy
        have h1 := abs_sub_le_of_frozenHolderSeminorm hα hsf hx hy hxy
        have h2 := abs_sub_le_of_frozenHolderSeminorm hα hsg hx hy hxy
        calc |(f x - g x) - (f y - g y)| = |(f x - f y) - (g x - g y)| := by ring_nf
          _ ≤ |f x - f y| + |g x - g y| := abs_sub _ _
          _ ≤ _ := by nlinarith [h1, h2])
    rwa [ENNReal.ofReal_add ENNReal.toReal_nonneg ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal hsf, ENNReal.ofReal_toReal hsg] at h
  calc _ ≤ ((⨆ x : V, ENNReal.ofReal |f x|) + ⨆ x : V, ENNReal.ofReal |g x|) +
        (holderSeminorm d α V f + holderSeminorm d α V g) := add_le_add hsup hsem
    _ = _ := by ac_rfl

/-- A measurable function of finite Hölder norm on a set of finite measure belongs to
every `L^P` there. -/
theorem memLp_of_holderENorm_ne_top {d : (Fin n' → ℝ) → (Fin n' → ℝ) → ℝ≥0∞} {α : ℝ}
    {V : Set (Fin n' → ℝ)} (hVm : MeasurableSet V) (hfin : volume V < ⊤)
    {f : (Fin n' → ℝ) → ℝ} (hf : holderENorm d α V f ≠ ⊤)
    (hfm : AEStronglyMeasurable f (volume.restrict V)) (P : ℝ≥0∞) :
    MemLp f P (volume.restrict V) := by
  have : IsFiniteMeasure (volume.restrict V) := ⟨by rwa [Measure.restrict_apply_univ]⟩
  refine MemLp.of_bound hfm (holderENorm d α V f).toReal
    (ae_restrict_of_forall_mem hVm fun x hx => ?_)
  rw [Real.norm_eq_abs]
  exact (ENNReal.ofReal_le_iff_le_toReal hf).mp
    (le_trans (le_iSup (fun x : V => ENNReal.ofReal |f x|) ⟨x, hx⟩) le_self_add)

end HolderNorm

end RothschildStein.P1
