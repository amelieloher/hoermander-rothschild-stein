-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.H2CertificateCarrier
public import RothschildStein.H2.LocDoubling
public import RothschildStein.G2.DilationMeasure

/-!
# Metric and measure certificate for a lifted chart

For a compact set `K ⊆ U` of the lifted chart (the input/output supports with their chart
margins) there are regions `Ω₀ ⋐ Ω₁ ⋐ Ω₂` of the carrier `C.Carrier` containing `K` and a radius
`κ > 0` below one sixth of the buffers and of the uniform volume radius of `ball_bounds`, such
that

* `closedBall y (6κ) ⊆ Ω₁` for `y ∈ Ω₀` and `⊆ Ω₂` for `y ∈ Ω₁`,
* `vLo t^Q ≤ μ(B(y, t)) ≤ vHi t^Q` for `y ∈ Ω₁`, `0 < t ≤ 6κ`,
* hence the `H2.LocDoubling` instance with `C_D = 2^Q vHi / vLo`, `m_κ ≥ vLo κ^Q`, `μ(Ω₂) < ∞`,
  `Ω₁` bounded (BB Def 7.1, p. 295; (7.1)-(7.2); BB pp. 568-569).

The regions are metric thickenings of the compact set, so the buffers are explicit. The volume
bounds are the lifted-chart field `ball_bounds` (the free-field volume estimate, with drift);
no regularity hypothesis of G4 is used.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set Metric MeasureTheory Filter
open scoped ENNReal Topology
namespace RothschildStein.P1

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}

namespace LiftedChart

namespace Carrier

variable {C : LiftedChart w s Ω hΩ X x₀ m}

/-- A carrier ball is the set of chart points at lifted control distance below `t`. -/
theorem image_val_ball (x : C.Carrier) (t : ℝ) :
    val '' ball x t = {ξ | ξ ∈ C.U ∧ C.dl x.val ξ < ENNReal.ofReal t} := by
  ext ξ
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.val_mem, mem_ball_iff.mp hy⟩
  · rintro ⟨hξ, h⟩
    exact ⟨mk ξ hξ, mem_ball_iff.mpr h, rfl⟩

/-- A carrier ball is the lifted control ball `rsBall` as soon as the latter lies in
`U` (always the case below the uniform volume radius, by `ball_bounds`). -/
theorem image_val_ball_eq_rsBall {x : C.Carrier} {t : ℝ}
    (h : rsBall C.O w C.Xl x.val t ⊆ C.U) :
    val '' ball x t = rsBall C.O w C.Xl x.val t := by
  rw [image_val_ball]
  ext ξ
  constructor
  · rintro ⟨hξ, hd⟩
    exact ⟨C.mem_O_of_mem_U hξ, hd⟩
  · intro hξ
    exact ⟨h hξ, hξ.2⟩

/-- The measure of a carrier ball is the Lebesgue measure of the lifted control ball. -/
theorem volume_ball_eq_rsBall {x : C.Carrier} {t : ℝ}
    (h : rsBall C.O w C.Xl x.val t ⊆ C.U) :
    (volume : Measure C.Carrier) (ball x t) = volume (rsBall C.O w C.Xl x.val t) := by
  rw [volume_apply, image_val_ball_eq_rsBall h]

/-- The image of the closure of a region of a locally
doubling structure is a compact subset of the chart domain. -/
theorem isCompact_image_closure {A : Set C.Carrier} (hA : IsCompact (closure A)) :
    IsCompact (val '' closure A : Set (Fin (n + m) → ℝ)) ∧ val '' closure A ⊆ C.U :=
  ⟨hA.image continuous_val, by rintro _ ⟨x, -, rfl⟩; exact x.val_mem⟩

end Carrier

variable (C : LiftedChart w s Ω hΩ X x₀ m)

/-- The metric-measure certificate: the properties of a `LocDoubling` structure on
the carrier of a lifted chart: Lebesgue measure, the uniform volume bounds
`vLo t^Q ≤ μ(B(y, t)) ≤ vHi t^Q` on `Ω₁` for `0 < t ≤ 6κ` (so doubling holds through `3κ` and
normality through `κ`), `C_D = 2^Q vHi / vLo`, `m_κ ≥ vLo κ^Q` and a bounded `Ω₁`
(BB Def 7.1 and (7.1)-(7.2), pp. 295-296; BB pp. 568–569, corrected). -/
structure IsMetricMeasureCertificate (S : H2.LocDoubling C.Carrier) (vLo vHi : ℝ) : Prop where
  μ_eq : S.μ = volume
  vLo_pos : 0 < vLo
  vLo_le_vHi : vLo ≤ vHi
  ball_eq_rsBall : ∀ y ∈ S.Ω₁, ∀ t : ℝ, 0 < t → t ≤ 6 * S.κ →
    Carrier.val '' ball y t = rsBall C.O w C.Xl y.val t
  ball_pos_lt_top : ∀ y ∈ S.Ω₁, ∀ t : ℝ, 0 < t → t ≤ 6 * S.κ →
    0 < S.μ (ball y t) ∧ S.μ (ball y t) < ⊤
  volume_lower : ∀ y ∈ S.Ω₁, ∀ t : ℝ, 0 < t → t ≤ 6 * S.κ →
    vLo * t ^ C.G.homogeneousDimension ≤ (S.μ (ball y t)).toReal
  volume_upper : ∀ y ∈ S.Ω₁, ∀ t : ℝ, 0 < t → t ≤ 6 * S.κ →
    (S.μ (ball y t)).toReal ≤ vHi * t ^ C.G.homogeneousDimension
  C_D_eq : S.C_D = 2 ^ C.G.homogeneousDimension * vHi / vLo
  m_κ_lower : ∀ y ∈ S.Ω₁, vLo * S.κ ^ C.G.homogeneousDimension ≤ (S.μ (ball y S.κ)).toReal
  isBounded_Ω₁ : Bornology.IsBounded S.Ω₁

/-- Existence of the geometric data `Ω₀ ⋐ Ω₁ ⋐ Ω₂`, `κ`, the
volume constants and the `H2.LocDoubling` structure, for every compact subset `K` of the chart
domain (the supports and their margins). The geometry
`(Ω_i, κ)` and the constants `(vLo, vHi, C_D)` are chosen first and depend only on `K` and the
chart, never on a function (BB pp. 295–296, 568–569). -/
theorem exists_metricMeasureCertificate {K : Set (Fin (n + m) → ℝ)} (hK : IsCompact K)
    (hKU : K ⊆ C.U) :
    ∃ (S : H2.LocDoubling C.Carrier) (vLo vHi : ℝ),
      C.IsMetricMeasureCertificate S vLo vHi ∧ K ⊆ Carrier.val '' S.Ω₀ := by
  classical
  have hQ : 1 ≤ C.G.homogeneousDimension := G2.homogeneousDimension_pos C.G
  -- a compact Euclidean neighbourhood `LE` of `K` inside `U`
  obtain ⟨δe, hδe, hLEU⟩ := hK.exists_cthickening_subset_open C.isOpen_U hKU
  have hLE : IsCompact (cthickening δe K) := hK.cthickening
  -- the corresponding sets in the carrier
  have hKt_cpt : IsCompact (Carrier.val ⁻¹' K : Set C.Carrier) :=
    Carrier.isCompact_preimage_val hK hKU
  have hLt_cpt : IsCompact (Carrier.val ⁻¹' (cthickening δe K) : Set C.Carrier) :=
    Carrier.isCompact_preimage_val hLE hLEU
  have hKt_int : (Carrier.val ⁻¹' K : Set C.Carrier) ⊆
      interior (Carrier.val ⁻¹' (cthickening δe K) : Set C.Carrier) := by
    have h1 : (Carrier.val ⁻¹' (thickening δe K) : Set C.Carrier) ⊆
        interior (Carrier.val ⁻¹' (cthickening δe K) : Set C.Carrier) :=
      interior_maximal (preimage_mono (thickening_subset_cthickening δe K))
        (isOpen_thickening.preimage Carrier.continuous_val)
    exact (preimage_mono (self_subset_thickening hδe K)).trans h1
  obtain ⟨δ, hδ, hcth⟩ := hKt_cpt.exists_cthickening_subset_open isOpen_interior hKt_int
  -- uniform volume bounds on `LE`
  obtain ⟨rstar, cv, Cv, _, _, _, hrstar, hcv, hCv, -, -, -, -, hb⟩ :=
    C.ball_bounds (cthickening δe K) hLE hLEU
  have hvol : ∀ y : C.Carrier, y.val ∈ cthickening δe K → ∀ t : ℝ, 0 < t → t < rstar →
      rsBall C.O w C.Xl y.val t ⊆ C.U ∧ volume (rsBall C.O w C.Xl y.val t) ≠ ⊤ ∧
      0 < (volume (rsBall C.O w C.Xl y.val t)).toReal ∧
      cv * t ^ C.G.homogeneousDimension ≤ (volume (rsBall C.O w C.Xl y.val t)).toReal ∧
      (volume (rsBall C.O w C.Xl y.val t)).toReal ≤ Cv * t ^ C.G.homogeneousDimension := by
    intro y hy t ht htr
    obtain ⟨hUl, -, -, hfin, -, hpos, -, hlow, hup, -⟩ := hb y.val hy t ht htr
    exact ⟨hUl, hfin, hpos, hlow, hup⟩
  set κ : ℝ := min (δ / 20) (rstar / 7) with hκdef
  have hκpos : 0 < κ := lt_min (by positivity) (by positivity)
  have hκ1 : κ ≤ δ / 20 := min_le_left _ _
  have hκ2 : κ ≤ rstar / 7 := min_le_right _ _
  have h6κ : 6 * κ < rstar := by linarith
  -- points of `Ω₁` lie over `LE`
  have hΩ1LE : ∀ y ∈ (thickening (2 * δ / 3) (Carrier.val ⁻¹' K : Set C.Carrier)),
      y.val ∈ cthickening δe K := by
    intro y hy
    have h1 : y ∈ cthickening δ (Carrier.val ⁻¹' K : Set C.Carrier) :=
      thickening_subset_cthickening δ _ (thickening_mono (by linarith) _ hy)
    exact (interior_subset (hcth h1) : y ∈ (Carrier.val ⁻¹' (cthickening δe K) : Set C.Carrier))
  set vHi : ℝ := max Cv cv with hvHi
  set CD : ℝ := 2 ^ C.G.homogeneousDimension * vHi / cv with hCD
  have hvHicv : cv ≤ vHi := le_max_right _ _
  have hvHipos : 0 < vHi := hcv.trans_le hvHicv
  have hCDpos : 0 < CD := by positivity
  have hCDcv : CD * cv = 2 ^ C.G.homogeneousDimension * vHi := by
    rw [hCD]
    exact div_mul_cancel₀ _ hcv.ne'
  have hCDone : 1 < CD := by
    have h2Q : (2 : ℝ) ≤ 2 ^ C.G.homogeneousDimension := by
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ C.G.homogeneousDimension := pow_le_pow_right₀ (by norm_num) hQ
    rw [hCD, lt_div_iff₀ hcv]
    nlinarith [mul_nonneg (sub_nonneg.2 h2Q) hvHipos.le]
  -- measure of balls over `Ω₁`
  have hball : ∀ y ∈ (thickening (2 * δ / 3) (Carrier.val ⁻¹' K : Set C.Carrier)),
      ∀ t : ℝ, 0 < t → t ≤ 6 * κ →
      Carrier.val '' ball y t = rsBall C.O w C.Xl y.val t ∧
      (volume : Measure C.Carrier) (ball y t) = volume (rsBall C.O w C.Xl y.val t) ∧
      volume (rsBall C.O w C.Xl y.val t) ≠ ⊤ ∧
      0 < (volume (rsBall C.O w C.Xl y.val t)).toReal ∧
      cv * t ^ C.G.homogeneousDimension ≤ (volume (rsBall C.O w C.Xl y.val t)).toReal ∧
      (volume (rsBall C.O w C.Xl y.val t)).toReal ≤ vHi * t ^ C.G.homogeneousDimension := by
    intro y hy t ht htκ
    obtain ⟨hUl, hfin, hpos, hlow, hup⟩ := hvol y (hΩ1LE y hy) t ht (by linarith)
    exact ⟨Carrier.image_val_ball_eq_rsBall hUl, Carrier.volume_ball_eq_rsBall hUl, hfin, hpos,
      hlow, hup.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))⟩
  -- the structure
  have hS : ∃ S : H2.LocDoubling C.Carrier, S.κ = κ ∧
      S.Ω₀ = thickening (δ / 3) (Carrier.val ⁻¹' K : Set C.Carrier) ∧
      S.Ω₁ = thickening (2 * δ / 3) (Carrier.val ⁻¹' K : Set C.Carrier) ∧
      S.Ω₂ = thickening δ (Carrier.val ⁻¹' K : Set C.Carrier) ∧ S.μ = volume ∧ S.C_D = CD := by
    refine ⟨{ μ := volume
              Ω₀ := thickening (δ / 3) (Carrier.val ⁻¹' K : Set C.Carrier)
              Ω₁ := thickening (2 * δ / 3) (Carrier.val ⁻¹' K : Set C.Carrier)
              Ω₂ := thickening δ (Carrier.val ⁻¹' K : Set C.Carrier)
              open₀ := isOpen_thickening
              open₁ := isOpen_thickening
              open₂ := isOpen_thickening
              sub₀₁ := thickening_mono (by linarith) _
              sub₁₂ := thickening_mono (by linarith) _
              cpt := ?_
              κ := κ
              κ_pos := hκpos
              incl₀ := ?_
              incl₁ := ?_
              C_D := CD
              one_lt_C_D := hCDone
              doubling := ?_
              noAtoms := Carrier.measure_singleton_eq_zero
              finΩ₂ := ?_ }, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · -- compactness of the closure of `Ω₂`
      refine hLt_cpt.of_isClosed_subset isClosed_closure ?_
      refine (closure_thickening_subset_cthickening δ _).trans ?_
      exact (hcth.trans interior_subset)
    · intro y hy z hz
      rw [mem_thickening_iff] at hy ⊢
      obtain ⟨a, ha, hya⟩ := hy
      refine ⟨a, ha, ?_⟩
      have hz' : dist z y ≤ 6 * κ := mem_closedBall.mp hz
      calc dist z a ≤ dist z y + dist y a := dist_triangle _ _ _
        _ < 2 * δ / 3 := by linarith
    · intro y hy z hz
      rw [mem_thickening_iff] at hy ⊢
      obtain ⟨a, ha, hya⟩ := hy
      refine ⟨a, ha, ?_⟩
      have hz' : dist z y ≤ 6 * κ := mem_closedBall.mp hz
      calc dist z a ≤ dist z y + dist y a := dist_triangle _ _ _
        _ < δ := by linarith
    · intro y hy r hr hr3
      have hr2 : 2 * r ≤ 6 * κ := by linarith
      obtain ⟨-, hv1, hfin1, hpos1, hlow1, hup1⟩ := hball y hy r hr (by linarith)
      obtain ⟨-, hv2, hfin2, hpos2, hlow2, hup2⟩ := hball y hy (2 * r) (by linarith) hr2
      rw [hv1, hv2]
      refine ⟨(ENNReal.toReal_pos_iff.mp hpos2).1, ?_, hfin1.lt_top⟩
      rw [← ENNReal.ofReal_toReal hfin2, ← ENNReal.ofReal_toReal hfin1,
        ← ENNReal.ofReal_mul hCDpos.le]
      refine ENNReal.ofReal_le_ofReal ?_
      calc (volume (rsBall C.O w C.Xl y.val (2 * r))).toReal
          ≤ vHi * (2 * r) ^ C.G.homogeneousDimension := hup2
        _ = CD * (cv * r ^ C.G.homogeneousDimension) := by
            rw [← mul_assoc CD cv, hCDcv, mul_pow]; ring
        _ ≤ CD * (volume (rsBall C.O w C.Xl y.val r)).toReal :=
            mul_le_mul_of_nonneg_left hlow1 hCDpos.le
    · -- finite measure of `Ω₂`
      rw [Carrier.volume_apply]
      refine lt_of_le_of_lt (measure_mono ?_) hLE.measure_lt_top
      rintro _ ⟨y, hy, rfl⟩
      exact (interior_subset (hcth (thickening_subset_cthickening δ _ hy)) :
        y ∈ (Carrier.val ⁻¹' (cthickening δe K) : Set C.Carrier))
  obtain ⟨S, hκS, hΩ0, hΩ1, hΩ2, hμ, hCDS⟩ := hS
  refine ⟨S, cv, vHi, ⟨hμ, hcv, hvHicv, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro y hy t ht htκ
    rw [hκS] at htκ
    rw [hΩ1] at hy
    exact (hball y hy t ht htκ).1
  · intro y hy t ht htκ
    rw [hκS] at htκ
    rw [hΩ1] at hy
    obtain ⟨-, hv, hfin, hpos, -⟩ := hball y hy t ht htκ
    rw [hμ, hv]
    exact ⟨(ENNReal.toReal_pos_iff.mp hpos).1, hfin.lt_top⟩
  · intro y hy t ht htκ
    rw [hκS] at htκ
    rw [hΩ1] at hy
    obtain ⟨-, hv, -, -, hlow, -⟩ := hball y hy t ht htκ
    rw [hμ, hv]
    exact hlow
  · intro y hy t ht htκ
    rw [hκS] at htκ
    rw [hΩ1] at hy
    obtain ⟨-, hv, -, -, -, hup⟩ := hball y hy t ht htκ
    rw [hμ, hv]
    exact hup
  · exact hCDS.trans hCD
  · intro y hy
    rw [hΩ1] at hy
    rw [hκS]
    obtain ⟨-, hv, -, -, hlow, -⟩ := hball y hy κ hκpos (by linarith)
    rw [hμ, hv]
    exact hlow
  · rw [hΩ1]
    refine hLt_cpt.isBounded.subset ?_
    intro y hy
    exact (interior_subset (hcth ((thickening_subset_cthickening δ _) (thickening_mono (by linarith) _ hy))) :
      y ∈ (Carrier.val ⁻¹' (cthickening δe K) : Set C.Carrier))
  · intro ξ hξ
    rw [hΩ0]
    exact ⟨Carrier.mk ξ (hKU hξ), self_subset_thickening (by positivity) _ hξ, rfl⟩

end LiftedChart

end RothschildStein.P1
