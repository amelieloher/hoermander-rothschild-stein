-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.ContinuityReconstructionTransfer
public import RothschildStein.H2.HolderEstimates
public import RothschildStein.H2.HolderBallExtension
public import RothschildStein.Definitions.holderENorm

/-!
# Reconstruction and extension: Hölder calculus on the carrier

The Hölder norm `holderENorm C.dl α V f` (supremum on `V` plus the infimum-defined
seminorm, lifted control distance) and the Hölder norm of H2 on the carrier (`boundedHolderNorm`,
Mathlib's least Hölder constant for the carrier metric `d = (C.dl).toReal`) are compared:

* `holderENorm_le_boundedHolderNorm`: the Hölder norm `holderENorm` of an output on `V ⊆ U` is bounded by the
  carrier norm of its pullback;
* `exists_lipschitzWith_of_contDiff_compact`: a smooth compactly supported (signed) function is
  Lipschitz for the lifted control distance (the signed version of `exists_lipschitzWith_comp_val`);
* `exists_boundedHolder_mul_extension` (**controlled Hölder extension of the input**): for a test multiplier `b` with compact support in the
  open patch `V ⊆ U` and *any* `f` of finite Hölder norm on `V`, the product `b f`, extended by
  zero into the carrier, is bounded Hölder with
  `‖b f‖_{C^α(carrier)} ≤ K ‖f‖_{C^α(V)}`; the constant depends on `b` and on the margin `δ_b`
  between `supp b` and `U ∖ V`: pairs crossing `∂V` are bounded by `δ_b^{-α} ‖b f‖_∞`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Metric
open scoped ENNReal NNReal
namespace RothschildStein.P1

/-- An increment bounded both by `M` and by `L d` is bounded by `M^{1-α} L^α d^α`
(`0 ≤ α ≤ 1`). -/
theorem abs_le_rpow_of_min_bound {M L d α e : ℝ} (hM : 0 ≤ M) (hL : 0 ≤ L) (hd : 0 ≤ d)
    (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (he0 : 0 ≤ e) (he1 : e ≤ M) (he2 : e ≤ L * d) :
    e ≤ M ^ (1 - α) * L ^ α * d ^ α := by
  rcases he0.eq_or_lt with h0 | hpos
  · rw [← h0]
    have h1 : 0 ≤ M ^ (1 - α) := Real.rpow_nonneg hM _
    have h2 : 0 ≤ L ^ α := Real.rpow_nonneg hL _
    have h3 : 0 ≤ d ^ α := Real.rpow_nonneg hd _
    positivity
  · have hsplit : e = e ^ (1 - α) * e ^ α := by
      rw [← Real.rpow_add hpos, sub_add_cancel, Real.rpow_one]
    have h1 : e ^ (1 - α) ≤ M ^ (1 - α) := Real.rpow_le_rpow he0 he1 (by linarith)
    have h2 : e ^ α ≤ (L * d) ^ α := Real.rpow_le_rpow he0 he2 hα0
    rw [Real.mul_rpow hL hd] at h2
    calc e = e ^ (1 - α) * e ^ α := hsplit
      _ ≤ M ^ (1 - α) * (L ^ α * d ^ α) :=
          mul_le_mul h1 h2 (Real.rpow_nonneg he0 _) (Real.rpow_nonneg hM _)
      _ = M ^ (1 - α) * L ^ α * d ^ α := by ring

/-- A finite Hölder seminorm gives the pointwise bound with its real value
(a copy of the P2 statement, for `holderSeminorm`). -/
theorem abs_sub_le_of_frozenHolderSeminorm {n' : ℕ}
    {d : (Fin n' → ℝ) → (Fin n' → ℝ) → ℝ≥0∞} {α : ℝ} (hα : 0 ≤ α) {V : Set (Fin n' → ℝ)}
    {f : (Fin n' → ℝ) → ℝ} (hf : holderSeminorm d α V f ≠ ⊤) {x y : Fin n' → ℝ} (hx : x ∈ V)
    (hy : y ∈ V) (hxy : d x y ≠ ⊤) :
    |f x - f y| ≤ (holderSeminorm d α V f).toReal * (d x y).toReal ^ α := by
  have hset : {C : ℝ≥0∞ | C < ⊤ ∧ ∀ x ∈ V, ∀ y ∈ V, d x y < ⊤ →
      ENNReal.ofReal |f x - f y| ≤ C * d x y ^ α}.Nonempty := by
    by_contra hne
    rw [not_nonempty_iff_eq_empty] at hne
    exact hf (by unfold holderSeminorm; rw [hne, sInf_empty])
  have hpow : d x y ^ α ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg hα hxy
  have hle : ENNReal.ofReal |f x - f y| ≤ holderSeminorm d α V f * d x y ^ α := by
    obtain ⟨C0, hC0⟩ := hset
    unfold holderSeminorm
    rw [sInf_eq_iInf', ENNReal.iInf_mul' (fun h => absurd h hpow) (fun _ => ⟨⟨C0, hC0⟩⟩)]
    exact le_iInf fun C => C.2.2 x hx y hy (lt_top_iff_ne_top.mpr hxy)
  have hrhs : holderSeminorm d α V f * d x y ^ α ≠ ⊤ := ENNReal.mul_ne_top hf hpow
  have := ENNReal.toReal_mono hrhs hle
  rwa [ENNReal.toReal_ofReal (abs_nonneg _), ENNReal.toReal_mul, ← ENNReal.toReal_rpow] at this

/-- The Hölder seminorm is bounded by any real constant for which the pointwise
bound holds (a copy of the P2 statement). -/
theorem frozenHolderSeminorm_le_of_bound {n' : ℕ} {d : (Fin n' → ℝ) → (Fin n' → ℝ) → ℝ≥0∞}
    {α : ℝ} (hα : 0 ≤ α) {V : Set (Fin n' → ℝ)} {f : (Fin n' → ℝ) → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x ∈ V, ∀ y ∈ V, d x y ≠ ⊤ → |f x - f y| ≤ C * (d x y).toReal ^ α) :
    holderSeminorm d α V f ≤ ENNReal.ofReal C := by
  refine sInf_le ⟨ENNReal.ofReal_lt_top, fun x hx y hy hxy => ?_⟩
  have hxy' : d x y ≠ ⊤ := hxy.ne
  have hpow : d x y ^ α = ENNReal.ofReal ((d x y).toReal ^ α) := by
    conv_lhs => rw [← ENNReal.ofReal_toReal hxy']
    exact ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hα
  rw [hpow, ← ENNReal.ofReal_mul hC]
  exact ENNReal.ofReal_le_ofReal (h x hx y hy hxy')

/-- A bounded Lipschitz function is bounded Hölder on the whole space for every
exponent at most one (no diameter bound is needed: `min (2M, L d) ≤ (2M)^{1-δ} (L d)^δ`). -/
theorem boundedHolder_univ_of_lipschitz {Y : Type*} [MetricSpace Y] {A : Y → ℝ} {L : ℝ≥0}
    (hl : LipschitzWith L A) {M : ℝ} (hM : ∀ y, |A y| ≤ M) {δ : ℝ≥0} (hδ : δ ≤ 1) :
    H2.BoundedHolder δ univ A := by
  have hM' : ∀ y, |A y| ≤ max M 0 := fun y => (hM y).trans (le_max_left _ _)
  have hM0 : 0 ≤ max M 0 := le_max_right _ _
  have hδ1 : (δ : ℝ) ≤ 1 := by exact_mod_cast hδ
  have hsup : H2.holderSup univ A ≤ ENNReal.ofReal (max M 0) :=
    H2.holderSup_le_of_bound (fun x _ => hM' x)
  have hsemi : H2.holderSemi δ univ A ≤
      ENNReal.ofReal ((2 * max M 0) ^ (1 - (δ : ℝ)) * (L : ℝ) ^ (δ : ℝ)) := by
    refine H2.holderSemi_le_of_bound (by positivity) (fun x _ y _ => ?_)
    have he1 : |A x - A y| ≤ 2 * max M 0 := by
      calc |A x - A y| ≤ |A x| + |A y| := abs_sub _ _
        _ ≤ max M 0 + max M 0 := add_le_add (hM' x) (hM' y)
        _ = 2 * max M 0 := by ring
    have he2 : |A x - A y| ≤ (L : ℝ) * dist x y := by
      have := hl.dist_le_mul x y
      rwa [Real.dist_eq] at this
    exact abs_le_rpow_of_min_bound (by positivity) L.coe_nonneg dist_nonneg δ.coe_nonneg hδ1
      (abs_nonneg _) he1 he2
  unfold H2.BoundedHolder H2.boundedHolderNorm
  exact (add_le_add hsup hsemi).trans_lt
    (ENNReal.add_lt_top.mpr ⟨ENNReal.ofReal_lt_top, ENNReal.ofReal_lt_top⟩)

namespace LiftedChart

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  {C : LiftedChart w s Ω hΩ X x₀ m}

/-- The Hölder norm of a function on `V ⊆ U` is bounded by the carrier Hölder norm
of its pullback to the carrier (lifted control distance, `0 < α`). -/
theorem holderENorm_le_boundedHolderNorm {V : Set (Fin (n + m) → ℝ)} (hVU : V ⊆ C.U) {α : ℝ}
    (hα : 0 < α) (v : (Fin (n + m) → ℝ) → ℝ) :
    holderENorm C.dl α V v ≤
      H2.boundedHolderNorm α.toNNReal univ (fun y : C.Carrier => v y.val) := by
  set g : C.Carrier → ℝ := fun y => v y.val with hg
  by_cases hT : H2.boundedHolderNorm α.toNNReal univ g = ⊤
  · rw [hT]; exact le_top
  · have hlt : H2.BoundedHolder α.toNNReal univ g := lt_top_iff_ne_top.mpr hT
    obtain ⟨hsup, hsem⟩ := hlt.parts
    unfold holderENorm
    refine add_le_add ?_ ?_
    · refine iSup_le fun x => ?_
      have := le_iSup (fun y : (univ : Set C.Carrier) => ENNReal.ofReal |g y|)
        ⟨Carrier.mk x.1 (hVU x.2), mem_univ _⟩
      exact this
    · have hle := frozenHolderSeminorm_le_of_bound (d := C.dl) (V := V) (f := v) hα.le
        (C := (H2.holderSemi α.toNNReal univ g).toReal) ENNReal.toReal_nonneg (by
          intro x hx y hy hxy
          have h1 := H2.sub_le_holderSemi hsem (mem_univ (Carrier.mk x (hVU hx)))
            (mem_univ (Carrier.mk y (hVU hy)))
          have h2 : dist (Carrier.mk x (hVU hx)) (Carrier.mk y (hVU hy)) =
              (C.dl x y).toReal := rfl
          rw [h2, Real.coe_toNNReal _ hα.le] at h1
          exact h1)
      rwa [ENNReal.ofReal_toReal hsem.ne] at hle

/-- **A smooth compactly supported function is Lipschitz for the lifted control
distance** (the signed version of `exists_lipschitzWith_comp_val`): near the support integrate
the derivative along a controlled curve; far from it the sup bound `2 M` is controlled by
`d̃/δ`. -/
theorem exists_lipschitzWith_of_contDiff_compact {g : (Fin (n + m) → ℝ) → ℝ}
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) {Mg : ℝ} (hMg : ∀ ξ, |g ξ| ≤ Mg)
    (hc : IsCompact (tsupport g)) (hU : tsupport g ⊆ C.U) :
    ∃ L : ℝ≥0, LipschitzWith L (fun x : C.Carrier => g x.val) := by
  have hMg0 : 0 ≤ Mg := (abs_nonneg _).trans (hMg 0)
  obtain ⟨δe, hδe, hLU⟩ := hc.exists_cthickening_subset_open C.isOpen_U hU
  have hLc : IsCompact (cthickening δe (tsupport g)) := hc.cthickening
  set K' : Set C.Carrier := Carrier.val ⁻¹' tsupport g with hK'
  set L' : Set C.Carrier := Carrier.val ⁻¹' cthickening δe (tsupport g) with hL'
  have hK'c : IsCompact K' := Carrier.isCompact_preimage_val hc hU
  have hL'c : IsCompact L' := Carrier.isCompact_preimage_val hLc hLU
  have hKint : K' ⊆ interior L' := by
    have h1 : (Carrier.val ⁻¹' thickening δe (tsupport g) : Set C.Carrier) ⊆ interior L' :=
      interior_maximal (preimage_mono (thickening_subset_cthickening δe _))
        (isOpen_thickening.preimage Carrier.continuous_val)
    exact (preimage_mono (self_subset_thickening hδe _)).trans h1
  obtain ⟨δ, hδ, hcth⟩ := hK'c.exists_cthickening_subset_open isOpen_interior hKint
  have hLimg : IsCompact (Carrier.val '' L' : Set (Fin (n + m) → ℝ)) :=
    hL'c.image Carrier.continuous_val
  have hLimgU : Carrier.val '' L' ⊆ C.U := by
    rintro _ ⟨x, -, rfl⟩
    exact x.val_mem
  have hG : ContDiffOn ℝ 1 (fun p : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => g p.1)
      (C.U ×ˢ C.U) :=
    (hg.comp contDiff_fst).contDiffOn.of_le (by simp)
  obtain ⟨M, hM0, hM⟩ := C.exists_lipschitz_first hG hLimg hLimgU
  have hδinv : 0 ≤ 2 * Mg / δ := by positivity
  have key : ∀ x y : C.Carrier, x ∈ K' → |g x.val - g y.val| ≤ (M + 2 * Mg / δ) * dist x y := by
    intro x y hx
    by_cases hxy : dist x y < δ
    · have hxL : x ∈ L' := interior_subset (hKint hx)
      have hyL : y ∈ L' := interior_subset (hcth
        (Metric.mem_cthickening_of_dist_le y x δ K' hx (by rw [dist_comm]; exact hxy.le)))
      have h1 : |g y.val - g x.val| ≤ M * (C.dl x.val y.val).toReal :=
        hM x.val ⟨x, hxL, rfl⟩ y.val ⟨y, hyL, rfl⟩ x.val ⟨x, hxL, rfl⟩
      have h2 : (C.dl x.val y.val).toReal = dist x y := rfl
      rw [h2] at h1
      rw [abs_sub_comm]
      exact h1.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hδinv) dist_nonneg)
    · have hge : δ ≤ dist x y := not_lt.mp hxy
      have h1 : |g x.val - g y.val| ≤ 2 * Mg := by
        calc |g x.val - g y.val| ≤ |g x.val| + |g y.val| := abs_sub _ _
          _ ≤ Mg + Mg := add_le_add (hMg _) (hMg _)
          _ = 2 * Mg := by ring
      have h2 : 2 * Mg ≤ (2 * Mg / δ) * dist x y := by
        calc 2 * Mg = (2 * Mg / δ) * δ := by field_simp
          _ ≤ (2 * Mg / δ) * dist x y := mul_le_mul_of_nonneg_left hge hδinv
      calc |g x.val - g y.val| ≤ 2 * Mg := h1
        _ ≤ (2 * Mg / δ) * dist x y := h2
        _ ≤ (M + 2 * Mg / δ) * dist x y :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hM0) dist_nonneg
  refine ⟨⟨M + 2 * Mg / δ, add_nonneg hM0 hδinv⟩, LipschitzWith.of_dist_le_mul fun x y => ?_⟩
  rw [Real.dist_eq]
  by_cases hx : x ∈ K'
  · exact key x y hx
  · by_cases hy : y ∈ K'
    · rw [abs_sub_comm, dist_comm x y]
      exact key y x hy
    · have h1 : g x.val = 0 := image_eq_zero_of_notMem_tsupport hx
      have h2 : g y.val = 0 := image_eq_zero_of_notMem_tsupport hy
      rw [h1, h2, sub_self, abs_zero]
      exact mul_nonneg (add_nonneg hM0 hδinv) dist_nonneg

/-- A smooth compactly supported function with support in `U` has finite Hölder
norm on every `V ⊆ U`, for every exponent `0 < α ≤ 1`. -/
theorem holderENorm_ne_top_of_contDiff_compact {V : Set (Fin (n + m) → ℝ)} (hVU : V ⊆ C.U)
    {g : (Fin (n + m) → ℝ) → ℝ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g)
    (hgU : tsupport g ⊆ C.U) {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) :
    holderENorm C.dl α V g ≠ ⊤ := by
  obtain ⟨Mg, hMg⟩ := hg.continuous.bounded_above_of_compact_support hgc
  obtain ⟨L, hL⟩ := exists_lipschitzWith_of_contDiff_compact (C := C) hg
    (fun ξ => by simpa using hMg ξ) hgc hgU
  have hH := boundedHolder_univ_of_lipschitz hL (M := Mg) (fun y => by simpa using hMg y.val)
    (δ := α.toNNReal) (by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hα0.le]
      exact_mod_cast hα1)
  exact ne_top_of_le_ne_top hH.ne
    (holderENorm_le_boundedHolderNorm hVU hα0 g)

/-- **The margin `δ_b`**: a compact set `K ⊆ V` with `V ⊆ U` open has a positive distance
(for the carrier metric) from `U ∖ V`. -/
theorem exists_margin_val {V : Set (Fin (n + m) → ℝ)} (hVo : IsOpen V) (hVU : V ⊆ C.U)
    {K : Set (Fin (n + m) → ℝ)} (hK : IsCompact K) (hKV : K ⊆ V) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x y : C.Carrier, x.val ∈ K → y.val ∉ V → δ ≤ dist x y := by
  have hK' : IsCompact (Carrier.val ⁻¹' K : Set C.Carrier) :=
    Carrier.isCompact_preimage_val hK (hKV.trans hVU)
  have hV' : IsOpen (Carrier.val ⁻¹' V : Set C.Carrier) := hVo.preimage Carrier.continuous_val
  obtain ⟨δ, hδ, hcth⟩ := hK'.exists_cthickening_subset_open hV' (preimage_mono hKV)
  refine ⟨δ, hδ, fun x y hx hy => ?_⟩
  by_contra hlt
  have hlt' : dist x y < δ := not_le.mp hlt
  have hyc : y ∈ cthickening δ (Carrier.val ⁻¹' K : Set C.Carrier) :=
    Metric.mem_cthickening_of_dist_le y x δ _ hx (by rw [dist_comm]; exact hlt'.le)
  exact hy (hcth hyc)

/-- **Controlled Hölder extension of the input** (BB
pp. 295–296; "for inputs, extend `bf`, not arbitrary `f`"). Let `V ⊆ U` be
open and `b` a smooth function with compact support in `V`. There is a constant `K` (depending on
`b`, through `sup |b|`, its Lipschitz constant for `d̃` and the margin `δ_b` between `supp b` and
`U ∖ V`, and on `α`) such that for every function `f` of finite Hölder norm on `V` the
product `b f`, extended by zero to the carrier, satisfies
`‖b f‖_{C^α(carrier)} ≤ K ‖f‖_{C^α(V)}`. Pairs inside `V` use the product rule; pairs crossing
`∂V` are bounded by `δ_b^{-α} ‖b f‖_∞`. -/
theorem exists_boundedHolder_mul_extension {V : Set (Fin (n + m) → ℝ)} (hVo : IsOpen V)
    (hVU : V ⊆ C.U) {b : (Fin (n + m) → ℝ) → ℝ} (hbd : ContDiff ℝ (⊤ : ℕ∞) b)
    (hbc : HasCompactSupport b) (hbV : tsupport b ⊆ V) {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ f : (Fin (n + m) → ℝ) → ℝ,
      H2.boundedHolderNorm α.toNNReal univ (fun y : C.Carrier => b y.val * f y.val) ≤
        ENNReal.ofReal K * holderENorm C.dl α V f := by
  obtain ⟨Mb, hMb⟩ := hbd.continuous.bounded_above_of_compact_support hbc
  have hMb' : ∀ ξ, |b ξ| ≤ Mb := fun ξ => by simpa using hMb ξ
  have hMb0 : 0 ≤ Mb := (abs_nonneg _).trans (hMb' 0)
  obtain ⟨Lb, hLb⟩ := exists_lipschitzWith_of_contDiff_compact (C := C) hbd hMb' hbc
    (hbV.trans hVU)
  obtain ⟨δb, hδb, hmargin⟩ := exists_margin_val (C := C) hVo hVU hbc.isCompact hbV
  set cb : ℝ := (2 * Mb) ^ (1 - α) * (Lb : ℝ) ^ α with hcb
  have hcb0 : 0 ≤ cb := by
    have h1 : 0 ≤ (2 * Mb) ^ (1 - α) := Real.rpow_nonneg (by positivity) _
    have h2 : 0 ≤ (Lb : ℝ) ^ α := Real.rpow_nonneg Lb.coe_nonneg _
    rw [hcb]; positivity
  set ib : ℝ := δb ^ (-α) with hib
  have hib0 : 0 ≤ ib := Real.rpow_nonneg hδb.le _
  set K : ℝ := Mb + cb + Mb * ib + 1 with hK
  have hKpos : 0 < K := by rw [hK]; positivity
  refine ⟨K, hKpos, fun f => ?_⟩
  by_cases hT : holderENorm C.dl α V f = ⊤
  · rw [hT, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hKpos).ne']
    exact le_top
  · have hsup_ne : (⨆ x : V, ENNReal.ofReal |f x|) ≠ ⊤ :=
      ne_top_of_le_ne_top hT le_self_add
    have hsem_ne : holderSeminorm C.dl α V f ≠ ⊤ :=
      ne_top_of_le_ne_top hT le_add_self
    set Mf : ℝ := (⨆ x : V, ENNReal.ofReal |f x|).toReal with hMf
    set Sf : ℝ := (holderSeminorm C.dl α V f).toReal with hSf
    have hMf0 : 0 ≤ Mf := ENNReal.toReal_nonneg
    have hSf0 : 0 ≤ Sf := ENNReal.toReal_nonneg
    have hp1 : ∀ x ∈ V, |f x| ≤ Mf := fun x hx =>
      (ENNReal.ofReal_le_iff_le_toReal hsup_ne).mp
        (le_iSup (fun x : V => ENNReal.ofReal |f x|) ⟨x, hx⟩)
    have hp2 : ∀ x ∈ V, ∀ y ∈ V, |f x - f y| ≤ Sf * (C.dl x y).toReal ^ α := fun x hx y hy =>
      abs_sub_le_of_frozenHolderSeminorm hα0.le hsem_ne hx hy (C.dl_ne_top (hVU hx) (hVU hy))
    have hnorm : holderENorm C.dl α V f = ENNReal.ofReal Mf + ENNReal.ofReal Sf := by
      unfold holderENorm
      rw [hMf, hSf, ENNReal.ofReal_toReal hsup_ne, ENNReal.ofReal_toReal hsem_ne]
    have hδα : ((α.toNNReal : ℝ≥0) : ℝ) = α := Real.coe_toNNReal _ hα0.le
    set Hc : ℝ := Mb * Sf + (cb + Mb * ib) * Mf with hHc
    have hHc0 : 0 ≤ Hc := by rw [hHc]; positivity
    have hb0 : ∀ y : C.Carrier, y.val ∉ V → b y.val = 0 := fun y hy =>
      image_eq_zero_of_notMem_tsupport (fun h => hy (hbV h))
    -- the crossing estimate
    have hcross : ∀ x y : C.Carrier, x.val ∈ V → y.val ∉ V →
        |b x.val * f x.val - b y.val * f y.val| ≤ Mb * ib * Mf * dist x y ^ α := by
      intro x y hx hy
      rw [hb0 y hy, zero_mul, sub_zero, abs_mul]
      by_cases hbx : b x.val = 0
      · rw [hbx, abs_zero, zero_mul]
        have : 0 ≤ dist x y ^ α := Real.rpow_nonneg dist_nonneg _
        positivity
      · have hxs : x.val ∈ tsupport b := subset_tsupport _ hbx
        have hd := hmargin x y hxs hy
        have h1 : δb ^ α ≤ dist x y ^ α := Real.rpow_le_rpow hδb.le hd hα0.le
        have h2 : 1 ≤ ib * dist x y ^ α := by
          have : ib * δb ^ α = 1 := by
            rw [hib, ← Real.rpow_add hδb, neg_add_cancel, Real.rpow_zero]
          calc (1 : ℝ) = ib * δb ^ α := this.symm
            _ ≤ ib * dist x y ^ α := mul_le_mul_of_nonneg_left h1 hib0
        have h3 : |b x.val| * |f x.val| ≤ Mb * Mf :=
          mul_le_mul (hMb' _) (hp1 _ hx) (abs_nonneg _) hMb0
        calc |b x.val| * |f x.val| ≤ Mb * Mf := h3
          _ = Mb * Mf * 1 := by ring
          _ ≤ Mb * Mf * (ib * dist x y ^ α) :=
              mul_le_mul_of_nonneg_left h2 (mul_nonneg hMb0 hMf0)
          _ = Mb * ib * Mf * dist x y ^ α := by ring
    have hpoint : ∀ x y : C.Carrier,
        |b x.val * f x.val - b y.val * f y.val| ≤ Hc * dist x y ^ α := by
      intro x y
      have hdn : 0 ≤ dist x y ^ α := Real.rpow_nonneg dist_nonneg _
      by_cases hx : x.val ∈ V <;> by_cases hy : y.val ∈ V
      · -- both inside `V`
        have hbl : |b x.val - b y.val| ≤ cb * dist x y ^ α := by
          have he1 : |b x.val - b y.val| ≤ 2 * Mb := by
            calc |b x.val - b y.val| ≤ |b x.val| + |b y.val| := abs_sub _ _
              _ ≤ Mb + Mb := add_le_add (hMb' _) (hMb' _)
              _ = 2 * Mb := by ring
          have he2 : |b x.val - b y.val| ≤ (Lb : ℝ) * dist x y := by
            have := hLb.dist_le_mul x y
            rwa [Real.dist_eq] at this
          exact abs_le_rpow_of_min_bound (by positivity) Lb.coe_nonneg dist_nonneg hα0.le hα1
            (abs_nonneg _) he1 he2
        have hfl : |f x.val - f y.val| ≤ Sf * dist x y ^ α := hp2 _ hx _ hy
        have hid : b x.val * f x.val - b y.val * f y.val =
            b x.val * (f x.val - f y.val) + f y.val * (b x.val - b y.val) := by ring
        rw [hid]
        calc |b x.val * (f x.val - f y.val) + f y.val * (b x.val - b y.val)|
            ≤ |b x.val * (f x.val - f y.val)| + |f y.val * (b x.val - b y.val)| := abs_add_le _ _
          _ ≤ Mb * (Sf * dist x y ^ α) + Mf * (cb * dist x y ^ α) := by
            rw [abs_mul, abs_mul]
            exact add_le_add (mul_le_mul (hMb' _) hfl (abs_nonneg _) hMb0)
              (mul_le_mul (hp1 _ hy) hbl (abs_nonneg _) hMf0)
          _ ≤ Hc * dist x y ^ α := by
            rw [hHc]
            have : 0 ≤ Mb * ib * Mf * dist x y ^ α := by positivity
            nlinarith [mul_nonneg hMf0 hdn, mul_nonneg hMb0 hdn]
      · refine (hcross x y hx hy).trans (mul_le_mul_of_nonneg_right ?_ hdn)
        rw [hHc]; nlinarith [mul_nonneg hMb0 hSf0, mul_nonneg (mul_nonneg hMb0 hib0) hMf0,
          mul_nonneg hcb0 hMf0]
      · rw [abs_sub_comm]
        have hc := hcross y x hy hx
        rw [dist_comm y x] at hc
        refine hc.trans (mul_le_mul_of_nonneg_right ?_ hdn)
        rw [hHc]; nlinarith [mul_nonneg hMb0 hSf0, mul_nonneg (mul_nonneg hMb0 hib0) hMf0,
          mul_nonneg hcb0 hMf0]
      · rw [hb0 x hx, hb0 y hy]
        simp only [zero_mul, sub_self, abs_zero]
        positivity
    have hsup' : H2.holderSup univ (fun y : C.Carrier => b y.val * f y.val) ≤
        ENNReal.ofReal (Mb * Mf) := by
      refine H2.holderSup_le_of_bound (fun y _ => ?_)
      by_cases hy : y.val ∈ V
      · rw [abs_mul]
        exact mul_le_mul (hMb' _) (hp1 _ hy) (abs_nonneg _) hMb0
      · rw [hb0 y hy, zero_mul, abs_zero]; positivity
    have hsemi' : H2.holderSemi α.toNNReal univ (fun y : C.Carrier => b y.val * f y.val) ≤
        ENNReal.ofReal Hc := by
      refine H2.holderSemi_le_of_bound hHc0 (fun x _ y _ => ?_)
      rw [hδα]
      exact hpoint x y
    have hsum : Mb * Mf + Hc ≤ K * (Mf + Sf) := by
      rw [hHc, hK]
      nlinarith [mul_nonneg hMb0 hMf0, mul_nonneg hMb0 hSf0, mul_nonneg hcb0 hMf0,
        mul_nonneg (mul_nonneg hMb0 hib0) hMf0, hMf0, hSf0]
    calc H2.boundedHolderNorm α.toNNReal univ (fun y : C.Carrier => b y.val * f y.val)
        = H2.holderSup univ (fun y : C.Carrier => b y.val * f y.val) +
            H2.holderSemi α.toNNReal univ (fun y : C.Carrier => b y.val * f y.val) := rfl
      _ ≤ ENNReal.ofReal (Mb * Mf) + ENNReal.ofReal Hc := add_le_add hsup' hsemi'
      _ = ENNReal.ofReal (Mb * Mf + Hc) := (ENNReal.ofReal_add (mul_nonneg hMb0 hMf0) hHc0).symm
      _ ≤ ENNReal.ofReal (K * (Mf + Sf)) := ENNReal.ofReal_le_ofReal hsum
      _ = ENNReal.ofReal K * holderENorm C.dl α V f := by
          rw [hnorm, ENNReal.ofReal_mul hKpos.le, ENNReal.ofReal_add hMf0 hSf0]

end LiftedChart

end RothschildStein.P1
