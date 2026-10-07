-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.RestrictedErrorMeasurable
public import RothschildStein.P1.SingularSplitEstimatesProduct

/-!
# Positive-type continuity: measure data on a compact patch

The abstract dyadic-shell machinery of the restricted-error estimates (`ShellData`, `SliceBounds`; Schur bound, sup bound and
Hölder bound on a measurable set with a homogeneous ball bound) is instantiated on an arbitrary
compact patch `S ⊆ U` of a lifted chart, not only on a small ball `U_r`:

* `exists_shellData_patch`: the real lifted distance `d̃` on a compact `S ⊆ U` satisfies `ShellData`
  (ball volume `≤ Cv t^Q` for all radii: the lifted volume bounds `ball_bounds` for small radii and
  the finite total volume of `S` for large radii);
* `HasKernelBounds.of_le_exponent` and `hasKernelBounds_one_of_bounded_lipschitz`: kernels with bounds
  of every exponent `ℓ ≥ 1`, and bounded `d̃`-Lipschitz regular kernels, have bounds of exponent
  `ℓ = 1` on a compact patch (`d̃` is bounded there);
* `exists_sliceBounds_of_hasKernelBounds`: the exponent-one bounds are the abstract `SliceBounds`.

(BB p. 544, Prop. 11.10; p. 297, Lemma 7.5.)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace RothschildStein.P1
namespace LiftedChart

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  (C : LiftedChart w s Ω hΩ X x₀ m)

/-- The `d̃`-ball of every radius centred in `U`, inside `U`, is open (the control-metric
topology of the chart domain is the Euclidean one, `H2CertificateCarrier`). -/
theorem isOpen_dl_ball {x : Fin (n + m) → ℝ} (hx : x ∈ C.U) (t : ℝ) :
    IsOpen {y | y ∈ C.U ∧ (C.dl x y).toReal < t} := by
  have h : {y | y ∈ C.U ∧ (C.dl x y).toReal < t} =
      Carrier.val '' (Metric.ball (Carrier.mk x hx) t) := by
    ext y
    constructor
    · rintro ⟨hy, hyt⟩
      refine ⟨Carrier.mk y hy, ?_, rfl⟩
      rw [Metric.mem_ball, Carrier.dist_def]
      show (C.dl y x).toReal < t
      rw [C.dl_symm y x]
      exact hyt
    · rintro ⟨z, hz, rfl⟩
      refine ⟨z.val_mem, ?_⟩
      rw [Metric.mem_ball, Carrier.dist_def] at hz
      have hz' : (C.dl z.val x).toReal < t := hz
      rw [C.dl_symm z.val x] at hz'
      exact hz'
  rw [h]
  exact Carrier.isOpenEmbedding_val.isOpenMap _ Metric.isOpen_ball

/-- **Measure data on a compact patch** (as in the growth bound for type kernels: the shell volume is at most
`C (2^{-j} A)^Q`): for a compact `S ⊆ U` the real lifted distance satisfies the abstract
`ShellData` hypotheses of the restricted-error estimates, with `ρ` above the `d̃`-diameter of `S` and `Cv` bounding the volume
of `d̃`-balls inside `S` by `Cv t^Q` at every radius `t` (small radii: `ball_bounds`; large radii:
the finite volume of `S`). -/
theorem exists_shellData_patch {S : Set (Fin (n + m) → ℝ)} (hS : IsCompact S) (hSU : S ⊆ C.U) :
    ∃ ρ Cv : ℝ, ShellData volume S (fun x y => (C.dl x y).toReal)
      (C.G.homogeneousDimension - 1) ρ Cv := by
  obtain ⟨D₀, hD₀, hD⟩ := C.exists_dl_bound hS hSU
  obtain ⟨rb, cv, Cv, δ, cf, Cf, hrb, hcv, hCv, hδ, hδ1, hcf, hCf, hball⟩ :=
    C.ball_bounds S hS hSU
  have hQ : 1 ≤ C.G.homogeneousDimension := G2.homogeneousDimension_pos C.G
  have hQ' : C.G.homogeneousDimension - 1 + 1 = C.G.homogeneousDimension :=
    Nat.sub_add_cancel hQ
  have hvS : volume S < ⊤ := hS.measure_lt_top
  have hvS0 : 0 ≤ (volume S).toReal := ENNReal.toReal_nonneg
  have hrbQ : 0 < rb ^ C.G.homogeneousDimension := pow_pos hrb _
  have hdiv : 0 ≤ (volume S).toReal / rb ^ C.G.homogeneousDimension := div_nonneg hvS0 hrbQ.le
  refine ⟨D₀, max Cv ((volume S).toReal / rb ^ C.G.homogeneousDimension), ?_⟩
  refine ⟨hS.measurableSet, hD₀, le_max_of_le_left hCv.le, fun x _ y _ => ENNReal.toReal_nonneg,
    fun x hx => ?_, fun x hx y hy => ?_, fun x hx y hy z hz => ?_, fun x hx y hy => ?_,
    fun x hx t ht htr => ?_, fun x hx t ht htr => ?_⟩
  · show (C.dl x x).toReal = 0
    rw [(C.dl_eq_zero_iff (hSU hx) (hSU hx)).mpr rfl]
    rfl
  · exact congrArg ENNReal.toReal (C.dl_symm x y)
  · exact C.dl_toReal_triangle (hSU hx) (hSU hy) (hSU hz)
  · have := hD x hx y hy
    show (C.dl x y).toReal < 2 * D₀
    linarith
  · show MeasurableSet (S ∩ {y | (C.dl x y).toReal < t})
    have : S ∩ {y | (C.dl x y).toReal < t} = S ∩ {y | y ∈ C.U ∧ (C.dl x y).toReal < t} := by
      ext y
      simp only [mem_inter_iff, mem_ofPred_eq]
      exact ⟨fun h => ⟨h.1, hSU h.1, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
    rw [this]
    exact hS.measurableSet.inter (C.isOpen_dl_ball (hSU hx) t).measurableSet
  · rw [hQ']
    by_cases htb : t < rb
    · obtain ⟨-, -, -, hfin, -, -, -, -, hup, -⟩ := hball x hx t ht htb
      have hsub : S ∩ {y | (C.dl x y).toReal < t} ⊆ rsBall C.O w C.Xl x t := by
        rintro y ⟨hy, hyt⟩
        exact ⟨C.U_subset_O (hSU hy),
          (ENNReal.lt_ofReal_iff_toReal_lt (C.dl_ne_top (hSU hx) (hSU hy))).mpr hyt⟩
      calc volume (S ∩ {y | (C.dl x y).toReal < t})
          ≤ volume (rsBall C.O w C.Xl x t) := measure_mono hsub
        _ = ENNReal.ofReal (volume (rsBall C.O w C.Xl x t)).toReal :=
          (ENNReal.ofReal_toReal hfin).symm
        _ ≤ ENNReal.ofReal (Cv * t ^ C.G.homogeneousDimension) := ENNReal.ofReal_le_ofReal hup
        _ ≤ _ := ENNReal.ofReal_le_ofReal
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg ht.le _))
    · replace htb := not_lt.mp htb
      calc volume (S ∩ {y | (C.dl x y).toReal < t}) ≤ volume S := measure_mono inter_subset_left
        _ = ENNReal.ofReal (volume S).toReal := (ENNReal.ofReal_toReal hvS.ne).symm
        _ ≤ _ := ENNReal.ofReal_le_ofReal ?_
      calc (volume S).toReal
          = (volume S).toReal / rb ^ C.G.homogeneousDimension * rb ^ C.G.homogeneousDimension :=
            (div_mul_cancel₀ _ hrbQ.ne').symm
        _ ≤ (volume S).toReal / rb ^ C.G.homogeneousDimension * t ^ C.G.homogeneousDimension :=
            mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hrb.le htb _) hdiv
        _ ≤ max Cv ((volume S).toReal / rb ^ C.G.homogeneousDimension) *
              t ^ C.G.homogeneousDimension :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg ht.le _)

variable {C}

/-- Two kernels that agree off the diagonal have the same kernel bounds (the kernel bounds
only evaluate the kernel at distinct points: if `d̃(ξ', η) > 2 d̃(ξ, ξ')` then `ξ' ≠ η` and
`ξ ≠ η`). -/
theorem HasKernelBounds.congr_off_diagonal {L : Set (Fin (n + m) → ℝ)} {ℓ : ℕ}
    {κ₁ κ₂ : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ} (hLU : L ⊆ C.U)
    (h : C.HasKernelBounds L ℓ κ₁) (he : ∀ ξ η, ξ ≠ η → κ₁ ξ η = κ₂ ξ η) :
    C.HasKernelBounds L ℓ κ₂ := by
  obtain ⟨A, S, hA, hS, hsz, hdf⟩ := h
  refine ⟨A, S, hA, hS, fun ξ hξ η hη hne => ?_, fun ξ hξ ξ' hξ' η hη hsep => ?_⟩
  · rw [← he ξ η hne]
    exact hsz ξ hξ η hη hne
  · have hh0 : 0 ≤ (C.dl ξ ξ').toReal := ENNReal.toReal_nonneg
    have hr0 : 0 < (C.dl ξ' η).toReal := by linarith
    have hξ'η : ξ' ≠ η := C.ne_of_dl_toReal_pos (hLU hξ') hr0
    have hxlo : (C.dl ξ' η).toReal - (C.dl ξ ξ').toReal ≤ (C.dl ξ η).toReal := by
      have := C.dl_toReal_triangle (hLU hξ') (hLU hξ) (hLU hη)
      have hs : (C.dl ξ' ξ).toReal = (C.dl ξ ξ').toReal := by rw [C.dl_symm ξ' ξ]
      linarith
    have hxpos : 0 < (C.dl ξ η).toReal := by linarith
    have hξη : ξ ≠ η := C.ne_of_dl_toReal_pos (hLU hξ) hxpos
    rw [← he ξ' η hξ'η, ← he ξ η hξη, ← he η ξ' hξ'η.symm, ← he η ξ hξη.symm]
    exact hdf ξ hξ ξ' hξ' η hη hsep

/-- **Exponents `ℓ ≥ 1` reduce to the exponent `1`** on a compact patch: `d̃` is bounded by
some `D₁ ≥ 1` there, so `d̃^(ℓ - Q) ≤ D₁^(ℓ-1) d̃^(1 - Q)` and
`1 / d̃^(Q + 1 - ℓ) ≤ D₁^(ℓ-1) / d̃^Q`. -/
theorem HasKernelBounds.of_le_exponent {L : Set (Fin (n + m) → ℝ)} {ℓ : ℕ}
    {κ : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ} (hL : IsCompact L) (hLU : L ⊆ C.U)
    (hℓ : 1 ≤ ℓ) (h : C.HasKernelBounds L ℓ κ) : C.HasKernelBounds L 1 κ := by
  obtain ⟨e, rfl⟩ : ∃ e, ℓ = e + 1 := ⟨ℓ - 1, by omega⟩
  obtain ⟨A, S, hA, hS, hsz, hdf⟩ := h
  obtain ⟨D₀, hD₀, hD⟩ := C.exists_dl_bound hL hLU
  have hD₁1 : 1 ≤ max 1 D₀ := le_max_left _ _
  have hD₁0 : 0 ≤ max 1 D₀ := zero_le_one.trans hD₁1
  have hc0 : 0 ≤ max 1 D₀ ^ e := pow_nonneg hD₁0 e
  refine ⟨A * max 1 D₀ ^ e, S * max 1 D₀ ^ e, mul_nonneg hA hc0, mul_nonneg hS hc0, ?_, ?_⟩
  · intro ξ hξ η hη hne
    have hd : 0 < (C.dl ξ η).toReal := C.dl_toReal_pos (hLU hξ) (hLU hη) hne.symm
    have hdle : (C.dl ξ η).toReal ≤ max 1 D₀ := (hD ξ hξ η hη).trans (le_max_right _ _)
    have h1 := hsz ξ hξ η hη hne
    have hsplit : (C.dl ξ η).toReal ^ (((e + 1 : ℕ) : ℤ) - (C.G.homogeneousDimension : ℤ)) =
        (C.dl ξ η).toReal ^ e *
          (C.dl ξ η).toReal ^ (((1 : ℕ) : ℤ) - (C.G.homogeneousDimension : ℤ)) := by
      rw [← zpow_natCast, ← zpow_add₀ hd.ne']
      congr 1
      push_cast
      ring
    have hz : 0 ≤ (C.dl ξ η).toReal ^ (((1 : ℕ) : ℤ) - (C.G.homogeneousDimension : ℤ)) :=
      zpow_nonneg hd.le _
    calc |κ ξ η|
        ≤ A * (C.dl ξ η).toReal ^ (((e + 1 : ℕ) : ℤ) - (C.G.homogeneousDimension : ℤ)) := h1
      _ = A * ((C.dl ξ η).toReal ^ e *
            (C.dl ξ η).toReal ^ (((1 : ℕ) : ℤ) - (C.G.homogeneousDimension : ℤ))) := by
          rw [hsplit]
      _ ≤ A * (max 1 D₀ ^ e *
            (C.dl ξ η).toReal ^ (((1 : ℕ) : ℤ) - (C.G.homogeneousDimension : ℤ))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
            (pow_le_pow_left₀ hd.le hdle e) hz) hA
      _ = A * max 1 D₀ ^ e *
            (C.dl ξ η).toReal ^ (((1 : ℕ) : ℤ) - (C.G.homogeneousDimension : ℤ)) := by ring
  · intro ξ hξ ξ' hξ' η hη hsep
    have hh0 : 0 ≤ (C.dl ξ ξ').toReal := ENNReal.toReal_nonneg
    have hr : 0 < (C.dl ξ' η).toReal := by linarith
    have hrle : (C.dl ξ' η).toReal ≤ max 1 D₀ := (hD ξ' hξ' η hη).trans (le_max_right _ _)
    have h1 := hdf ξ hξ ξ' hξ' η hη hsep
    set r : ℝ := (C.dl ξ' η).toReal with hrdef
    set h : ℝ := (C.dl ξ ξ').toReal with hhdef
    set P : ℝ := r ^ ((C.G.homogeneousDimension : ℤ) + 1 - ((e + 1 : ℕ) : ℤ)) with hP
    have hPpos : 0 < P := zpow_pos hr _
    have hRe : r ^ ((C.G.homogeneousDimension : ℤ) + 1 - ((1 : ℕ) : ℤ)) = P * r ^ e := by
      rw [hP, ← zpow_natCast r e, ← zpow_add₀ hr.ne']
      congr 1
      push_cast
      ring
    rw [hRe]
    have hre : 0 < r ^ e := pow_pos hr e
    calc |κ ξ' η - κ ξ η| + |κ η ξ' - κ η ξ| ≤ S * h / P := h1
      _ = S * h * r ^ e / (P * r ^ e) := (mul_div_mul_right _ _ hre.ne').symm
      _ ≤ S * h * max 1 D₀ ^ e / (P * r ^ e) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr.le hrle e) (by positivity)
      _ = S * max 1 D₀ ^ e * h / (P * r ^ e) := by ring

/-- **Bounded regular kernels** (BB p. 544, Prop 11.10: "regular components have bounds
from their sup norms and support volumes"): a kernel bounded by `M₀` and `d̃`-Lipschitz with
constant `M` in each variable on a compact patch has the kernel bounds of exponent `ℓ = 1` (the size
bound `d̃^(1-Q) ≥ D₁^(1-Q)` and the difference bound `d̃(ξ', η)^(-Q) ≥ D₁^(-Q)` hold on the bounded
patch). -/
theorem hasKernelBounds_one_of_bounded_lipschitz {L : Set (Fin (n + m) → ℝ)}
    (hL : IsCompact L) (hLU : L ⊆ C.U) {r : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ}
    {M₀ M : ℝ} (hM₀ : 0 ≤ M₀) (hM : 0 ≤ M)
    (hbd : ∀ ξ ∈ L, ∀ η ∈ L, |r ξ η| ≤ M₀)
    (hl₁ : ∀ ξ ∈ L, ∀ ξ' ∈ L, ∀ η ∈ L, |r ξ' η - r ξ η| ≤ M * (C.dl ξ ξ').toReal)
    (hl₂ : ∀ ξ ∈ L, ∀ ξ' ∈ L, ∀ η ∈ L, |r η ξ' - r η ξ| ≤ M * (C.dl ξ ξ').toReal) :
    C.HasKernelBounds L 1 r := by
  obtain ⟨D₀, hD₀, hD⟩ := C.exists_dl_bound hL hLU
  have hQ : 1 ≤ C.G.homogeneousDimension := G2.homogeneousDimension_pos C.G
  have hD₁1 : 1 ≤ max 1 D₀ := le_max_left _ _
  have hD₁0 : 0 ≤ max 1 D₀ := zero_le_one.trans hD₁1
  refine ⟨M₀ * max 1 D₀ ^ (C.G.homogeneousDimension - 1),
    2 * M * max 1 D₀ ^ C.G.homogeneousDimension, by positivity, by positivity, ?_, ?_⟩
  · intro ξ hξ η hη hne
    have hd : 0 < (C.dl ξ η).toReal := C.dl_toReal_pos (hLU hξ) (hLU hη) hne.symm
    have hdle : (C.dl ξ η).toReal ≤ max 1 D₀ := (hD ξ hξ η hη).trans (le_max_right _ _)
    have e : ((1 : ℕ) : ℤ) - (C.G.homogeneousDimension : ℤ) =
        -((C.G.homogeneousDimension - 1 : ℕ) : ℤ) := by
      rw [Nat.cast_sub hQ]
      push_cast
      ring
    rw [e, zpow_neg, zpow_natCast, ← div_eq_mul_inv, le_div_iff₀ (pow_pos hd _)]
    exact mul_le_mul (hbd ξ hξ η hη) (pow_le_pow_left₀ hd.le hdle _) (by positivity) hM₀
  · intro ξ hξ ξ' hξ' η hη hsep
    have hh0 : 0 ≤ (C.dl ξ ξ').toReal := ENNReal.toReal_nonneg
    have hr : 0 < (C.dl ξ' η).toReal := by linarith
    have hrle : (C.dl ξ' η).toReal ≤ max 1 D₀ := (hD ξ' hξ' η hη).trans (le_max_right _ _)
    have hsum : |r ξ' η - r ξ η| + |r η ξ' - r η ξ| ≤ 2 * M * (C.dl ξ ξ').toReal := by
      have := hl₁ ξ hξ ξ' hξ' η hη
      have := hl₂ ξ hξ ξ' hξ' η hη
      linarith
    rw [Nat.cast_one, add_sub_cancel_right, zpow_natCast, le_div_iff₀ (pow_pos hr _)]
    calc (|r ξ' η - r ξ η| + |r η ξ' - r η ξ|) * (C.dl ξ' η).toReal ^ C.G.homogeneousDimension
        ≤ (2 * M * (C.dl ξ ξ').toReal) * max 1 D₀ ^ C.G.homogeneousDimension :=
          mul_le_mul hsum (pow_le_pow_left₀ hr.le hrle _) (by positivity) (by positivity)
      _ = 2 * M * max 1 D₀ ^ C.G.homogeneousDimension * (C.dl ξ ξ').toReal := by ring

/-- **The kernel bounds of exponent one are the abstract slice bounds**: on a compact
patch `S ⊆ U`, a kernel with `HasKernelBounds S 1` and measurable cut to `S × S` satisfies the
`SliceBounds` hypotheses of the restricted-error estimates (size `A / d̃^(Q-1)` and first-variable difference
`B d̃(ξ, ξ') / d̃(ξ', η)^Q` for `d̃(ξ', η) > 2 d̃(ξ, ξ')`), with `q + 1 = Q`. -/
theorem exists_sliceBounds_of_hasKernelBounds {S : Set (Fin (n + m) → ℝ)} (hSU : S ⊆ C.U)
    {κ : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ} (h : C.HasKernelBounds S 1 κ)
    (hmeas : Measurable (Function.uncurry (sliceKernel S κ))) :
    ∃ A B : ℝ, SliceBounds S (fun x y => (C.dl x y).toReal) (C.G.homogeneousDimension - 1)
      (sliceKernel S κ) A B := by
  obtain ⟨A, B, hA, hB, hsz, hdf⟩ := h
  have hQ : 1 ≤ C.G.homogeneousDimension := G2.homogeneousDimension_pos C.G
  refine ⟨A, B, hA, hB, hmeas, fun x y hx => sliceKernel_of_not_mem (Or.inl hx),
    fun x y hy => sliceKernel_of_not_mem (Or.inr (Or.inl hy)), ?_, ?_⟩
  · intro x hx y hy
    show |sliceKernel S κ x y| ≤ A / (C.dl x y).toReal ^ (C.G.homogeneousDimension - 1)
    by_cases hxy : x = y
    · rw [sliceKernel_of_not_mem (Or.inr (Or.inr hxy))]
      simp only [abs_zero]
      exact div_nonneg hA (pow_nonneg ENNReal.toReal_nonneg _)
    · rw [sliceKernel_of_mem hx hy hxy]
      have := hsz x hx y hy hxy
      have e : ((1 : ℕ) : ℤ) - (C.G.homogeneousDimension : ℤ) =
          -((C.G.homogeneousDimension - 1 : ℕ) : ℤ) := by
        rw [Nat.cast_sub hQ]
        push_cast
        ring
      rwa [e, zpow_neg, zpow_natCast, ← div_eq_mul_inv] at this
  · intro x hx x' hx' y hy hsep
    have hsep' : 2 * (C.dl x x').toReal < (C.dl x' y).toReal := hsep
    have hh0 : 0 ≤ (C.dl x x').toReal := ENNReal.toReal_nonneg
    have hne1 : x' ≠ y := by
      intro h
      rw [← h] at hsep'
      have : (C.dl x' x').toReal = 0 := by
        rw [(C.dl_eq_zero_iff (hSU hx') (hSU hx')).mpr rfl]
        rfl
      linarith
    have hne2 : x ≠ y := by
      intro h
      rw [← h] at hsep'
      have : (C.dl x' x).toReal = (C.dl x x').toReal := congrArg ENNReal.toReal (C.dl_symm x' x)
      linarith
    show |sliceKernel S κ x' y - sliceKernel S κ x y| ≤
      B * (C.dl x x').toReal / (C.dl x' y).toReal ^ (C.G.homogeneousDimension - 1 + 1)
    rw [sliceKernel_of_mem hx' hy hne1, sliceKernel_of_mem hx hy hne2, Nat.sub_add_cancel hQ]
    have := hdf x hx x' hx' y hy hsep'
    rw [Nat.cast_one, add_sub_cancel_right, zpow_natCast] at this
    exact le_trans (le_add_of_nonneg_right (abs_nonneg _)) this

end LiftedChart
end RothschildStein.P1
