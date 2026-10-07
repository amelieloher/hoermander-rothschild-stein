-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.BaseHolderNoDriftBounds
public import RothschildStein.P2.BaseHolderNoDriftCutoff

/-!
# No drift: the cutoff step

Part of the base Hölder estimate (BB p. 601 (11.92)), alphabet `Fin q`, all weights one. Let
`t, g > 0`, `t₁ = t + g`, `t₂ = t + 2 g`, `s = t + 3 g`, let `ζ = φ(t, t₁)` and `ζ' = φ(t₁, t₂)` be the
radial cutoffs (`ζ = 1` on `U_t^ρ`, `tsupport ζ ⊆ U_{t₁}^ρ`, `ζ' = 1` on `U_{t₁}^ρ`, `tsupport ζ' ⊆ U_{t₂}^ρ`) and
`u` of finite Hölder norm with Hölder weak jet `D` on the patch. Write `Y` for a common bound of
`‖L̃u‖_{C^α(U_s^ρ)}` and `‖u‖_{∞, U_s^ρ}` and assume `∑ₗ ‖X̃ₗ u‖_{C^α(U_{t₂}^ρ)} ≤ c_n Y` (the nested Hölder
interpolation inequality). With `L̃(ζ u) = ζ L̃u + 2 ∑ᵢ X̃ᵢζ X̃ᵢu + u L̃ζ`:

* `‖ζ L̃u‖_{C^α} ≤ B₀ g⁻¹ Y` and `‖X̃ᵢζ X̃ᵢu‖_{C^α}` summed `≤ B₁ g⁻² c_n Y` (zero-extension product estimate);
* `u L̃ζ = (ζ' u) L̃ζ`, `‖ζ' u‖_{C^α} ≤ C₃ (‖L̃(ζ' u)‖_∞ + ‖ζ' u‖_∞)` (`HolderFromSupNoDrift`, so that no
  drift/flow-time absorption is needed) and `‖L̃(ζ' u)‖_∞ ≤ (1 + 2 b₁ g⁻¹ c_n + b₂ g⁻²) Y`.

The compact Hölder estimate applied to `ζ u` gives
`‖u‖_{C^{2,α}(U_t^ρ)} ≤ K(g) Y` (`cutoff_step_noDrift`) with `K(g)` an explicit polynomial in `g⁻¹` and `c_n`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped ENNReal Topology BigOperators
namespace RothschildStein.P2

open RothschildStein.P1

variable {n q st m : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart noDriftWeight st Ω hΩ X x₀ m} {F : KernelFrame (n + m)}

/-- **The cutoff step, no drift.** See the module docstring. -/
theorem cutoff_step_noDrift (hF : C.IsLiftedFrame F) {ν : G2.HomogeneousNorm C.G}
    {ξ₀ : Fin (n + m) → ℝ} (hξ₀ : ξ₀ ∈ C.U) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {a : TestFunction F.V ℝ (⊤ : ℕ∞)} {Λ C₃ : ℝ} (hΛ0 : 0 ≤ Λ)
    (hΛ : CompactHolderEstimateNoDrift C F a α Λ) (hC₃ : 0 ≤ C₃)
    (hS : HolderFromSupNoDrift C F a α C₃) {rstar b₁ b₂ B₀ B₁ B₂ : ℝ} (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂)
    (hB₀ : 0 ≤ B₀) (hB₁ : 0 ≤ B₁) (hB₂ : 0 ≤ B₂)
    (hcut : CutoffDataNoDrift C ν ξ₀ α rstar b₁ b₂ B₀ B₁ B₂) {t g : ℝ} (ht : 0 < t) (hg : 0 < g)
    (hts : t + 3 * g < rstar) (hBV : rhoBall C ν ξ₀ (t + 3 * g) ⊆ (F.V : Set (Fin (n + m) → ℝ)))
    (ha1 : ∀ x ∈ rhoBall C ν ξ₀ (t + 3 * g), a x = 1) {u : (Fin (n + m) → ℝ) → ℝ}
    {D : List (Fin q) → (Fin (n + m) → ℝ) → ℝ}
    (hu : holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) u ≠ ⊤)
    (hD : LiftedChart.IsHolderWeakJet noDriftWeight C.Xl C.dl F.V 2 α u D) {cn : ℝ} (hcn : 0 ≤ cn)
    {Y : ℝ≥0∞}
    (hY1 : holderENorm C.dl α (rhoBall C ν ξ₀ (t + 3 * g)) (weakSumSquares D []) ≤ Y)
    (hY2 : supNormE (rhoBall C ν ξ₀ (t + 3 * g)) u ≤ Y)
    (hΨ : ∑ l : Fin q, holderENorm C.dl α (rhoBall C ν ξ₀ (t + 2 * g)) (D [l]) ≤
      ENNReal.ofReal cn * Y) :
    jetENormNoDrift C.dl α (rhoBall C ν ξ₀ t) D ≤
      ENNReal.ofReal (Λ * (B₀ * g⁻¹ + 2 * (B₁ * (g ^ 2)⁻¹) * cn +
        C₃ * (2 + 2 * (b₁ * g⁻¹) * cn + b₂ * (g ^ 2)⁻¹) * (B₂ * (g ^ 3)⁻¹) + 1)) * Y := by
  classical
  have hw : ∀ j : Fin q, ((noDriftWeight j : ℕ+) : ℕ) = 1 := noDriftWeight_natCast_eq_one
  -- radii
  have ht₁ : t < t + g := by linarith
  have ht₂ : t + g < t + 2 * g := by linarith
  have ht₃ : t + 2 * g < t + 3 * g := by linarith
  have e1 : t + g - t = g := by ring
  have e2 : t + 2 * g - (t + g) = g := by ring
  have hr1 : t + g < rstar := by linarith
  have hr2 : t + 2 * g < rstar := by linarith
  have ht1pos : 0 < t + g := by linarith
  set Bt := rhoBall C ν ξ₀ t with hBt
  set B1 := rhoBall C ν ξ₀ (t + g) with hB1
  set B2 := rhoBall C ν ξ₀ (t + 2 * g) with hB2
  set Bs := rhoBall C ν ξ₀ (t + 3 * g) with hBs
  have hBtB1 : Bt ⊆ B1 := rhoBall_mono C ν ξ₀ ht₁.le
  have hB1B2 : B1 ⊆ B2 := rhoBall_mono C ν ξ₀ ht₂.le
  have hB2Bs : B2 ⊆ Bs := rhoBall_mono C ν ξ₀ ht₃.le
  have hB1V : B1 ⊆ (F.V : Set (Fin (n + m) → ℝ)) := (hB1B2.trans hB2Bs).trans hBV
  have hB2V : B2 ⊆ (F.V : Set (Fin (n + m) → ℝ)) := hB2Bs.trans hBV
  have hBtV : Bt ⊆ (F.V : Set (Fin (n + m) → ℝ)) := hBtB1.trans hB1V
  have hB1open : IsOpen B1 := isOpen_rhoBall C ν hξ₀ _
  have hBtopen : IsOpen Bt := isOpen_rhoBall C ν hξ₀ _
  have hFO : (F.V : Set (Fin (n + m) → ℝ)) ⊆ C.O := hF.subset_U.trans
    (fun x hx => (C.closure_U_subset (subset_closure hx)))
  have hB1O : B1 ⊆ C.O := hB1V.trans hFO
  -- the cutoffs
  set ζ := radialCutoff C ν ξ₀ t (t + g) with hζdef
  set ζ' := radialCutoff C ν ξ₀ (t + g) (t + 2 * g) with hζ'def
  have hζs : ContDiff ℝ (⊤ : ℕ∞) ζ := hcut.smooth t (t + g) ht ht₁ hr1
  have hζc : HasCompactSupport ζ := hcut.compact t (t + g) ht ht₁ hr1
  have hζr := hcut.range t (t + g) ht ht₁ hr1
  have hζ1 : EqOn ζ (fun _ => 1) Bt := hcut.eq_one t (t + g) ht ht₁ hr1
  have hζsupp : tsupport ζ ⊆ B1 := hcut.support t (t + g) ht ht₁ hr1
  have hζ's : ContDiff ℝ (⊤ : ℕ∞) ζ' := hcut.smooth (t + g) (t + 2 * g) ht1pos ht₂ hr2
  have hζ'c : HasCompactSupport ζ' := hcut.compact (t + g) (t + 2 * g) ht1pos ht₂ hr2
  have hζ'r := hcut.range (t + g) (t + 2 * g) ht1pos ht₂ hr2
  have hζ'1 : EqOn ζ' (fun _ => 1) B1 := hcut.eq_one (t + g) (t + 2 * g) ht1pos ht₂ hr2
  have hζ'supp : tsupport ζ' ⊆ B2 := hcut.support (t + g) (t + 2 * g) ht1pos ht₂ hr2
  have hd1 : ∀ i x, |fieldDerivative (C.Xl i) ζ x| ≤ b₁ * g⁻¹ := fun i x => by
    have := hcut.deriv1 t (t + g) ht ht₁ hr1 i x
    rwa [e1] at this
  have hd2 : ∀ x, |sumSquares C.Xl ζ x| ≤ b₂ * (g ^ 2)⁻¹ := fun x => by
    have := hcut.deriv2 t (t + g) ht ht₁ hr1 x
    rwa [e1] at this
  have hd1' : ∀ i x, |fieldDerivative (C.Xl i) ζ' x| ≤ b₁ * g⁻¹ := fun i x => by
    have := hcut.deriv1 (t + g) (t + 2 * g) ht1pos ht₂ hr2 i x
    rwa [e2] at this
  have hd2' : ∀ x, |sumSquares C.Xl ζ' x| ≤ b₂ * (g ^ 2)⁻¹ := fun x => by
    have := hcut.deriv2 (t + g) (t + 2 * g) ht1pos ht₂ hr2 x
    rwa [e2] at this
  have hH0 : holderENorm C.dl α C.O ζ ≤ ENNReal.ofReal (B₀ * g⁻¹) := by
    have := hcut.holder0 t (t + g) ht ht₁ hr1
    rwa [e1] at this
  have hH1 : ∀ i, holderENorm C.dl α C.O (fieldDerivative (C.Xl i) ζ) ≤
      ENNReal.ofReal (B₁ * (g ^ 2)⁻¹) := fun i => by
    have := hcut.holder1 t (t + g) ht ht₁ hr1 i
    rwa [e1] at this
  have hH2 : holderENorm C.dl α C.O (sumSquares C.Xl ζ) ≤ ENNReal.ofReal (B₂ * (g ^ 3)⁻¹) := by
    have := hcut.holder2 t (t + g) ht ht₁ hr1
    rwa [e1] at this
  -- finiteness of the data
  have hLD : holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) (weakSumSquares D []) ≠ ⊤ :=
    hD.weakSumSquares_nil_ne_top hw hα0
  have hDfin : ∀ i : Fin q, holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) (D [i]) ≠ ⊤ :=
    fun i => (hD [i] (LiftedChart.horizontal_mem_wordFamily_noDrift hw i)).2
  have hDnil := hD [] (S.nil_mem_wordFamily _ _)
  have huc : ContinuousOn u (F.V : Set (Fin (n + m) → ℝ)) :=
    LiftedChart.continuousOn_of_holderENorm_lt_top hF.subset_U hα0 (lt_top_iff_ne_top.2 hu)
  have hnil : EqOn (D []) u (F.V : Set (Fin (n + m) → ℝ)) :=
    holderWeakJet_nil_eqOn_noDrift (C := C) (V := F.V) hF.subset_U hα0 huc hDnil.1
      (lt_top_iff_ne_top.2 hDnil.2)
  have hsepV : ∀ x ∈ (F.V : Set (Fin (n + m) → ℝ)), ∀ y ∈ (F.V : Set (Fin (n + m) → ℝ)),
      C.dl x y = 0 → x = y := fun x hx y hy hd =>
    ((C.dl_eq_zero_iff (hF.subset_U hx) (hF.subset_U hy)).1 hd).symm
  have hDV : ∀ I ∈ wordFamily noDriftWeight 2, hasWeakWordDeriv C.Xl F.V I u (D I) ∧
      holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) (D I) ≠ ⊤ := hD
  -- the localized products
  have hvC := memHolderXCompact_prod_ext_noDrift hF (P := F.V) subset_rfl hα0 hα1.le hζs hζc
    (hζsupp.trans hB1V) hu hDV
  have hjetv := isHolderWeakJet_prodJet_ext_noDrift hF (P := F.V) subset_rfl hα0 hα1.le hζs hζc
    (hζsupp.trans hB1V) hu hDV
  have hv'C := memHolderXCompact_prod_ext_noDrift hF (P := F.V) subset_rfl hα0 hα1.le hζ's hζ'c
    (hζ'supp.trans hB2V) hu hDV
  have hjetv' := isHolderWeakJet_prodJet_ext_noDrift hF (P := F.V) subset_rfl hα0 hα1.le hζ's hζ'c
    (hζ'supp.trans hB2V) hu hDV
  have hav : ∀ x, a x * (fun x => u x * ζ x) x = (fun x => u x * ζ x) x := fun x => by
    by_cases hx : x ∈ tsupport ζ
    · simp only [ha1 x (hB2Bs (hB1B2 (hζsupp hx))), one_mul]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  have hav' : ∀ x, a x * (fun x => u x * ζ' x) x = (fun x => u x * ζ' x) x := fun x => by
    by_cases hx : x ∈ tsupport ζ'
    · simp only [ha1 x (hB2Bs (hζ'supp hx)), one_mul]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  -- common bounds on the balls
  have hfB : ∀ x ∈ B2, ENNReal.ofReal |weakSumSquares D [] x| ≤ Y := fun x hx =>
    (S.enorm_le_holderENorm C.dl α Bs (weakSumSquares D []) (hB2Bs hx)).trans hY1
  have huB : ∀ x ∈ B2, ENNReal.ofReal |u x| ≤ Y := fun x hx =>
    (ofReal_abs_le_supNormE (hB2Bs hx)).trans hY2
  have hΨB : ∀ x ∈ B2, ∑ i : Fin q, ENNReal.ofReal |D [i] x| ≤ ENNReal.ofReal cn * Y := fun x hx =>
    (Finset.sum_le_sum fun i _ => S.enorm_le_holderENorm C.dl α B2 (D [i]) hx).trans hΨ
  -- (A) the Hölder norm of `ζ' u`
  have hsupL' : supNormE (F.V : Set (Fin (n + m) → ℝ))
      (weakSumSquares (prodJetNoDrift C.Xl ζ' u D) []) ≤
      Y + ENNReal.ofReal (2 * (b₁ * g⁻¹)) * (ENNReal.ofReal cn * Y) +
        ENNReal.ofReal (b₂ * (g ^ 2)⁻¹) * Y :=
    supNormE_weakSumSquares_prod_le C.Xl hζ'supp (fun x => (hζ'r x).1) (fun x => (hζ'r x).2)
      (by positivity) hd1' hd2' hfB huB hΨB
  have hsupv' : supNormE (F.V : Set (Fin (n + m) → ℝ)) (fun x => u x * ζ' x) ≤ Y := by
    refine supNormE_le_of_forall fun x _ => ?_
    by_cases hx : x ∈ tsupport ζ'
    · obtain ⟨hz0, hz1⟩ := hζ'r x
      calc ENNReal.ofReal |u x * ζ' x| = ENNReal.ofReal |u x| * ENNReal.ofReal |ζ' x| := by
            rw [abs_mul, ENNReal.ofReal_mul (abs_nonneg _)]
        _ ≤ Y * 1 := mul_le_mul' (huB x (hζ'supp hx)) (by
            rw [abs_of_nonneg hz0]
            exact ENNReal.ofReal_le_one.2 hz1)
        _ = Y := mul_one _
    · simp [image_eq_zero_of_notMem_tsupport hx]
  have hv'Hold : holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) (fun x => u x * ζ' x) ≤
      ENNReal.ofReal (C₃ * (2 + 2 * (b₁ * g⁻¹) * cn + b₂ * (g ^ 2)⁻¹)) * Y := by
    have h1 := hS _ _ hv'C hjetv' hav'
    refine h1.trans ?_
    have hk : 0 ≤ 2 * (b₁ * g⁻¹) := by positivity
    have hβ₂ : 0 ≤ b₂ * (g ^ 2)⁻¹ := by positivity
    have hb1 : BoundedBy (supNormE (F.V : Set (Fin (n + m) → ℝ))
        (weakSumSquares (prodJetNoDrift C.Xl ζ' u D) [])) Y
        (1 + 2 * (b₁ * g⁻¹) * cn + b₂ * (g ^ 2)⁻¹) :=
      (((BoundedBy.of_le (le_refl Y)).add
        ((BoundedBy.of_const_mul_le hcn (le_refl Y)).const_mul hk) zero_le_one
        (mul_nonneg hk hcn)).add (BoundedBy.of_const_mul_le hβ₂ (le_refl Y))
        (add_nonneg zero_le_one (mul_nonneg hk hcn)) hβ₂).mono_left hsupL'
    have hb2 : BoundedBy (supNormE (F.V : Set (Fin (n + m) → ℝ)) (fun x => u x * ζ' x)) Y 1 :=
      BoundedBy.of_le hsupv'
    have hb3 := (hb1.add hb2 (by positivity) zero_le_one).const_mul hC₃
    unfold BoundedBy at hb3
    have e : C₃ * (1 + 2 * (b₁ * g⁻¹) * cn + b₂ * (g ^ 2)⁻¹ + 1) =
        C₃ * (2 + 2 * (b₁ * g⁻¹) * cn + b₂ * (g ^ 2)⁻¹) := by ring
    rw [e] at hb3
    exact hb3
  -- (B) `u L̃ζ = (ζ' u) L̃ζ`
  have hfun3 : (fun x => u x * sumSquares C.Xl ζ x) =
      fun x => (u x * ζ' x) * sumSquares C.Xl ζ x := by
    funext x
    by_cases hx : x ∈ tsupport ζ
    · rw [hζ'1 (hζsupp hx), mul_one]
    · have : sumSquares C.Xl ζ x = 0 := Finset.sum_eq_zero fun i _ =>
        fieldDerivative_fieldDerivative_eq_zero_of_notMem_tsupport hx
      simp [this]
  have hH2F : holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) (sumSquares C.Xl ζ) ≤
      ENNReal.ofReal (B₂ * (g ^ 3)⁻¹) := (S.holderENorm_mono C.dl α _ _ hFO).trans hH2
  have hK3 : 0 ≤ C₃ * (2 + 2 * (b₁ * g⁻¹) * cn + b₂ * (g ^ 2)⁻¹) := by positivity
  have hA3 : BoundedBy (holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ))
      (fun x => u x * sumSquares C.Xl ζ x)) Y
      (C₃ * (2 + 2 * (b₁ * g⁻¹) * cn + b₂ * (g ^ 2)⁻¹) * (B₂ * (g ^ 3)⁻¹)) := by
    unfold BoundedBy
    rw [hfun3]
    refine (S.holderENorm_mul_le C.dl hα0 _ hsepV _ _ hv'C.1.1
      (lt_of_le_of_lt hH2F ENNReal.ofReal_lt_top)).trans ?_
    calc _ ≤ (ENNReal.ofReal (C₃ * (2 + 2 * (b₁ * g⁻¹) * cn + b₂ * (g ^ 2)⁻¹)) * Y) *
          ENNReal.ofReal (B₂ * (g ^ 3)⁻¹) := mul_le_mul' hv'Hold hH2F
      _ = _ := by
          rw [ENNReal.ofReal_mul hK3]
          ring
  -- (C) the cutoff summand `L̃u ζ`
  set P1 : Opens (Fin (n + m) → ℝ) := ⟨B1, hB1open⟩ with hP1
  have hP1c : (P1 : Set (Fin (n + m) → ℝ)) = B1 := rfl
  have hζK : ∀ z, z ∉ tsupport ζ → ζ z = 0 := fun z hz => image_eq_zero_of_notMem_tsupport hz
  have hζB1 : holderENorm C.dl α B1 ζ ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.ofReal_ne_top) ((S.holderENorm_mono C.dl α _ _ hB1O).trans hH0)
  have hA1 : BoundedBy (holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ))
      (fun x => weakSumSquares D [] x * ζ x)) Y (B₀ * g⁻¹) := by
    unfold BoundedBy
    have hfB1 : holderENorm C.dl α B1 (weakSumSquares D []) ≠ ⊤ :=
      ne_top_of_le_ne_top hLD (S.holderENorm_mono C.dl α _ _ hB1V)
    refine (holderENorm_cutoff_mul_le_noDrift hF (P := P1) hB1V hα0 hζc hζsupp hζK hfB1 hζB1).trans ?_
    calc _ ≤ Y * ENNReal.ofReal (B₀ * g⁻¹) := mul_le_mul'
          (((S.holderENorm_mono C.dl α _ _ (hB1B2.trans hB2Bs)).trans hY1))
          (((S.holderENorm_mono C.dl α _ _ hB1O).trans hH0))
      _ = _ := mul_comm _ _
  -- (D) the cutoff summand `2 ∑ᵢ X̃ᵢζ X̃ᵢu`
  have hA2i : ∀ i : Fin q, holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ))
      (fun x => D [i] x * fieldDerivative (C.Xl i) ζ x) ≤
        holderENorm C.dl α B2 (D [i]) * ENNReal.ofReal (B₁ * (g ^ 2)⁻¹) := by
    intro i
    have hfi : holderENorm C.dl α B1 (D [i]) ≠ ⊤ :=
      ne_top_of_le_ne_top (hDfin i) (S.holderENorm_mono C.dl α _ _ hB1V)
    have hH1' : holderENorm C.dl α B1 (fieldDerivative (C.Xl i) ζ) ≤
        ENNReal.ofReal (B₁ * (g ^ 2)⁻¹) := (S.holderENorm_mono C.dl α _ _ hB1O).trans (hH1 i)
    refine (holderENorm_cutoff_mul_le_noDrift hF (P := P1) hB1V hα0 hζc hζsupp
      (fun z hz => fieldDerivative_eq_zero_of_notMem_tsupport hz) hfi
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hH1')).trans ?_
    exact mul_le_mul' (S.holderENorm_mono C.dl α _ _ hB1B2) hH1'
  have hA2 : BoundedBy (holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ))
      (fun x => 2 * ∑ i : Fin q, D [i] x * fieldDerivative (C.Xl i) ζ x)) Y
      (2 * (B₁ * (g ^ 2)⁻¹) * cn) := by
    unfold BoundedBy
    refine (holderENorm_two_mul_sum_le hα0.le _ _).trans ?_
    have hB1' : 0 ≤ B₁ * (g ^ 2)⁻¹ := by positivity
    calc 2 * ∑ i : Fin q, holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ))
          (fun x => D [i] x * fieldDerivative (C.Xl i) ζ x)
        ≤ 2 * ∑ i : Fin q, holderENorm C.dl α B2 (D [i]) * ENNReal.ofReal (B₁ * (g ^ 2)⁻¹) :=
          mul_le_mul' le_rfl (Finset.sum_le_sum fun i _ => hA2i i)
      _ = 2 * ((∑ i : Fin q, holderENorm C.dl α B2 (D [i])) * ENNReal.ofReal (B₁ * (g ^ 2)⁻¹)) := by
          rw [Finset.sum_mul]
      _ ≤ 2 * ((ENNReal.ofReal cn * Y) * ENNReal.ofReal (B₁ * (g ^ 2)⁻¹)) :=
          mul_le_mul' le_rfl (mul_le_mul' hΨ le_rfl)
      _ = ENNReal.ofReal (2 * (B₁ * (g ^ 2)⁻¹) * cn) * Y := by
          rw [ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 * (B₁ * (g ^ 2)⁻¹) by positivity),
            ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 by norm_num), ENNReal.ofReal_mul hB₁,
            ENNReal.ofReal_ofNat]
          ring
  -- (E) the Hölder norm of `L̃ (ζ u)`
  have hLv : weakSumSquares (prodJetNoDrift C.Xl ζ u D) [] = fun x =>
      (weakSumSquares D [] x * ζ x + 2 * ∑ i : Fin q, D [i] x * fieldDerivative (C.Xl i) ζ x) +
        u x * sumSquares C.Xl ζ x := funext fun x => weakSumSquares_prodJetNoDrift C.Xl ζ u D x
  have hHL : BoundedBy (holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ))
      (weakSumSquares (prodJetNoDrift C.Xl ζ u D) [])) Y
      (B₀ * g⁻¹ + 2 * (B₁ * (g ^ 2)⁻¹) * cn +
        C₃ * (2 + 2 * (b₁ * g⁻¹) * cn + b₂ * (g ^ 2)⁻¹) * (B₂ * (g ^ 3)⁻¹)) := by
    have hp1 : 0 ≤ B₀ * g⁻¹ := by positivity
    have hp2 : 0 ≤ 2 * (B₁ * (g ^ 2)⁻¹) * cn := by positivity
    have hp3 : 0 ≤ C₃ * (2 + 2 * (b₁ * g⁻¹) * cn + b₂ * (g ^ 2)⁻¹) * (B₂ * (g ^ 3)⁻¹) := by positivity
    refine ((hA1.add hA2 hp1 hp2).add hA3 (add_nonneg hp1 hp2) hp3).mono_left ?_
    rw [hLv]
    exact (holderENorm_add_le hα0.le _ _).trans
      (add_le_add (holderENorm_add_le hα0.le _ _) le_rfl)
  -- (F) the sup norm of `ζ u`
  have hsupv : supNormE (F.V : Set (Fin (n + m) → ℝ)) (fun x => u x * ζ x) ≤ Y := by
    refine supNormE_le_of_forall fun x _ => ?_
    by_cases hx : x ∈ tsupport ζ
    · obtain ⟨hz0, hz1⟩ := hζr x
      calc ENNReal.ofReal |u x * ζ x| = ENNReal.ofReal |u x| * ENNReal.ofReal |ζ x| := by
            rw [abs_mul, ENNReal.ofReal_mul (abs_nonneg _)]
        _ ≤ Y * 1 := mul_le_mul' (huB x (hB1B2 (hζsupp hx))) (by
            rw [abs_of_nonneg hz0]
            exact ENNReal.ofReal_le_one.2 hz1)
        _ = Y := mul_one _
    · simp [image_eq_zero_of_notMem_tsupport hx]
  -- (G) the compact estimate for `ζ u`
  have hΛv := hΛ _ _ hvC hjetv hav
  have hjetEq : jetENormNoDrift C.dl α Bt D =
      jetENormNoDrift C.dl α Bt (prodJetNoDrift C.Xl ζ u D) :=
    jetENormNoDrift_congr fun I hI =>
      (prodJetNoDrift_eq_of_eqOn_one (C := C) hBtopen hζ1 (hnil.mono hBtV) hI).symm
  have hp1 : 0 ≤ B₀ * g⁻¹ + 2 * (B₁ * (g ^ 2)⁻¹) * cn +
      C₃ * (2 + 2 * (b₁ * g⁻¹) * cn + b₂ * (g ^ 2)⁻¹) * (B₂ * (g ^ 3)⁻¹) := by positivity
  have hfin := (hHL.add (BoundedBy.of_le hsupv) hp1 zero_le_one)
  unfold BoundedBy at hfin
  calc jetENormNoDrift C.dl α Bt D = jetENormNoDrift C.dl α Bt (prodJetNoDrift C.Xl ζ u D) := hjetEq
    _ ≤ jetENormNoDrift C.dl α (F.V : Set (Fin (n + m) → ℝ)) (prodJetNoDrift C.Xl ζ u D) :=
        jetENormNoDrift_mono_set hBtV _
    _ ≤ _ := hΛv
    _ ≤ ENNReal.ofReal Λ * (ENNReal.ofReal (B₀ * g⁻¹ + 2 * (B₁ * (g ^ 2)⁻¹) * cn +
          C₃ * (2 + 2 * (b₁ * g⁻¹) * cn + b₂ * (g ^ 2)⁻¹) * (B₂ * (g ^ 3)⁻¹) + 1) * Y) :=
        mul_le_mul' le_rfl hfin
    _ = _ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hΛ0]

end RothschildStein.P2
