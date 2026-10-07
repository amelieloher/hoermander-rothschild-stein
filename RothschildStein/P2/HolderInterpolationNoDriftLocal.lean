-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.HolderInterpolationNoDriftLeibniz
public import RothschildStein.P2.HolderInterpolationLocal

/-!
# Nested Hölder interpolation without drift: localization with radial cutoffs

The no-drift counterpart of `HolderInterpolationLocal` (alphabet `Fin q`, all weights one, `L̃ = ∑ᵢ X̃ᵢ²`). For
`0 < t < s ≤ R`, the radial cutoff `ζ = φ(t, s)` of the radial cutoff construction (`ζ = 1` on `U_t^ρ`, supported in `U_s^ρ`,
`|X̃ᵢζ| ≤ b₁ (s - t)⁻¹`, `|L̃ζ| ≤ b₂ (s - t)⁻²`), and the compact derivative interpolation inequality applied to
`v = ζ u`, whose Leibniz jet is `prodJetNoDrift`, give

`ψ(t) ≤ ε (‖L̃u‖_{∞,U_R} + 2 b₁ (s-t)⁻¹ ψ(s) + b₂ (s-t)⁻² ‖u‖_{∞,U_R}) + Cc ε^{-γ} ‖u‖_{∞,U_R}`,

`ψ(ρ) = ∑_l ‖X̃_l u‖_{C^α(U_ρ^ρ)}`. This module proves it from the interpolation inequality taken as a
hypothesis `hder` (the conclusion of `exists_derivativeInterpolation_noDrift_of_representation`). The
`(HD1)`-`(HD2)` package is `LiftedChart.distanceGeometry`, which needs no further hypothesis.
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

/-! ### Sup and Hölder quantities on a `ρ`-ball -/

/-- No drift: `ψ(ρ) = ∑_l ‖D [l]‖_{C^α(U_ρ^ρ)}` (real number). -/
def psiBallNoDrift (C : LiftedChart noDriftWeight st Ω hΩ X x₀ m) (ν : G2.HomogeneousNorm C.G)
    (ξ₀ : Fin (n + m) → ℝ) (α : ℝ) (D : List (Fin q) → (Fin (n + m) → ℝ) → ℝ) (ρ : ℝ) : ℝ :=
  (∑ l : Fin q, holderENorm C.dl α (rhoBall C ν ξ₀ ρ) (D [l])).toReal

/-- No drift chart: the sup norm `‖f‖_{∞, U_ρ^ρ}` (real number; the sup of `|f|` over the ball). -/
def supBallNoDrift (C : LiftedChart noDriftWeight st Ω hΩ X x₀ m) (ν : G2.HomogeneousNorm C.G)
    (ξ₀ : Fin (n + m) → ℝ) (f : (Fin (n + m) → ℝ) → ℝ) (ρ : ℝ) : ℝ :=
  (⨆ x : rhoBall C ν ξ₀ ρ, ENNReal.ofReal |f x|).toReal

theorem supBallNoDrift_ne_top (ν : G2.HomogeneousNorm C.G) {ξ₀ : Fin (n + m) → ℝ}
    {f : (Fin (n + m) → ℝ) → ℝ} {α ρ : ℝ}
    (hf : holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) f ≠ ⊤)
    (hBV : rhoBall C ν ξ₀ ρ ⊆ (F.V : Set (Fin (n + m) → ℝ))) :
    (⨆ x : rhoBall C ν ξ₀ ρ, ENNReal.ofReal |f x|) ≠ ⊤ := by
  refine ne_top_of_le_ne_top hf (iSup_le fun x => ?_)
  exact S.enorm_le_holderENorm C.dl α _ f (hBV x.2)

theorem abs_le_supBallNoDrift (ν : G2.HomogeneousNorm C.G) {ξ₀ : Fin (n + m) → ℝ}
    {f : (Fin (n + m) → ℝ) → ℝ} {α ρ : ℝ}
    (hf : holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) f ≠ ⊤)
    (hBV : rhoBall C ν ξ₀ ρ ⊆ (F.V : Set (Fin (n + m) → ℝ))) {x : Fin (n + m) → ℝ}
    (hx : x ∈ rhoBall C ν ξ₀ ρ) : |f x| ≤ supBallNoDrift C ν ξ₀ f ρ :=
  (ENNReal.ofReal_le_iff_le_toReal (supBallNoDrift_ne_top ν hf hBV)).mp
    (le_iSup (fun y : rhoBall C ν ξ₀ ρ => ENNReal.ofReal |f y|) ⟨x, hx⟩)

theorem supBallNoDrift_nonneg (C : LiftedChart noDriftWeight st Ω hΩ X x₀ m)
    (ν : G2.HomogeneousNorm C.G) (ξ₀ : Fin (n + m) → ℝ) (f : (Fin (n + m) → ℝ) → ℝ) (ρ : ℝ) :
    0 ≤ supBallNoDrift C ν ξ₀ f ρ :=
  ENNReal.toReal_nonneg

/-- The Hölder norm of a jet entry on a smaller ball is finite (no drift chart). -/
theorem holderENorm_ball_ne_top_noDrift (ν : G2.HomogeneousNorm C.G) {ξ₀ : Fin (n + m) → ℝ}
    {f : (Fin (n + m) → ℝ) → ℝ} {α ρ : ℝ}
    (hf : holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) f ≠ ⊤)
    (hBV : rhoBall C ν ξ₀ ρ ⊆ (F.V : Set (Fin (n + m) → ℝ))) :
    holderENorm C.dl α (rhoBall C ν ξ₀ ρ) f ≠ ⊤ :=
  ne_top_of_le_ne_top hf (S.holderENorm_mono C.dl α _ f hBV)

/-! ### The cutoff data -/

/-- No drift: the data of the radial cutoff construction used by the localization, at one centre: a
threshold `r_*`, and constants `b₁, b₂` with `ζ = φ(s, r)` smooth with compact support, `0 ≤ ζ ≤ 1`, `ζ = 1` on
`U_s^ρ`, `tsupport ζ ⊆ U_r^ρ`, `|X̃_{i}ζ| ≤ b₁ (r - s)⁻¹` for the generators and
`|L̃ ζ| ≤ b₂ (r - s)⁻²` (`L̃ = ∑ᵢ X̃ᵢ²`). -/
theorem exists_cutoff_data_noDrift (C : LiftedChart noDriftWeight st Ω hΩ X x₀ m)
    (ν : G2.HomogeneousNorm C.G) (hν : ν.Smooth) {ξ₀ : Fin (n + m) → ℝ} (hξ₀ : ξ₀ ∈ C.U) :
    ∃ rstar b₁ b₂ : ℝ, 0 < rstar ∧ rstar ≤ 1 ∧ 0 ≤ b₁ ∧ 0 ≤ b₂ ∧
      (∀ s r : ℝ, 0 < s → s < r → r < rstar →
        ContDiff ℝ (⊤ : ℕ∞) (radialCutoff C ν ξ₀ s r) ∧
        HasCompactSupport (radialCutoff C ν ξ₀ s r) ∧
        (∀ ξ, 0 ≤ radialCutoff C ν ξ₀ s r ξ ∧ radialCutoff C ν ξ₀ s r ξ ≤ 1) ∧
        EqOn (radialCutoff C ν ξ₀ s r) (fun _ => 1) (rhoBall C ν ξ₀ s) ∧
        tsupport (radialCutoff C ν ξ₀ s r) ⊆ rhoBall C ν ξ₀ r) ∧
      (∀ s r : ℝ, 0 < s → s < r → r < rstar → ∀ (i : Fin q) (ξ : Fin (n + m) → ℝ),
        |fieldDerivative (C.Xl i) (radialCutoff C ν ξ₀ s r) ξ| ≤ b₁ * (r - s)⁻¹) ∧
      (∀ s r : ℝ, 0 < s → s < r → r < rstar → ∀ ξ : Fin (n + m) → ℝ,
        |sumSquares C.Xl (radialCutoff C ν ξ₀ s r) ξ| ≤ b₂ * ((r - s) ^ 2)⁻¹) := by
  obtain ⟨rstar, hr0, hr1, hq, hsup, -⟩ := smooth_cutoffs_noDrift C ν hν
    (isCompact_singleton (x := ξ₀)) (singleton_subset_iff.2 hξ₀)
  choose C1 hC1 hC1b using fun i : Fin q => hsup [i]
  choose C2 hC2 hC2b using fun i : Fin q => hsup [i, i]
  have w1 : ∀ i : Fin q, wordWeight noDriftWeight [i] = 1 := fun i => by
    simp [wordWeight, noDriftWeight]
  have w2 : ∀ i : Fin q, wordWeight noDriftWeight [i, i] = 2 := fun i => by
    simp [wordWeight, noDriftWeight]
  refine ⟨rstar, ∑ i, C1 i, ∑ i, C2 i, hr0, hr1, Finset.sum_nonneg fun i _ => hC1 i,
    Finset.sum_nonneg fun i _ => hC2 i, ?_, ?_, ?_⟩
  · intro s r hs hsr hr
    obtain ⟨h1, h2, h3, h4, h5, h6⟩ := hq ξ₀ (mem_singleton _) s r hs hsr hr
    exact ⟨h1, h2, h3, h4, h5.trans h6⟩
  · intro s r hs hsr hr i ξ
    have h := hC1b i ξ₀ (mem_singleton _) s r hs hsr hr ξ
    rw [w1 i] at h
    have e : (r - s) ^ (-((1 : ℕ) : ℤ)) = (r - s)⁻¹ := by simp
    rw [e] at h
    have hle : C1 i ≤ ∑ j, C1 j :=
      Finset.single_le_sum (f := C1) (fun j _ => hC1 j) (Finset.mem_univ i)
    have hpos : 0 ≤ (r - s)⁻¹ := inv_nonneg.2 (sub_pos.2 hsr).le
    exact (h.trans (mul_le_mul_of_nonneg_right hle hpos))
  · intro s r hs hsr hr ξ
    have e : (r - s) ^ (-((2 : ℕ) : ℤ)) = ((r - s) ^ 2)⁻¹ := by simp [zpow_neg]
    have hi : ∀ i : Fin q, |wordDerivative C.Xl [i, i] (radialCutoff C ν ξ₀ s r) ξ| ≤
        C2 i * ((r - s) ^ 2)⁻¹ := fun i => by
      have h := hC2b i ξ₀ (mem_singleton _) s r hs hsr hr ξ
      rw [w2 i, e] at h
      exact h
    have hL : sumSquares C.Xl (radialCutoff C ν ξ₀ s r) ξ =
        ∑ i : Fin q, wordDerivative C.Xl [i, i] (radialCutoff C ν ξ₀ s r) ξ := rfl
    rw [hL]
    calc |∑ i : Fin q, wordDerivative C.Xl [i, i] (radialCutoff C ν ξ₀ s r) ξ|
        ≤ ∑ i : Fin q, |wordDerivative C.Xl [i, i] (radialCutoff C ν ξ₀ s r) ξ| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin q, C2 i * ((r - s) ^ 2)⁻¹ := Finset.sum_le_sum fun i _ => hi i
      _ = (∑ i, C2 i) * ((r - s) ^ 2)⁻¹ := by rw [Finset.sum_mul]

/-! ### The compact intrinsic class of the localized product -/

/-- No drift: the product `u ζ` of a function of the intrinsic class
`C^{2,α}_{X̃}(V)` with a smooth cutoff compactly supported in the patch lies in the compact intrinsic class
(Leibniz rule in `C^{k,α}_{X̃}`; the Leibniz jet is a Hölder weak jet, and weak Hölder membership is intrinsic membership
under the `(HD)` package of the lifted control distance, `LiftedChart.distanceGeometry`). -/
theorem memHolderXCompact_prod_noDrift (hF : C.IsLiftedFrame F) {α : ℝ} (hα0 : 0 < α)
    (hα1 : α ≤ 1) {ζ u : (Fin (n + m) → ℝ) → ℝ} {D : List (Fin q) → (Fin (n + m) → ℝ) → ℝ}
    (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ) (hζc : HasCompactSupport ζ)
    (hζV : tsupport ζ ⊆ (F.V : Set (Fin (n + m) → ℝ)))
    (hu : holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) u ≠ ⊤)
    (hD : LiftedChart.IsHolderWeakJet noDriftWeight C.Xl C.dl F.V 2 α u D) :
    memHolderXCompact noDriftWeight C.Xl C.dl F.V 2 α (fun x => u x * ζ x) := by
  have hjet := isHolderWeakJet_prodJet_noDrift hF hα0 hα1 hζ hζc hζV hu hD
  have hweak : S.memWeakHolderX noDriftWeight C.Xl C.distanceGeometry.d F.V 2 α
      (fun x => u x * ζ x) :=
    ⟨lt_top_iff_ne_top.2 ((hjet [] (S.nil_mem_wordFamily _ _)).2), fun I hI =>
      ⟨prodJetNoDrift C.Xl ζ u D I, (hjet I hI).1, lt_top_iff_ne_top.2 (hjet I hI).2⟩⟩
  have hmem := S.memHolderX_of_memWeakHolderX C.chartOpens F.V C.distanceGeometry hF.subset_U
    noDriftWeight C.Xl hF.contDiffOn_Xl 2 hα0 hweak
  have hmem' : memHolderX noDriftWeight C.Xl C.dl F.V 2 α (fun x => u x * ζ x) := hmem
  have hsub : closure ((F.V : Set (Fin (n + m) → ℝ)) ∩ Function.support (fun x => u x * ζ x)) ⊆
      tsupport ζ := by
    refine closure_minimal (fun x hx => ?_) (isClosed_tsupport ζ)
    exact subset_tsupport ζ (right_ne_zero_of_mul hx.2)
  exact ⟨hmem', hζc.of_isClosed_subset isClosed_closure hsub, hsub.trans hζV⟩

/-! ### The one-step estimate -/

/-- **The localization step, no drift** (nested form of the Hölder interpolation inequality). Assume
the compact derivative interpolation inequality `hder` (constants `γ₁`, `Cc₁`, cutoff `a`), the cutoff data of
the radial cutoff construction at the centre `ξ₀` (`rstar, b₁, b₂`), `U_R^ρ ⊆ V` with `a = 1` on `U_R^ρ`, and `u` of finite Hölder norm
with the Hölder weak jet `D` on the patch. Then for `0 < t < s ≤ R < r_*` and `0 < ε < 1`

`ψ(t) ≤ ε (‖L̃u‖_{∞,U_R} + 2 b₁ (s-t)⁻¹ ψ(s) + b₂ (s-t)⁻² ‖u‖_{∞,U_R}) + Cc₁ ε^{-γ₁} ‖u‖_{∞,U_R}`. -/
theorem nested_step_noDrift (hF : C.IsLiftedFrame F)
    (ν : G2.HomogeneousNorm C.G) {ξ₀ : Fin (n + m) → ℝ} (hξ₀ : ξ₀ ∈ C.U) {α : ℝ} (hα0 : 0 < α)
    (hα1 : α < 1) {a : TestFunction F.V ℝ (⊤ : ℕ∞)} {γ₁ Cc₁ : ℝ}
    (hder : ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∀ (v : (Fin (n + m) → ℝ) → ℝ) (D : List (Fin q) → (Fin (n + m) → ℝ) → ℝ),
        memHolderXCompact noDriftWeight C.Xl C.dl F.V 2 α v →
        LiftedChart.IsHolderWeakJet noDriftWeight C.Xl C.dl F.V 2 α v D → (∀ x, a x * v x = v x) →
        ∑ l : Fin q, holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) (D [l]) ≤
          ENNReal.ofReal ε * (⨆ x : (F.V : Set (Fin (n + m) → ℝ)),
              ENNReal.ofReal |weakSumSquares D [] x|) +
            ENNReal.ofReal (Cc₁ * ε ^ (-γ₁)) *
              ⨆ x : (F.V : Set (Fin (n + m) → ℝ)), ENNReal.ofReal |v x|)
    (hCc₁ : 0 ≤ Cc₁) {rstar b₁ b₂ : ℝ} (hb₁ : 0 ≤ b₁) (hb₂ : 0 ≤ b₂)
    (hqual : ∀ s r : ℝ, 0 < s → s < r → r < rstar →
        ContDiff ℝ (⊤ : ℕ∞) (radialCutoff C ν ξ₀ s r) ∧
        HasCompactSupport (radialCutoff C ν ξ₀ s r) ∧
        (∀ ξ, 0 ≤ radialCutoff C ν ξ₀ s r ξ ∧ radialCutoff C ν ξ₀ s r ξ ≤ 1) ∧
        EqOn (radialCutoff C ν ξ₀ s r) (fun _ => 1) (rhoBall C ν ξ₀ s) ∧
        tsupport (radialCutoff C ν ξ₀ s r) ⊆ rhoBall C ν ξ₀ r)
    (hζb1 : ∀ s r : ℝ, 0 < s → s < r → r < rstar → ∀ (i : Fin q) (ξ : Fin (n + m) → ℝ),
        |fieldDerivative (C.Xl i) (radialCutoff C ν ξ₀ s r) ξ| ≤ b₁ * (r - s)⁻¹)
    (hζb2 : ∀ s r : ℝ, 0 < s → s < r → r < rstar → ∀ ξ : Fin (n + m) → ℝ,
        |sumSquares C.Xl (radialCutoff C ν ξ₀ s r) ξ| ≤ b₂ * ((r - s) ^ 2)⁻¹)
    {R : ℝ} (hR : R < rstar) (hBV : rhoBall C ν ξ₀ R ⊆ (F.V : Set (Fin (n + m) → ℝ)))
    (ha1 : ∀ x ∈ rhoBall C ν ξ₀ R, a x = 1)
    {u : (Fin (n + m) → ℝ) → ℝ} {D : List (Fin q) → (Fin (n + m) → ℝ) → ℝ}
    (hu : holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) u ≠ ⊤)
    (hD : LiftedChart.IsHolderWeakJet noDriftWeight C.Xl C.dl F.V 2 α u D)
    {t s : ℝ} (ht : 0 < t) (hts : t < s) (hsR : s ≤ R) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    psiBallNoDrift C ν ξ₀ α D t ≤
      ε * (supBallNoDrift C ν ξ₀ (weakSumSquares D []) R +
          2 * b₁ * (s - t)⁻¹ * psiBallNoDrift C ν ξ₀ α D s +
            b₂ * ((s - t) ^ 2)⁻¹ * supBallNoDrift C ν ξ₀ u R) +
        Cc₁ * ε ^ (-γ₁) * supBallNoDrift C ν ξ₀ u R := by
  classical
  have hsr : s < rstar := lt_of_le_of_lt hsR hR
  have hst0 : 0 < s - t := sub_pos.2 hts
  obtain ⟨hζs, hζc, hζr, hζ1, hζsupp⟩ := hqual t s ht hts hsr
  set ζ : (Fin (n + m) → ℝ) → ℝ := radialCutoff C ν ξ₀ t s with hζdef
  have hBsR : rhoBall C ν ξ₀ s ⊆ rhoBall C ν ξ₀ R := rhoBall_mono C ν ξ₀ hsR
  have hBtR : rhoBall C ν ξ₀ t ⊆ rhoBall C ν ξ₀ s := rhoBall_mono C ν ξ₀ hts.le
  have hBsV : rhoBall C ν ξ₀ s ⊆ (F.V : Set (Fin (n + m) → ℝ)) := hBsR.trans hBV
  have hζV : tsupport ζ ⊆ (F.V : Set (Fin (n + m) → ℝ)) := hζsupp.trans hBsV
  have hζB : tsupport ζ ⊆ rhoBall C ν ξ₀ R := hζsupp.trans hBsR
  set v : (Fin (n + m) → ℝ) → ℝ := fun x => u x * ζ x with hvdef
  have hjet := isHolderWeakJet_prodJet_noDrift hF hα0 hα1.le hζs hζc hζV hu hD
  have hvC := memHolderXCompact_prod_noDrift hF hα0 hα1.le hζs hζc hζV hu hD
  have hav : ∀ x, a x * v x = v x := fun x => by
    by_cases hx : x ∈ tsupport ζ
    · rw [ha1 x (hζB hx), one_mul]
    · have h0 : ζ x = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [hvdef, h0]
  have hderiv := hder ε hε0 hε1 v (prodJetNoDrift C.Xl ζ u D) hvC hjet hav
  -- (1) the left side dominates `ψ(t)`
  have hEq : ∀ l : Fin q, EqOn (D [l]) (prodJetNoDrift C.Xl ζ u D [l]) (rhoBall C ν ξ₀ t) := by
    intro l x hx
    have h1 : ζ x = 1 := hζ1 hx
    have h2 : fieldDerivative (C.Xl l) ζ x = 0 :=
      fieldDerivative_eq_zero_of_eqOn_one (isOpen_rhoBall C ν hξ₀ t) hζ1 hx
    simp [prodJetNoDrift, h1, h2]
  have hlhs : ∑ l : Fin q, holderENorm C.dl α (rhoBall C ν ξ₀ t) (D [l]) ≤
      ∑ l : Fin q, holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ))
        (prodJetNoDrift C.Xl ζ u D [l]) := Finset.sum_le_sum fun l _ => by
    calc holderENorm C.dl α (rhoBall C ν ξ₀ t) (D [l]) =
          holderENorm C.dl α (rhoBall C ν ξ₀ t) (prodJetNoDrift C.Xl ζ u D [l]) :=
          S.holderENorm_congr C.dl α _ _ (hEq l)
      _ ≤ _ := S.holderENorm_mono C.dl α _ _ (hBtR.trans hBsV)
  -- (2) the sup norm of `L̃ (u ζ)`
  have hLD : holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) (weakSumSquares D []) ≠ ⊤ :=
    hD.weakSumSquares_nil_ne_top noDriftWeight_natCast_eq_one hα0
  have hDfin : ∀ i : Fin q, holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) (D [i]) ≠ ⊤ :=
    fun i => (hD [i] (LiftedChart.horizontal_mem_wordFamily_noDrift
      noDriftWeight_natCast_eq_one i)).2
  have hDi : ∀ (i : Fin q), ∀ x ∈ rhoBall C ν ξ₀ s,
      |D [i] x| ≤ (holderENorm C.dl α (rhoBall C ν ξ₀ s) (D [i])).toReal :=
    fun i x hx =>
      (ENNReal.ofReal_le_iff_le_toReal (holderENorm_ball_ne_top_noDrift ν (hDfin i) hBsV)).mp
        (S.enorm_le_holderENorm C.dl α _ _ hx)
  have hpsi : psiBallNoDrift C ν ξ₀ α D s =
      ∑ i : Fin q, (holderENorm C.dl α (rhoBall C ν ξ₀ s) (D [i])).toReal :=
    ENNReal.toReal_sum fun i _ => holderENorm_ball_ne_top_noDrift ν (hDfin i) hBsV
  set ML : ℝ := supBallNoDrift C ν ξ₀ (weakSumSquares D []) R with hML
  set Mu : ℝ := supBallNoDrift C ν ξ₀ u R with hMu
  have hML0 : 0 ≤ ML := supBallNoDrift_nonneg C ν ξ₀ _ R
  have hMu0 : 0 ≤ Mu := supBallNoDrift_nonneg C ν ξ₀ _ R
  have hpsi0 : 0 ≤ psiBallNoDrift C ν ξ₀ α D s := ENNReal.toReal_nonneg
  set Bg : ℝ := ML + 2 * b₁ * (s - t)⁻¹ * psiBallNoDrift C ν ξ₀ α D s + b₂ * ((s - t) ^ 2)⁻¹ * Mu
    with hBg
  have hinv0 : 0 ≤ (s - t)⁻¹ := inv_nonneg.2 hst0.le
  have hinv20 : 0 ≤ ((s - t) ^ 2)⁻¹ := by positivity
  have hBg0 : 0 ≤ Bg := by
    rw [hBg]
    have : 0 ≤ 2 * b₁ * (s - t)⁻¹ * psiBallNoDrift C ν ξ₀ α D s :=
      mul_nonneg (mul_nonneg (by positivity) hinv0) hpsi0
    have : 0 ≤ b₂ * ((s - t) ^ 2)⁻¹ * Mu := mul_nonneg (mul_nonneg hb₂ hinv20) hMu0
    linarith
  have hpt : ∀ x ∈ (F.V : Set (Fin (n + m) → ℝ)),
      |weakSumSquares (prodJetNoDrift C.Xl ζ u D) [] x| ≤ Bg := by
    intro x hx
    rw [weakSumSquares_prodJetNoDrift]
    by_cases hxs : x ∈ tsupport ζ
    · have hxB : x ∈ rhoBall C ν ξ₀ s := hζsupp hxs
      have hxR : x ∈ rhoBall C ν ξ₀ R := hBsR hxB
      obtain ⟨hz0, hz1⟩ := hζr x
      have b1 : ∀ i : Fin q, |fieldDerivative (C.Xl i) ζ x| ≤ b₁ * (s - t)⁻¹ := fun i =>
        hζb1 t s ht hts hsr i x
      have b2 : |sumSquares C.Xl ζ x| ≤ b₂ * ((s - t) ^ 2)⁻¹ := hζb2 t s ht hts hsr x
      have hg : |weakSumSquares D [] x| ≤ ML := abs_le_supBallNoDrift ν hLD hBV hxR
      have hu' : |u x| ≤ Mu := abs_le_supBallNoDrift ν hu hBV hxR
      have t1 : |weakSumSquares D [] x * ζ x| ≤ ML := by
        rw [abs_mul, abs_of_nonneg hz0]
        calc |weakSumSquares D [] x| * ζ x ≤ ML * 1 :=
              mul_le_mul hg hz1 hz0 hML0
          _ = ML := mul_one _
      have t2 : |2 * ∑ i : Fin q, D [i] x * fieldDerivative (C.Xl i) ζ x| ≤
          2 * b₁ * (s - t)⁻¹ * psiBallNoDrift C ν ξ₀ α D s := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), hpsi]
        calc 2 * |∑ i : Fin q, D [i] x * fieldDerivative (C.Xl i) ζ x|
            ≤ 2 * ∑ i : Fin q, |D [i] x * fieldDerivative (C.Xl i) ζ x| :=
              mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by norm_num)
          _ ≤ 2 * ∑ i : Fin q, (holderENorm C.dl α (rhoBall C ν ξ₀ s) (D [i])).toReal *
              (b₁ * (s - t)⁻¹) := by
              refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => ?_) (by norm_num)
              rw [abs_mul]
              exact mul_le_mul (hDi i x hxB) (b1 i) (abs_nonneg _) ENNReal.toReal_nonneg
          _ = 2 * b₁ * (s - t)⁻¹ * ∑ i : Fin q,
              (holderENorm C.dl α (rhoBall C ν ξ₀ s) (D [i])).toReal := by
              rw [← Finset.sum_mul]
              ring
      have t3 : |u x * sumSquares C.Xl ζ x| ≤ b₂ * ((s - t) ^ 2)⁻¹ * Mu := by
        rw [abs_mul]
        calc |u x| * |sumSquares C.Xl ζ x| ≤ Mu * (b₂ * ((s - t) ^ 2)⁻¹) :=
              mul_le_mul hu' b2 (abs_nonneg _) hMu0
          _ = _ := by ring
      calc |weakSumSquares D [] x * ζ x +
            2 * ∑ i : Fin q, D [i] x * fieldDerivative (C.Xl i) ζ x +
              u x * sumSquares C.Xl ζ x|
          ≤ |weakSumSquares D [] x * ζ x +
            2 * ∑ i : Fin q, D [i] x * fieldDerivative (C.Xl i) ζ x| +
              |u x * sumSquares C.Xl ζ x| := abs_add_le _ _
        _ ≤ |weakSumSquares D [] x * ζ x| +
            |2 * ∑ i : Fin q, D [i] x * fieldDerivative (C.Xl i) ζ x| +
              |u x * sumSquares C.Xl ζ x| := add_le_add (abs_add_le _ _) le_rfl
        _ ≤ Bg := by rw [hBg]; linarith
    · have h0 : ζ x = 0 := image_eq_zero_of_notMem_tsupport hxs
      have h1 : ∀ i : Fin q, fieldDerivative (C.Xl i) ζ x = 0 := fun i =>
        fieldDerivative_eq_zero_of_notMem_tsupport hxs
      have h2 : sumSquares C.Xl ζ x = 0 := by
        unfold sumSquares
        exact Finset.sum_eq_zero fun i _ =>
          fieldDerivative_fieldDerivative_eq_zero_of_notMem_tsupport hxs
      simp only [h0, h1, h2, mul_zero, Finset.sum_const_zero, add_zero]
      simpa using hBg0
  have hSg : (⨆ x : (F.V : Set (Fin (n + m) → ℝ)),
      ENNReal.ofReal |weakSumSquares (prodJetNoDrift C.Xl ζ u D) [] x|) ≤ ENNReal.ofReal Bg :=
    iSup_le fun x => ENNReal.ofReal_le_ofReal (hpt x x.2)
  -- (3) the sup norm of `u ζ`
  have hSv : (⨆ x : (F.V : Set (Fin (n + m) → ℝ)), ENNReal.ofReal |v x|) ≤ ENNReal.ofReal Mu := by
    refine iSup_le fun x => ENNReal.ofReal_le_ofReal ?_
    by_cases hxs : (x : Fin (n + m) → ℝ) ∈ tsupport ζ
    · obtain ⟨hz0, hz1⟩ := hζr x
      have hu' : |u x| ≤ Mu := abs_le_supBallNoDrift ν hu hBV (hζB hxs)
      show |u x * ζ x| ≤ Mu
      rw [abs_mul, abs_of_nonneg hz0]
      calc |u x| * ζ x ≤ Mu * 1 := mul_le_mul hu' hz1 hz0 hMu0
        _ = Mu := mul_one _
    · have h0 : ζ x = 0 := image_eq_zero_of_notMem_tsupport hxs
      show |u x * ζ x| ≤ Mu
      rw [h0, mul_zero, abs_zero]
      exact hMu0
  have hε0' : 0 ≤ Cc₁ * ε ^ (-γ₁) := mul_nonneg hCc₁ (Real.rpow_nonneg hε0.le _)
  have hfin : ∑ l : Fin q, holderENorm C.dl α (rhoBall C ν ξ₀ t) (D [l]) ≤
      ENNReal.ofReal (ε * Bg + Cc₁ * ε ^ (-γ₁) * Mu) := by
    refine hlhs.trans (hderiv.trans ?_)
    calc ENNReal.ofReal ε * (⨆ x : (F.V : Set (Fin (n + m) → ℝ)),
            ENNReal.ofReal |weakSumSquares (prodJetNoDrift C.Xl ζ u D) [] x|) +
          ENNReal.ofReal (Cc₁ * ε ^ (-γ₁)) *
            ⨆ x : (F.V : Set (Fin (n + m) → ℝ)), ENNReal.ofReal |v x|
        ≤ ENNReal.ofReal ε * ENNReal.ofReal Bg + ENNReal.ofReal (Cc₁ * ε ^ (-γ₁)) *
            ENNReal.ofReal Mu := add_le_add (mul_le_mul' le_rfl hSg) (mul_le_mul' le_rfl hSv)
      _ = ENNReal.ofReal (ε * Bg + Cc₁ * ε ^ (-γ₁) * Mu) := by
          rw [ENNReal.ofReal_add (mul_nonneg hε0.le hBg0) (mul_nonneg hε0' hMu0),
            ENNReal.ofReal_mul hε0.le, ENNReal.ofReal_mul hε0']
  have := ENNReal.toReal_le_of_le_ofReal (add_nonneg (mul_nonneg hε0.le hBg0)
    (mul_nonneg hε0' hMu0)) hfin
  exact this

end RothschildStein.P2
