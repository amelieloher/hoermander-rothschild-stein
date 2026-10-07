-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.WeakExtensionNoDriftBasic
public import RothschildStein.P1.LiftedDistanceGeometryCorollaries

/-!
# Hölder and noncompact inputs, no drift: compactly supported intrinsic `C^{2,α}` inputs

The no-drift counterparts of `weakExtension_parametrix_left_holder`, `weakExtension_parametrix_adjoint_holder`,
`weakExtension_firstOrder_holder`, `weakExtension_firstOrder_intrinsic` and `weakExtension_secondOrder_holder`
(alphabet `Fin k`, all weights one, `L̃ = sumSquares`): for `u` in the compact intrinsic Hölder class
`memHolderXCompact w C.Xl C.dl V 2 α u` (`0 < α < 1`) with Hölder weak jet `D`, the weak parametrix and
first- and second-order identities hold with the pointwise integral/PV actions on the Hölder jet, both sides are continuous on `V`, and
`a u = P₂ L̃u + F₂ u` holds at every point of `V`. `L̃u = ∑ᵢ D [i, i]` (`weakSumSquares D []`).

The `(HD1)`-`(HD2)` package of the lifted control distance is
`LiftedChart.distanceGeometry`, which needs no further hypothesis; no distance-geometry hypothesis is carried.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped ENNReal Topology BigOperators
namespace RothschildStein.P1

namespace LiftedChart

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {F : KernelFrame (n + m)}
  {r : ℕ} {H : H1.StandingHypotheses C.G r} {K : H1.FundamentalKernel C.G H}
  {hQ : 2 < (C.G.homogeneousDimension : ℝ)}

/-- No drift (all weights one): a single generator `[j]` has weight one,
so lies in every jet of order two. -/
theorem horizontal_mem_wordFamily_noDrift (hw : ∀ j, (w j : ℕ) = 1) (j : Fin k) :
    [j] ∈ wordFamily w 2 :=
  (S.mem_wordFamily_iff w 2 _).2 (by simp [wordWeight, hw j])

/-- No drift: the weak `L̃ u = ∑ᵢ D [i, i]` of a Hölder weak jet has
finite Hölder norm. -/
theorem IsHolderWeakJet.weakSumSquares_nil_ne_top (hw : ∀ j, (w j : ℕ) = 1) {α : ℝ} (hα0 : 0 < α)
    {u : (Fin (n + m) → ℝ) → ℝ} {D : List (Fin k) → (Fin (n + m) → ℝ) → ℝ}
    (hD : IsHolderWeakJet w C.Xl C.dl F.V 2 α u D) :
    holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) (weakSumSquares D []) ≠ ⊤ :=
  holderENorm_finset_sum_ne_top hα0.le (Finset.univ : Finset (Fin k)) (fun i => D [i, i])
    fun i _ => (hD [i, i] ((S.mem_wordFamily_iff w 2 _).2 (by simp [wordWeight, hw i]))).2

/-- **The parametrix identity `a u = P₂ L̃u + F₂ u`, pointwise for compactly supported intrinsic `C^{2,α}` inputs,
no drift**: if `a f = P₂ (L̃ f) + F₂ f` on `V` for tests `f` (`L̃ = ∑ᵢ X̃ᵢ²`), then for `u` in the compact
intrinsic class with Hölder weak jet `D`, `a ξ u ξ = P₂ (L̃u) ξ + F₂ u ξ` for every `ξ ∈ V` (pointwise
integral/PV actions; `L̃u = ∑ᵢ D [i, i]`). -/
theorem weakExtension_parametrix_left_holder_noDrift (hF : C.IsStandardFrame F H K hQ)
    (hw : ∀ j, (w j : ℕ) = 1) {a : TestFunction F.V ℝ (⊤ : ℕ∞)}
    {P₂ : TypeOperator F 2} {F₂ : TypeOperator F 1}
    (hzero : ∀ f : TestFunction F.V ℝ (⊤ : ℕ∞), ∀ ξ ∈ (F.V : Set (Fin (n + m) → ℝ)),
      a ξ * f ξ = P₂.apply (sumSquares C.Xl f) ξ + F₂.apply f ξ)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {u : (Fin (n + m) → ℝ) → ℝ}
    (hu : memHolderXCompact w C.Xl C.dl F.V 2 α u)
    {D : List (Fin k) → (Fin (n + m) → ℝ) → ℝ} (hD : IsHolderWeakJet w C.Xl C.dl F.V 2 α u D) :
    ∀ ξ ∈ (F.V : Set (Fin (n + m) → ℝ)),
      a ξ * u ξ = P₂.apply (weakSumSquares D []) ξ + F₂.apply u ξ := by
  have : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨one_le_two⟩
  have hP1 : (1 : ℝ≥0∞) < 2 := by norm_num
  have hP : (2 : ℝ≥0∞) ≠ ⊤ := by simp
  obtain ⟨hu0, hD0⟩ := memSobolevXZero_of_holder_lifted hF hα0 hu hD
  have hweak := weakExtension_parametrix_left_noDrift hF hw hzero hP1 hP hu0 hD0
  have hLD := hD.weakSumSquares_nil_ne_top hw hα0
  have hu1 : holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) u ≠ ⊤ := ne_top_of_lt hu.1.1
  have hLDm := aestronglyMeasurable_of_holderENorm_lt_top hF.lifted.subset_U
    F.V.isOpen.measurableSet hα0 (lt_top_iff_ne_top.2 hLD)
  have hum := aestronglyMeasurable_of_holderENorm_lt_top hF.lifted.subset_U
    F.V.isOpen.measurableSet hα0 (lt_top_iff_ne_top.2 hu1)
  have e1 := P₂.lpAct_holder hF hP1 hP hα0 hα1 hLD hLDm
  have e2 := F₂.lpAct_holder hF hP1 hP hα0 hα1 hu1 hum
  have hau : ContinuousOn (fun x => a x * u x) (F.V : Set (Fin (n + m) → ℝ)) :=
    a.continuous.continuousOn.mul (continuousOn_of_holderENorm_lt_top hF.lifted.subset_U hα0 hu.1.1)
  exact Measure.eqOn_open_of_ae_eq (hweak.trans (e1.add e2)) F.V.isOpen hau
    ((P₂.continuousOn_apply_holder hF hα0 hα1 hLD).add (F₂.continuousOn_apply_holder hF hα0 hα1 hu1))

/-- **The parametrix identity `M_a = L̃* P₁ + F₁`, with the pointwise actions on Hölder inputs, no drift**: if
`∫ P₁ f · L̃φ = ∫ a f φ - ∫ F₁ f · φ` for tests `f, φ`, the same holds for every measurable `g` of finite
Hölder norm `‖g‖_{C^α(V)}`, with the pointwise integral/PV actions `P₁ g`, `F₁ g` (by the continuity theorem, they are the `L^2`
extensions a.e.). The proof is alphabet-generic; this is the statement for the no-drift alphabet `Fin k`. -/
theorem weakExtension_parametrix_adjoint_holder_noDrift (hF : C.IsStandardFrame F H K hQ)
    {Lt : ((Fin (n + m) → ℝ) → ℝ) → (Fin (n + m) → ℝ) → ℝ}
    (Lap : TestFunction F.V ℝ (⊤ : ℕ∞) → TestFunction F.V ℝ (⊤ : ℕ∞))
    (hLap : ∀ u, (Lap u : (Fin (n + m) → ℝ) → ℝ) = Lt u) {a : TestFunction F.V ℝ (⊤ : ℕ∞)}
    {P₁ : TypeOperator F 2} {F₁ : TypeOperator F 1}
    (hadj : ∀ f φ : TestFunction F.V ℝ (⊤ : ℕ∞),
      (∫ ξ in (F.V : Set (Fin (n + m) → ℝ)), P₁.apply f ξ * Lt φ ξ) =
        (∫ ξ in (F.V : Set (Fin (n + m) → ℝ)), a ξ * f ξ * φ ξ) -
          ∫ ξ in (F.V : Set (Fin (n + m) → ℝ)), F₁.apply f ξ * φ ξ)
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {g : (Fin (n + m) → ℝ) → ℝ}
    (hg : holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) g ≠ ⊤)
    (hgm : AEStronglyMeasurable g (volume.restrict (F.V : Set (Fin (n + m) → ℝ))))
    (φ : TestFunction F.V ℝ (⊤ : ℕ∞)) :
    (∫ ξ in (F.V : Set (Fin (n + m) → ℝ)), P₁.apply g ξ * Lt φ ξ) =
      (∫ ξ in (F.V : Set (Fin (n + m) → ℝ)), a ξ * g ξ * φ ξ) -
        ∫ ξ in (F.V : Set (Fin (n + m) → ℝ)), F₁.apply g ξ * φ ξ := by
  have : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨one_le_two⟩
  have hP1 : (1 : ℝ≥0∞) < 2 := by norm_num
  have hP : (2 : ℝ≥0∞) ≠ ⊤ := by simp
  have hgL := memLp_of_holderENorm_ne_top F.V.isOpen.measurableSet hF.lifted.volume_lt_top hg hgm 2
  have h := weakExtension_parametrix_adjoint hF Lap hLap hadj hP1 hP hgL φ
  have e1 := P₁.lpAct_holder hF hP1 hP hα0 hα1 hg hgm
  have e2 := F₁.lpAct_holder hF hP1 hP hα0 hα1 hg hgm
  have i1 : (∫ ξ in (F.V : Set (Fin (n + m) → ℝ)), P₁.apply g ξ * Lt φ ξ) =
      ∫ ξ in (F.V : Set (Fin (n + m) → ℝ)), P₁.lpAct hF hP1 hP g ξ * Lt φ ξ :=
    integral_congr_ae (by filter_upwards [e1] with ξ hξ; rw [hξ])
  have i2 : (∫ ξ in (F.V : Set (Fin (n + m) → ℝ)), F₁.apply g ξ * φ ξ) =
      ∫ ξ in (F.V : Set (Fin (n + m) → ℝ)), F₁.lpAct hF hP1 hP g ξ * φ ξ :=
    integral_congr_ae (by filter_upwards [e2] with ξ hξ; rw [hξ])
  rw [i1, i2]
  exact h

/-- **First-order representation, for compactly supported intrinsic `C^{2,α}` inputs, no drift.** Let
`X̃_l(a φ) = F_l L̃φ + S_l φ` weakly for tests `φ`. For `u` in the compact intrinsic class
`memHolderXCompact w C.Xl C.dl V 2 α u` (`0 < α < 1`) with Hölder weak jet `D`, `X̃_l(a u) = F_l (L̃u) + S_l u`
weakly on `V`, with the pointwise integral/PV actions on the Hölder inputs `L̃u = ∑ᵢ D [i, i]` and `u`; the
right-hand side is continuous on `V`. -/
theorem weakExtension_firstOrder_holder_noDrift (hF : C.IsStandardFrame F H K hQ)
    (hw : ∀ j, (w j : ℕ) = 1) {a : TestFunction F.V ℝ (⊤ : ℕ∞)} {Fl : Fin k → TypeOperator F 1}
    {Sl : Fin k → TypeOperator F 0}
    (hid : ∀ (l : Fin k) (u : TestFunction F.V ℝ (⊤ : ℕ∞)),
      hasWeakWordDeriv C.Xl F.V [l] (fun x => a x * u x)
        (fun ξ => (Fl l).apply (sumSquares C.Xl u) ξ + (Sl l).apply u ξ))
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {u : (Fin (n + m) → ℝ) → ℝ}
    (hu : memHolderXCompact w C.Xl C.dl F.V 2 α u)
    {D : List (Fin k) → (Fin (n + m) → ℝ) → ℝ} (hD : IsHolderWeakJet w C.Xl C.dl F.V 2 α u D)
    (l : Fin k) :
    hasWeakWordDeriv C.Xl F.V [l] (fun x => a x * u x)
      (fun ξ => (Fl l).apply (weakSumSquares D []) ξ + (Sl l).apply u ξ) ∧
    ContinuousOn (fun ξ => (Fl l).apply (weakSumSquares D []) ξ + (Sl l).apply u ξ)
      (F.V : Set (Fin (n + m) → ℝ)) := by
  have : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨one_le_two⟩
  have hP1 : (1 : ℝ≥0∞) < 2 := by norm_num
  have hP : (2 : ℝ≥0∞) ≠ ⊤ := by simp
  obtain ⟨hu0, hD0⟩ := memSobolevXZero_of_holder_lifted hF hα0 hu hD
  have hweak := weakExtension_firstOrder_noDrift hF hw hid hP1 hP hu0 hD0 l
  have hLD := hD.weakSumSquares_nil_ne_top hw hα0
  have hu1 : holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) u ≠ ⊤ := ne_top_of_lt hu.1.1
  have hLDm := aestronglyMeasurable_of_holderENorm_lt_top hF.lifted.subset_U
    F.V.isOpen.measurableSet hα0 (lt_top_iff_ne_top.2 hLD)
  have hum := aestronglyMeasurable_of_holderENorm_lt_top hF.lifted.subset_U
    F.V.isOpen.measurableSet hα0 (lt_top_iff_ne_top.2 hu1)
  have e1 := (Fl l).lpAct_holder hF hP1 hP hα0 hα1 hLD hLDm
  have e2 := (Sl l).lpAct_holder hF hP1 hP hα0 hα1 hu1 hum
  exact ⟨S.hasWeakWordDeriv_congr_ae C.Xl F.V hweak Filter.EventuallyEq.rfl (e1.add e2),
    ((Fl l).continuousOn_apply_holder hF hα0 hα1 hLD).add
      ((Sl l).continuousOn_apply_holder hF hα0 hα1 hu1)⟩

/-- **First-order representation, intrinsic form, no drift.** Under the hypotheses of
`weakExtension_firstOrder_holder_noDrift`, the continuous function `F_l (L̃u) + S_l u` is an *intrinsic*
derivative `X̃_l(a u)` of `a u` on `V` (a continuous weak derivative of a continuous function is
intrinsic). -/
theorem weakExtension_firstOrder_intrinsic_noDrift (hF : C.IsStandardFrame F H K hQ)
    (hw : ∀ j, (w j : ℕ) = 1) {a : TestFunction F.V ℝ (⊤ : ℕ∞)} {Fl : Fin k → TypeOperator F 1}
    {Sl : Fin k → TypeOperator F 0}
    (hid : ∀ (l : Fin k) (u : TestFunction F.V ℝ (⊤ : ℕ∞)),
      hasWeakWordDeriv C.Xl F.V [l] (fun x => a x * u x)
        (fun ξ => (Fl l).apply (sumSquares C.Xl u) ξ + (Sl l).apply u ξ))
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {u : (Fin (n + m) → ℝ) → ℝ}
    (hu : memHolderXCompact w C.Xl C.dl F.V 2 α u)
    {D : List (Fin k) → (Fin (n + m) → ℝ) → ℝ} (hD : IsHolderWeakJet w C.Xl C.dl F.V 2 α u D)
    (l : Fin k) :
    hasIntrinsicWordDeriv C.Xl F.V [l] (fun x => a x * u x)
      (fun ξ => (Fl l).apply (weakSumSquares D []) ξ + (Sl l).apply u ξ) := by
  obtain ⟨hweak, hc⟩ := weakExtension_firstOrder_holder_noDrift hF hw hid hα0 hα1 hu hD l
  have hau : ContinuousOn (fun x => a x * u x) (F.V : Set (Fin (n + m) → ℝ)) :=
    a.continuous.continuousOn.mul (continuousOn_of_holderENorm_lt_top hF.lifted.subset_U hα0 hu.1.1)
  exact hasIntrinsicWordDeriv_singleton_of_weak hF.lifted.contDiffOn_Xl l hau hc hweak

/-- **Second-order representation, for compactly supported intrinsic `C^{2,α}` inputs, no drift**: the weak
identity `X̃_i X̃_l(a u) = S_il L̃u + ∑ₖ S_ilk X̃ₖu + S_il0 u` holds on `V` with the pointwise actions on the
Hölder jet `D` of `u` (`X̃ₖu = D [k]`), and the right-hand side is continuous on `V`. -/
theorem weakExtension_secondOrder_holder_noDrift (hF : C.IsStandardFrame F H K hQ)
    (hw : ∀ j, (w j : ℕ) = 1) {a : TestFunction F.V ℝ (⊤ : ℕ∞)}
    {Sml : Fin k → Fin k → TypeOperator F 0} {Smlk : Fin k → Fin k → Fin k → TypeOperator F 0}
    {Sml0 : Fin k → Fin k → TypeOperator F 0}
    (hid : ∀ (i l : Fin k) (u : TestFunction F.V ℝ (⊤ : ℕ∞)),
      hasWeakWordDeriv C.Xl F.V [i, l] (fun x => a x * u x)
        (fun ξ => (Sml i l).apply (sumSquares C.Xl u) ξ +
          (∑ j : Fin k, (Smlk i l j).apply
            (fieldDerivative (C.Xl j) (u : (Fin (n + m) → ℝ) → ℝ)) ξ) +
          (Sml0 i l).apply u ξ))
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {u : (Fin (n + m) → ℝ) → ℝ}
    (hu : memHolderXCompact w C.Xl C.dl F.V 2 α u)
    {D : List (Fin k) → (Fin (n + m) → ℝ) → ℝ} (hD : IsHolderWeakJet w C.Xl C.dl F.V 2 α u D)
    (i l : Fin k) :
    hasWeakWordDeriv C.Xl F.V [i, l] (fun x => a x * u x)
      (fun ξ => (Sml i l).apply (weakSumSquares D []) ξ +
        (∑ j : Fin k, (Smlk i l j).apply (D [j]) ξ) + (Sml0 i l).apply u ξ) ∧
    ContinuousOn (fun ξ => (Sml i l).apply (weakSumSquares D []) ξ +
        (∑ j : Fin k, (Smlk i l j).apply (D [j]) ξ) + (Sml0 i l).apply u ξ)
      (F.V : Set (Fin (n + m) → ℝ)) := by
  have : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨one_le_two⟩
  have hP1 : (1 : ℝ≥0∞) < 2 := by norm_num
  have hP : (2 : ℝ≥0∞) ≠ ⊤ := by simp
  obtain ⟨hu0, hD0⟩ := memSobolevXZero_of_holder_lifted hF hα0 hu hD
  have hweak := weakExtension_secondOrder_noDrift hF hw hid hP1 hP hu0 hD0 i l
  have hLD := hD.weakSumSquares_nil_ne_top hw hα0
  have hu1 : holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) u ≠ ⊤ := ne_top_of_lt hu.1.1
  have hDk : ∀ j : Fin k, holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) (D [j]) ≠ ⊤ :=
    fun j => (hD _ (horizontal_mem_wordFamily_noDrift hw j)).2
  have hmeas : ∀ {g : (Fin (n + m) → ℝ) → ℝ},
      holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) g ≠ ⊤ →
      AEStronglyMeasurable g (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) := fun hg =>
    aestronglyMeasurable_of_holderENorm_lt_top hF.lifted.subset_U F.V.isOpen.measurableSet hα0
      (lt_top_iff_ne_top.2 hg)
  have e1 := (Sml i l).lpAct_holder hF hP1 hP hα0 hα1 hLD (hmeas hLD)
  have e2 := ae_eq_finset_sum (μ := volume.restrict (F.V : Set (Fin (n + m) → ℝ)))
    (Finset.univ : Finset (Fin k))
    (f := fun j ξ => (Smlk i l j).lpAct hF hP1 hP (D [j]) ξ)
    (g := fun j ξ => (Smlk i l j).apply (D [j]) ξ) fun j _ =>
    (Smlk i l j).lpAct_holder hF hP1 hP hα0 hα1 (hDk j) (hmeas (hDk j))
  have e3 := (Sml0 i l).lpAct_holder hF hP1 hP hα0 hα1 hu1 (hmeas hu1)
  refine ⟨S.hasWeakWordDeriv_congr_ae C.Xl F.V hweak Filter.EventuallyEq.rfl ((e1.add e2).add e3),
    (((Sml i l).continuousOn_apply_holder hF hα0 hα1 hLD).add
      (continuousOn_finsetSum _ fun j _ =>
        (Smlk i l j).continuousOn_apply_holder hF hα0 hα1 (hDk j))).add
      ((Sml0 i l).continuousOn_apply_holder hF hα0 hα1 hu1)⟩

end LiftedChart

end RothschildStein.P1
