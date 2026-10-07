-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.WeakExtensionHolder

/-!
# Hölder inputs: the parametrix, second-order, drift and higher-order identities for compact `C^{m,α}`

Continuation of `WeakExtensionHolder`: for `u` in the compact intrinsic Hölder class and a Hölder weak jet
`D`, the remaining parametrix and representation identities hold

* `weakExtension_parametrix_left_holder`: `a u = P₂ L̃u + F₂ u` **at every point of `V`** (both sides are
  continuous, the a.e. identity of `weakExtension_parametrix_left_drift` upgrades pointwise);
* `weakExtension_secondOrder_holder`, `weakExtension_drift_holder`, `weakExtension_higher_holder`: the weak
  identities with the pointwise actions of the type operators on the Hölder jet, together with continuity of
  the right-hand sides on `V` (Hölder continuity of type operators), identifying the continuous representatives
  (`eqOn_of_hasWeakWordDeriv_of_continuousOn`).

No Hölder norm density is used: the passage to the limit is through the `W^{m,2}_{X̃,0}(V)` approximation
(BB Thm 2.9 and the inclusion `C^{k,α}_{X̃,0} ⊂ W^{k,p}_{X̃,0}`) and the agreement of the `L^2` extensions with the pointwise actions on Hölder inputs
(continuity theorem).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped ENNReal Topology
namespace RothschildStein.P1

namespace LiftedChart

variable {n q : ℕ} {w : Fin (q + 1) → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {F : KernelFrame (n + m)}
  {r : ℕ} {H : H1.StandingHypotheses C.G r} {K : H1.FundamentalKernel C.G H}
  {hQ : 2 < (C.G.homogeneousDimension : ℝ)}

/-- **The parametrix identity `a u = P₂ L̃u + F₂ u`, pointwise for compactly supported intrinsic `C^{2,α}`
inputs**: if `a f = P₂ (L̃ f) + F₂ f` on `V` for tests `f`, then for `u` in the compact intrinsic class with
Hölder weak jet `D`, `a ξ u ξ = P₂ (L̃u) ξ + F₂ u ξ` for every `ξ ∈ V` (pointwise integral/PV actions;
`L̃u = D [0] + ∑ᵢ D [i, i]`). -/
theorem weakExtension_parametrix_left_holder (hF : C.IsStandardFrame F H K hQ)
    (hw0 : (w 0 : ℕ) = 2) (hw : ∀ j : Fin q, (w j.succ : ℕ) = 1)
    {a : TestFunction F.V ℝ (⊤ : ℕ∞)} {P₂ : TypeOperator F 2} {F₂ : TypeOperator F 1}
    (hzero : ∀ f : TestFunction F.V ℝ (⊤ : ℕ∞), ∀ ξ ∈ (F.V : Set (Fin (n + m) → ℝ)),
      a ξ * f ξ = P₂.apply (sumSquaresWithDrift C.Xl f) ξ + F₂.apply f ξ)
    (Ω₂ : Opens (Fin (n + m) → ℝ)) (G : S.DistanceGeometry Ω₂) (hG : G.d = C.dl)
    (hV : (F.V : Set (Fin (n + m) → ℝ)) ⊆ (Ω₂ : Set (Fin (n + m) → ℝ))) {α : ℝ} (hα0 : 0 < α)
    (hα1 : α < 1) {u : (Fin (n + m) → ℝ) → ℝ} (hu : memHolderXCompact w C.Xl C.dl F.V 2 α u)
    {D : List (Fin (q + 1)) → (Fin (n + m) → ℝ) → ℝ} (hD : IsHolderWeakJet w C.Xl C.dl F.V 2 α u D) :
    ∀ ξ ∈ (F.V : Set (Fin (n + m) → ℝ)),
      a ξ * u ξ = P₂.apply (weakSumSquaresWithDrift D) ξ + F₂.apply u ξ := by
  have : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨one_le_two⟩
  have hP1 : (1 : ℝ≥0∞) < 2 := by norm_num
  have hP : (2 : ℝ≥0∞) ≠ ⊤ := by simp
  obtain ⟨hu0, hD0⟩ := memSobolevXZero_of_holder hF Ω₂ G hG hV hα0 hu hD
  have hweak := weakExtension_parametrix_left_drift hF hw0 hw hzero hP1 hP hu0 hD0
  have hLD := hD.weakSumSquaresWithDrift_ne_top hw0 hw hα0
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

/-- **The parametrix identity `M_a = L̃* P₁ + F₁`, with the pointwise actions on Hölder inputs**: if
`∫ P₁ f · L̃φ = ∫ a f φ - ∫ F₁ f · φ` for tests `f, φ`, the same holds for every measurable `g` of finite
Hölder norm `‖g‖_{C^α(V)}` (in particular for compactly supported intrinsic `C^{2,α}` functions), with the
pointwise integral/PV actions `P₁ g`, `F₁ g` (by the continuity theorem, they are the `L^2` extensions a.e.). -/
theorem weakExtension_parametrix_adjoint_holder (hF : C.IsStandardFrame F H K hQ)
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

/-- **Second-order representation, for compactly supported intrinsic `C^{2,α}` inputs**: the weak
identity `X̃_i X̃_l(a u) = S_il L̃u + ∑ₖ S_ilk X̃ₖu + S_il0 u` holds on `V` with the pointwise actions on the
Hölder jet `D` of `u` (`X̃ₖu = D [k]`), and the right-hand side is continuous on `V`. -/
theorem weakExtension_secondOrder_holder (hF : C.IsStandardFrame F H K hQ)
    (hw0 : (w 0 : ℕ) = 2) (hw : ∀ j : Fin q, (w j.succ : ℕ) = 1)
    {a : TestFunction F.V ℝ (⊤ : ℕ∞)} {Sml : Fin q → Fin q → TypeOperator F 0}
    {Smlk : Fin q → Fin q → Fin q → TypeOperator F 0} {Sml0 : Fin q → Fin q → TypeOperator F 0}
    (hid : ∀ (i l : Fin q) (u : TestFunction F.V ℝ (⊤ : ℕ∞)),
      hasWeakWordDeriv C.Xl F.V [i.succ, l.succ] (fun x => a x * u x)
        (fun ξ => (Sml i l).apply (sumSquaresWithDrift C.Xl u) ξ +
          (∑ k : Fin q, (Smlk i l k).apply
            (fieldDerivative (C.Xl k.succ) (u : (Fin (n + m) → ℝ) → ℝ)) ξ) +
          (Sml0 i l).apply u ξ))
    (Ω₂ : Opens (Fin (n + m) → ℝ)) (G : S.DistanceGeometry Ω₂) (hG : G.d = C.dl)
    (hV : (F.V : Set (Fin (n + m) → ℝ)) ⊆ (Ω₂ : Set (Fin (n + m) → ℝ))) {α : ℝ} (hα0 : 0 < α)
    (hα1 : α < 1) {u : (Fin (n + m) → ℝ) → ℝ} (hu : memHolderXCompact w C.Xl C.dl F.V 2 α u)
    {D : List (Fin (q + 1)) → (Fin (n + m) → ℝ) → ℝ} (hD : IsHolderWeakJet w C.Xl C.dl F.V 2 α u D)
    (i l : Fin q) :
    hasWeakWordDeriv C.Xl F.V [i.succ, l.succ] (fun x => a x * u x)
      (fun ξ => (Sml i l).apply (weakSumSquaresWithDrift D) ξ +
        (∑ k : Fin q, (Smlk i l k).apply (D [k.succ]) ξ) + (Sml0 i l).apply u ξ) ∧
    ContinuousOn (fun ξ => (Sml i l).apply (weakSumSquaresWithDrift D) ξ +
        (∑ k : Fin q, (Smlk i l k).apply (D [k.succ]) ξ) + (Sml0 i l).apply u ξ)
      (F.V : Set (Fin (n + m) → ℝ)) := by
  have : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨one_le_two⟩
  have hP1 : (1 : ℝ≥0∞) < 2 := by norm_num
  have hP : (2 : ℝ≥0∞) ≠ ⊤ := by simp
  obtain ⟨hu0, hD0⟩ := memSobolevXZero_of_holder hF Ω₂ G hG hV hα0 hu hD
  have hweak := weakExtension_secondOrder hF hw0 hw hid hP1 hP hu0 hD0 i l
  have hLD := hD.weakSumSquaresWithDrift_ne_top hw0 hw hα0
  have hu1 : holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) u ≠ ⊤ := ne_top_of_lt hu.1.1
  have hDk : ∀ k : Fin q, holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) (D [k.succ]) ≠ ⊤ :=
    fun k => (hD _ (horizontal_mem_wordFamily hw k)).2
  have hmeas : ∀ {g : (Fin (n + m) → ℝ) → ℝ},
      holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) g ≠ ⊤ →
      AEStronglyMeasurable g (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) := fun hg =>
    aestronglyMeasurable_of_holderENorm_lt_top hF.lifted.subset_U F.V.isOpen.measurableSet hα0
      (lt_top_iff_ne_top.2 hg)
  have e1 := (Sml i l).lpAct_holder hF hP1 hP hα0 hα1 hLD (hmeas hLD)
  have e2 := ae_eq_finset_sum (μ := volume.restrict (F.V : Set (Fin (n + m) → ℝ)))
    (Finset.univ : Finset (Fin q))
    (f := fun k ξ => (Smlk i l k).lpAct hF hP1 hP (D [k.succ]) ξ)
    (g := fun k ξ => (Smlk i l k).apply (D [k.succ]) ξ) fun k _ =>
    (Smlk i l k).lpAct_holder hF hP1 hP hα0 hα1 (hDk k) (hmeas (hDk k))
  have e3 := (Sml0 i l).lpAct_holder hF hP1 hP hα0 hα1 hu1 (hmeas hu1)
  refine ⟨S.hasWeakWordDeriv_congr_ae C.Xl F.V hweak Filter.EventuallyEq.rfl ((e1.add e2).add e3),
    (((Sml i l).continuousOn_apply_holder hF hα0 hα1 hLD).add
      (continuousOn_finsetSum _ fun k _ =>
        (Smlk i l k).continuousOn_apply_holder hF hα0 hα1 (hDk k))).add
      ((Sml0 i l).continuousOn_apply_holder hF hα0 hα1 hu1)⟩

end LiftedChart

namespace LiftedChart

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {F : KernelFrame (n + m)}
  {r : ℕ} {H : H1.StandingHypotheses C.G r} {K : H1.FundamentalKernel C.G H}
  {hQ : 2 < (C.G.homogeneousDimension : ℝ)}

/-- **The higher-order representation for compactly supported intrinsic `C^{|I|,α}` inputs** (no drift, all weights one):
if `X̃_I(a φ) = ∑_J S_J X̃_J L̃φ + ∑_K T_K X̃_K φ` weakly on `V` for tests `φ`, then for `u` in the compact
intrinsic class `memHolderXCompact w C.Xl C.dl V |I| α u` (`0 < α < 1`) with Hölder weak jet `D`,
`X̃_I(a u) = ∑_J S_J (∑ᵢ D (J ++ [i, i])) + ∑_K T_K (D K)` weakly on `V` with the pointwise actions of the
type operators, and the right-hand side is continuous on `V`. -/
theorem weakExtension_higher_holder (hF : C.IsStandardFrame F H K hQ) (hw : ∀ j, (w j : ℕ) = 1)
    {a : TestFunction F.V ℝ (⊤ : ℕ∞)} (I : List (Fin k)) (hI : 2 ≤ I.length)
    {Sf Tf : List (Fin k) → TypeOperator F 0}
    (hid : ∀ u : TestFunction F.V ℝ (⊤ : ℕ∞),
      hasWeakWordDeriv C.Xl F.V I (fun x => a x * u x)
        (fun ξ => (∑ J ∈ repWords k (I.length - 2),
            (Sf J).apply (wordDerivative C.Xl J (sumSquares C.Xl (u : (Fin (n + m) → ℝ) → ℝ))) ξ) +
          ∑ K ∈ repWords k (I.length - 1),
            (Tf K).apply (wordDerivative C.Xl K (u : (Fin (n + m) → ℝ) → ℝ)) ξ))
    (Ω₂ : Opens (Fin (n + m) → ℝ)) (G : S.DistanceGeometry Ω₂) (hG : G.d = C.dl)
    (hV : (F.V : Set (Fin (n + m) → ℝ)) ⊆ (Ω₂ : Set (Fin (n + m) → ℝ))) {α : ℝ} (hα0 : 0 < α)
    (hα1 : α < 1) {u : (Fin (n + m) → ℝ) → ℝ}
    (hu : memHolderXCompact w C.Xl C.dl F.V I.length α u)
    {D : List (Fin k) → (Fin (n + m) → ℝ) → ℝ}
    (hD : IsHolderWeakJet w C.Xl C.dl F.V I.length α u D) :
    hasWeakWordDeriv C.Xl F.V I (fun x => a x * u x)
      (fun ξ => (∑ J ∈ repWords k (I.length - 2), (Sf J).apply (weakSumSquares D J) ξ) +
        ∑ K ∈ repWords k (I.length - 1), (Tf K).apply (D K) ξ) ∧
    ContinuousOn (fun ξ => (∑ J ∈ repWords k (I.length - 2), (Sf J).apply (weakSumSquares D J) ξ) +
        ∑ K ∈ repWords k (I.length - 1), (Tf K).apply (D K) ξ) (F.V : Set (Fin (n + m) → ℝ)) := by
  classical
  have : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨one_le_two⟩
  have hP1 : (1 : ℝ≥0∞) < 2 := by norm_num
  have hP : (2 : ℝ≥0∞) ≠ ⊤ := by simp
  obtain ⟨hu0, hD0⟩ := memSobolevXZero_of_holder hF Ω₂ G hG hV hα0 hu hD
  have hweak := weakExtension_higher hF hw I hI hid hP1 hP hu0 hD0
  have hmeas : ∀ {g : (Fin (n + m) → ℝ) → ℝ},
      holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) g ≠ ⊤ →
      AEStronglyMeasurable g (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) := fun hg =>
    aestronglyMeasurable_of_holderENorm_lt_top hF.lifted.subset_U F.V.isOpen.measurableSet hα0
      (lt_top_iff_ne_top.2 hg)
  have hmemJ : ∀ J ∈ repWords k (I.length - 2), ∀ i : Fin k, J ++ [i, i] ∈ wordFamily w I.length :=
    fun J hJ i => by
      have := mem_repWords.1 hJ
      rw [S.mem_wordFamily_iff, wordWeight_eq_length hw]
      simp only [List.length_append, List.length_cons, List.length_nil]
      omega
  have hLJ : ∀ J ∈ repWords k (I.length - 2),
      holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) (weakSumSquares D J) ≠ ⊤ := fun J hJ =>
    holderENorm_finset_sum_ne_top hα0.le _ _ fun i _ => (hD _ (hmemJ J hJ i)).2
  have hDK : ∀ K ∈ repWords k (I.length - 1),
      holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) (D K) ≠ ⊤ := fun K hK =>
    (hD K ((S.mem_wordFamily_iff w _ K).2 (by
      have := mem_repWords.1 hK
      rw [wordWeight_eq_length hw]
      omega))).2
  have e1 := ae_eq_finset_sum (μ := volume.restrict (F.V : Set (Fin (n + m) → ℝ)))
    (repWords k (I.length - 2))
    (f := fun J ξ => (Sf J).lpAct hF hP1 hP (weakSumSquares D J) ξ)
    (g := fun J ξ => (Sf J).apply (weakSumSquares D J) ξ) fun J hJ =>
    (Sf J).lpAct_holder hF hP1 hP hα0 hα1 (hLJ J hJ) (hmeas (hLJ J hJ))
  have e2 := ae_eq_finset_sum (μ := volume.restrict (F.V : Set (Fin (n + m) → ℝ)))
    (repWords k (I.length - 1))
    (f := fun K ξ => (Tf K).lpAct hF hP1 hP (D K) ξ)
    (g := fun K ξ => (Tf K).apply (D K) ξ) fun K hK =>
    (Tf K).lpAct_holder hF hP1 hP hα0 hα1 (hDK K hK) (hmeas (hDK K hK))
  refine ⟨S.hasWeakWordDeriv_congr_ae C.Xl F.V hweak Filter.EventuallyEq.rfl (e1.add e2),
    (continuousOn_finsetSum _ fun J hJ =>
      (Sf J).continuousOn_apply_holder hF hα0 hα1 (hLJ J hJ)).add
      (continuousOn_finsetSum _ fun K hK =>
        (Tf K).continuousOn_apply_holder hF hα0 hα1 (hDK K hK))⟩

end LiftedChart

end RothschildStein.P1
