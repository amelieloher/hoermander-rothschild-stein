-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.WeakExtensionNoDriftSmooth
public import RothschildStein.P1.WeakExtensionNoDriftHolder

/-!
# No-drift weak extension of the parametrix and the first- and second-order identities

One declaration per identity, conditional exactly on the hypotheses of the no-drift parametrix and representation theorems
(`SignedParametrixNoDrift`, `TypeKernelIntegrable`, `LeftDifferentiation`, `RightDifferentiation`, `DerivativeTransfer`, the density data of
`SignedParametrixNoDrift`), returning the operators of the parametrix and the first- and second-order representations together with

* the identity on tests (as in `representation_*_noDrift_of`);
* its extension to `u ∈ W^{2,p}_{X̃,0}(V)`, `1 < p < ∞`: weak identity with the bounded `L^p` extensions of
  the continuity theorem applied to the weak jet;
* its validity for smooth noncompact inputs `u ∈ C^∞(V)` (cutoff equal to one near every input support);
* its validity for compactly supported intrinsic `C^{2,α}` inputs, `0 < α < 1`: weak identity with the
  pointwise integral/PV actions on the Hölder jet, continuity of the right-hand side, and (first order) the
  intrinsic form. The `(HD1)`-`(HD2)` package of the lifted control distance is
  `LiftedChart.distanceGeometry`, which needs no further hypothesis.

None of this regularizes an arbitrary distribution; every input is in the closure of the tests, smooth, or
compactly supported intrinsic Hölder. All weights are one, the alphabet is `Fin k`, `L̃ = sumSquares`,
`L̃u = ∑ᵢ D [i, i]` (`weakSumSquares D []`).
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

/-- **The signed parametrix identities without drift and their extensions.** For the
cutoffs `a, b ∈ C_c^∞(V)`, `a b = a`, and `SignedParametrixNoDrift` (BB Thm 11.25): the conclusion of
`SignedParametrixNoDrift` for operators `P₁, P₂, F₁, F₂`, and for these operators

* the distributional identity `M_a = L̃* P₁ + F₁` for every `g ∈ L^P(V)` (`1 < P < ∞`, bounded extensions) and,
  with the pointwise actions, for every measurable `g` of finite Hölder norm;
* `a u = P₂ L̃u + F₂ u`: a.e. on `V` for every `u ∈ W^{2,P}_{X̃,0}(V)` (weak `L̃u`), at every point of `V` for
  smooth `u` on `V` and for every compactly supported intrinsic `C^{2,α}` input. -/
theorem weakExtension_parametrix_full_noDrift_of (hF : C.IsStandardFrame F H K hQ)
    (hw : ∀ j, (w j : ℕ) = 1)
    {c : (Fin (n + m) → ℝ) → ℝ} (hc : ContDiffOn ℝ (⊤ : ℕ∞) c (F.V : Set (Fin (n + m) → ℝ)))
    (hc0 : ∀ ξ ∈ (F.V : Set (Fin (n + m) → ℝ)), 0 < c ξ) (a b : TestFunction F.V ℝ (⊤ : ℕ∞))
    (hab : ∀ ξ, a ξ * b ξ = a ξ) (hParametrix : SignedParametrixNoDrift F C.Xl c a b) :
    ∃ (P₁ P₂ : TypeOperator F 2) (F₁ F₂ : TypeOperator F 1),
      (∀ ξ η, ξ ≠ η → P₁.kernel ξ η = a ξ * F.Γs (F.Θ η ξ) * (b η / c η)) ∧
      (∀ ξ η, ξ ≠ η → P₂.kernel ξ η = b ξ / c ξ * (a η * F.Γ (F.Θ η ξ))) ∧
      (∀ ξ η, ξ ≠ η → P₂.kernel ξ η = P₁.kernel η ξ) ∧
      (∀ ξ η, ξ ≠ η → F₂.kernel ξ η = F₁.kernel η ξ) ∧
      IsTypeKernelOn F true 1 F₁.kernel ∧ IsTypeKernelOn F false 1 F₂.kernel ∧
      (∀ f φ : TestFunction F.V ℝ (⊤ : ℕ∞),
        IntegrableOn (fun ξ => P₁.apply f ξ * sumSquares C.Xl φ ξ)
          (F.V : Set (Fin (n + m) → ℝ)) ∧
        IntegrableOn (fun ξ => F₁.apply f ξ * φ ξ) (F.V : Set (Fin (n + m) → ℝ)) ∧
        (∫ ξ in (F.V : Set (Fin (n + m) → ℝ)), P₁.apply f ξ * sumSquares C.Xl φ ξ) =
          (∫ ξ in (F.V : Set (Fin (n + m) → ℝ)), a ξ * f ξ * φ ξ) -
            ∫ ξ in (F.V : Set (Fin (n + m) → ℝ)), F₁.apply f ξ * φ ξ) ∧
      (∀ f : TestFunction F.V ℝ (⊤ : ℕ∞), ∀ ξ ∈ (F.V : Set (Fin (n + m) → ℝ)),
        a ξ * f ξ = P₂.apply (sumSquares C.Xl f) ξ + F₂.apply f ξ) ∧
      (∀ (P : ℝ≥0∞) [Fact (1 ≤ P)] (hP1 : 1 < P) (hP : P ≠ ⊤) (g : (Fin (n + m) → ℝ) → ℝ),
        MemLp g P (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) →
        ∀ φ : TestFunction F.V ℝ (⊤ : ℕ∞),
          (∫ ξ in (F.V : Set (Fin (n + m) → ℝ)),
              P₁.lpAct hF hP1 hP g ξ * sumSquares C.Xl φ ξ) =
            (∫ ξ in (F.V : Set (Fin (n + m) → ℝ)), a ξ * g ξ * φ ξ) -
              ∫ ξ in (F.V : Set (Fin (n + m) → ℝ)), F₁.lpAct hF hP1 hP g ξ * φ ξ) ∧
      (∀ α : ℝ, 0 < α → α < 1 → ∀ g : (Fin (n + m) → ℝ) → ℝ,
        holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) g ≠ ⊤ →
        AEStronglyMeasurable g (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) →
        ∀ φ : TestFunction F.V ℝ (⊤ : ℕ∞),
          (∫ ξ in (F.V : Set (Fin (n + m) → ℝ)), P₁.apply g ξ * sumSquares C.Xl φ ξ) =
            (∫ ξ in (F.V : Set (Fin (n + m) → ℝ)), a ξ * g ξ * φ ξ) -
              ∫ ξ in (F.V : Set (Fin (n + m) → ℝ)), F₁.apply g ξ * φ ξ) ∧
      (∀ (P : ℝ≥0∞) [Fact (1 ≤ P)] (hP1 : 1 < P) (hP : P ≠ ⊤) (u : (Fin (n + m) → ℝ) → ℝ)
          (D : List (Fin k) → (Fin (n + m) → ℝ) → ℝ),
        memSobolevXZero w C.Xl F.V 2 P u → IsWeakJet w C.Xl F.V 2 P u D →
        (fun x => a x * u x) =ᵐ[volume.restrict (F.V : Set (Fin (n + m) → ℝ))]
          fun ξ => P₂.lpAct hF hP1 hP (weakSumSquares D []) ξ + F₂.lpAct hF hP1 hP u ξ) ∧
      (∀ u : (Fin (n + m) → ℝ) → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) u (F.V : Set (Fin (n + m) → ℝ)) →
        ∀ ξ ∈ (F.V : Set (Fin (n + m) → ℝ)),
          a ξ * u ξ = P₂.apply (sumSquares C.Xl u) ξ + F₂.apply u ξ) ∧
      (∀ α : ℝ, 0 < α → α < 1 → ∀ u : (Fin (n + m) → ℝ) → ℝ,
        memHolderXCompact w C.Xl C.dl F.V 2 α u →
        ∀ D : List (Fin k) → (Fin (n + m) → ℝ) → ℝ,
        IsHolderWeakJet w C.Xl C.dl F.V 2 α u D →
        ∀ ξ ∈ (F.V : Set (Fin (n + m) → ℝ)),
          a ξ * u ξ = P₂.apply (weakSumSquares D []) ξ + F₂.apply u ξ) := by
  obtain ⟨P₁, P₂, F₁, F₂, hk1, hk2, hk3, hk4, hF1, hF2, hadj, hzero⟩ := hParametrix hc hc0 hab
  have hXt := hF.lifted.contDiffOn_Xl
  refine ⟨P₁, P₂, F₁, F₂, hk1, hk2, hk3, hk4, hF1, hF2, hadj, hzero, ?_, ?_, ?_, ?_, ?_⟩
  · intro P _ hP1 hP g hg φ
    exact weakExtension_parametrix_adjoint hF (repSumSquaresTest F C.Xl hXt)
      (fun u => coe_repSumSquaresTest hXt u) (fun f φ => (hadj f φ).2.2) hP1 hP hg φ
  · intro α hα0 hα1 g hg hgm φ
    exact weakExtension_parametrix_adjoint_holder_noDrift hF (repSumSquaresTest F C.Xl hXt)
      (fun u => coe_repSumSquaresTest hXt u) (fun f φ => (hadj f φ).2.2) hα0 hα1 hg hgm φ
  · intro P _ hP1 hP u D hu hD
    exact weakExtension_parametrix_left_noDrift hF hw hzero hP1 hP hu hD
  · intro u hu
    exact weakExtension_parametrix_left_smooth_noDrift hF hzero hu
  · intro α hα0 hα1 u hu D hD
    exact weakExtension_parametrix_left_holder_noDrift hF hw hzero hα0 hα1 hu hD

/-- **First-order representation, without drift: representation and the three extensions.** Under the
hypotheses of `representation_firstOrder_noDrift_of`: type-1 `F_l` and endpoint type-0 `S_l` with
`X̃_l(a u) = F_l L̃u + S_l u` weakly on `V` for (i) tests `u` and (ii) smooth `u` on `V`; (iii) with the
bounded `L^P` extensions and the weak jet `D` for every `u ∈ W^{2,P}_{X̃,0}(V)`, `1 < P < ∞`; (iv) with the
pointwise actions on the Hölder jet for every compactly supported intrinsic `C^{2,α}` input (the right-hand
side is continuous and is an intrinsic derivative of `a u`). -/
theorem weakExtension_firstOrder_full_noDrift_of (hF : C.IsStandardFrame F H K hQ)
    (hw : ∀ j, (w j : ℕ) = 1) (hLeftDiff : LeftDifferentiation F w C.Xl)
    {c : (Fin (n + m) → ℝ) → ℝ} (hc : ContDiffOn ℝ (⊤ : ℕ∞) c (F.V : Set (Fin (n + m) → ℝ)))
    (hc0 : ∀ ξ ∈ (F.V : Set (Fin (n + m) → ℝ)), 0 < c ξ) (a : TestFunction F.V ℝ (⊤ : ℕ∞))
    (hParametrix : ∀ b : TestFunction F.V ℝ (⊤ : ℕ∞), SignedParametrixNoDrift F C.Xl c a b) :
    ∃ (Fl : Fin k → TypeOperator F 1) (Sl : Fin k → TypeOperator F 0),
      (∀ l, IsEndpoint F C.Xl (Sl l)) ∧
      (∀ (l : Fin k) (u : TestFunction F.V ℝ (⊤ : ℕ∞)),
        hasWeakWordDeriv C.Xl F.V [l] (fun x => a x * u x)
          (fun ξ => (Fl l).apply (sumSquares C.Xl u) ξ + (Sl l).apply u ξ)) ∧
      (∀ (l : Fin k) (u : (Fin (n + m) → ℝ) → ℝ),
        ContDiffOn ℝ (⊤ : ℕ∞) u (F.V : Set (Fin (n + m) → ℝ)) →
        hasWeakWordDeriv C.Xl F.V [l] (fun x => a x * u x)
          (fun ξ => (Fl l).apply (sumSquares C.Xl u) ξ + (Sl l).apply u ξ)) ∧
      (∀ (P : ℝ≥0∞) [Fact (1 ≤ P)] (hP1 : 1 < P) (hP : P ≠ ⊤) (u : (Fin (n + m) → ℝ) → ℝ)
          (D : List (Fin k) → (Fin (n + m) → ℝ) → ℝ),
        memSobolevXZero w C.Xl F.V 2 P u → IsWeakJet w C.Xl F.V 2 P u D → ∀ l : Fin k,
        hasWeakWordDeriv C.Xl F.V [l] (fun x => a x * u x)
          (fun ξ => (Fl l).lpAct hF hP1 hP (weakSumSquares D []) ξ +
            (Sl l).lpAct hF hP1 hP u ξ)) ∧
      (∀ α : ℝ, 0 < α → α < 1 → ∀ u : (Fin (n + m) → ℝ) → ℝ,
        memHolderXCompact w C.Xl C.dl F.V 2 α u →
        ∀ D : List (Fin k) → (Fin (n + m) → ℝ) → ℝ,
        IsHolderWeakJet w C.Xl C.dl F.V 2 α u D → ∀ l : Fin k,
        hasWeakWordDeriv C.Xl F.V [l] (fun x => a x * u x)
          (fun ξ => (Fl l).apply (weakSumSquares D []) ξ + (Sl l).apply u ξ) ∧
        ContinuousOn (fun ξ => (Fl l).apply (weakSumSquares D []) ξ + (Sl l).apply u ξ)
          (F.V : Set (Fin (n + m) → ℝ)) ∧
        hasIntrinsicWordDeriv C.Xl F.V [l] (fun x => a x * u x)
          (fun ξ => (Fl l).apply (weakSumSquares D []) ξ + (Sl l).apply u ξ)) := by
  obtain ⟨Fl, Sl, hend, hid, hext⟩ :=
    weakExtension_firstOrder_noDrift_of hF hw hLeftDiff hc hc0 a hParametrix
  refine ⟨Fl, Sl, hend, hid, fun l u hu => weakExtension_firstOrder_smooth_noDrift hF hid l hu, hext,
    fun α hα0 hα1 u hu D hD l => ?_⟩
  obtain ⟨h1, h2⟩ := weakExtension_firstOrder_holder_noDrift hF hw hid hα0 hα1 hu hD l
  exact ⟨h1, h2, weakExtension_firstOrder_intrinsic_noDrift hF hw hid hα0 hα1 hu hD l⟩

/-- **Second-order representation, without drift: representation and the three extensions** (as for
`weakExtension_firstOrder_full_noDrift_of`, under the hypotheses of `representation_secondOrder_noDrift_of`;
the Hölder case gives the weak identity and continuity of the right-hand side). -/
theorem weakExtension_secondOrder_full_noDrift_of (hF : C.IsStandardFrame F H K hQ)
    (hw : ∀ j, (w j : ℕ) = 1) (B : Fin (n + m) → List (Fin k)) (hRowInt : TypeKernelIntegrable F)
    (hLeftDiff : LeftDifferentiation F w C.Xl) (hRightDiff : RightDifferentiation F w C.Xl hF.lifted.contDiffOn_Xl)
    (hTransfer : DerivativeTransfer F w C.Xl B)
    {c : (Fin (n + m) → ℝ) → ℝ} (hc : ContDiffOn ℝ (⊤ : ℕ∞) c (F.V : Set (Fin (n + m) → ℝ)))
    (hc0 : ∀ ξ ∈ (F.V : Set (Fin (n + m) → ℝ)), 0 < c ξ) (a : TestFunction F.V ℝ (⊤ : ℕ∞))
    (hParametrix : ∀ b : TestFunction F.V ℝ (⊤ : ℕ∞), SignedParametrixNoDrift F C.Xl c a b) :
    ∃ (Sml : Fin k → Fin k → TypeOperator F 0)
      (Smlk : Fin k → Fin k → Fin k → TypeOperator F 0)
      (Sml0 : Fin k → Fin k → TypeOperator F 0),
      (∀ i l, IsEndpoint F C.Xl (Sml i l)) ∧ (∀ i l j, IsEndpoint F C.Xl (Smlk i l j)) ∧
      (∀ i l, IsEndpoint F C.Xl (Sml0 i l)) ∧
      (∀ (i l : Fin k) (u : TestFunction F.V ℝ (⊤ : ℕ∞)),
        hasWeakWordDeriv C.Xl F.V [i, l] (fun x => a x * u x)
          (fun ξ => (Sml i l).apply (sumSquares C.Xl u) ξ +
            (∑ j : Fin k, (Smlk i l j).apply
              (fieldDerivative (C.Xl j) (u : (Fin (n + m) → ℝ) → ℝ)) ξ) +
            (Sml0 i l).apply u ξ)) ∧
      (∀ (i l : Fin k) (u : (Fin (n + m) → ℝ) → ℝ),
        ContDiffOn ℝ (⊤ : ℕ∞) u (F.V : Set (Fin (n + m) → ℝ)) →
        hasWeakWordDeriv C.Xl F.V [i, l] (fun x => a x * u x)
          (fun ξ => (Sml i l).apply (sumSquares C.Xl u) ξ +
            (∑ j : Fin k, (Smlk i l j).apply
              (fieldDerivative (C.Xl j) (u : (Fin (n + m) → ℝ) → ℝ)) ξ) +
            (Sml0 i l).apply u ξ)) ∧
      (∀ (P : ℝ≥0∞) [Fact (1 ≤ P)] (hP1 : 1 < P) (hP : P ≠ ⊤) (u : (Fin (n + m) → ℝ) → ℝ)
          (D : List (Fin k) → (Fin (n + m) → ℝ) → ℝ),
        memSobolevXZero w C.Xl F.V 2 P u → IsWeakJet w C.Xl F.V 2 P u D → ∀ i l : Fin k,
        hasWeakWordDeriv C.Xl F.V [i, l] (fun x => a x * u x)
          (fun ξ => (Sml i l).lpAct hF hP1 hP (weakSumSquares D []) ξ +
            (∑ j : Fin k, (Smlk i l j).lpAct hF hP1 hP (D [j]) ξ) +
            (Sml0 i l).lpAct hF hP1 hP u ξ)) ∧
      (∀ α : ℝ, 0 < α → α < 1 → ∀ u : (Fin (n + m) → ℝ) → ℝ,
        memHolderXCompact w C.Xl C.dl F.V 2 α u →
        ∀ D : List (Fin k) → (Fin (n + m) → ℝ) → ℝ,
        IsHolderWeakJet w C.Xl C.dl F.V 2 α u D → ∀ i l : Fin k,
        hasWeakWordDeriv C.Xl F.V [i, l] (fun x => a x * u x)
          (fun ξ => (Sml i l).apply (weakSumSquares D []) ξ +
            (∑ j : Fin k, (Smlk i l j).apply (D [j]) ξ) + (Sml0 i l).apply u ξ) ∧
        ContinuousOn (fun ξ => (Sml i l).apply (weakSumSquares D []) ξ +
            (∑ j : Fin k, (Smlk i l j).apply (D [j]) ξ) + (Sml0 i l).apply u ξ)
          (F.V : Set (Fin (n + m) → ℝ))) := by
  obtain ⟨Sml, Smlk, Sml0, h1, h2, h3, hid, hext⟩ :=
    weakExtension_secondOrder_noDrift_of hF hw B hRowInt hLeftDiff hRightDiff hTransfer hc hc0 a hParametrix
  exact ⟨Sml, Smlk, Sml0, h1, h2, h3, hid,
    fun i l u hu => weakExtension_secondOrder_smooth_noDrift hF hid i l hu, hext,
    fun α hα0 hα1 u hu D hD i l =>
      weakExtension_secondOrder_holder_noDrift hF hw hid hα0 hα1 hu hD i l⟩

end LiftedChart

end RothschildStein.P1
