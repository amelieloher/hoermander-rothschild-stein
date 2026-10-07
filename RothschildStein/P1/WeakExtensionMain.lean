-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.WeakExtensionSmooth
public import RothschildStein.P1.WeakExtensionHolderMore

/-!
# Weak extension of the parametrix and representation identities, assembled

One declaration per identity, conditional exactly on the hypotheses of the parametrix and representation theorems
(`SignedParametrix` resp. `SignedParametrixNoDrift`, `TypeKernelIntegrable`, `LeftDifferentiation`, `RightDifferentiation`, `DerivativeTransfer`, the
density data of `SignedParametrix`), returning the operators of the representations together with

* the identity on tests (as in `representation_*_of`);
* its extension to `u ∈ W^{m,p}_{X̃,0}(V)`, `1 < p < ∞` (`m = 2`, resp. `m = |I|`): weak identity with the
  bounded `L^p` extensions of the continuity theorem applied to the weak jet;
* its validity for smooth noncompact inputs `u ∈ C^∞(V)` (cutoff equal to one near every input support);
* its validity for compactly supported intrinsic `C^{m,α}` inputs, `0 < α < 1`, for any
  `(HD1)`-`(HD2)` package `S.DistanceGeometry` of the lifted control distance on a domain `⊇ V`:
  weak identity with the pointwise integral/PV actions on the Hölder jet, continuity of the
  right-hand side, and (first order and drift) the intrinsic form.

None of this regularizes an arbitrary distribution; every input is in the closure of the tests, smooth, or
compactly supported intrinsic Hölder.
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

/-- **The signed parametrix identities and their extensions.** For the cutoffs
`a, b ∈ C_c^∞(V)`, `a b = a`, and `SignedParametrix` (BB Thm 11.25): the conclusion of `SignedParametrix` for operators
`P₁, P₂, F₁, F₂`, and for these operators

* the distributional identity `M_a = L̃* P₁ + F₁` for every `g ∈ L^P(V)` (`1 < P < ∞`, bounded extensions) and,
  with the pointwise actions, for every measurable `g` of finite Hölder norm;
* `a u = P₂ L̃u + F₂ u`: a.e. on `V` for every `u ∈ W^{2,P}_{X̃,0}(V)` (weak `L̃u`), at every point of `V` for
  smooth `u` on `V` and for every compactly supported intrinsic `C^{2,α}` input. -/
theorem weakExtension_parametrix_full_of (hF : C.IsStandardFrame F H K hQ)
    (hw0 : (w 0 : ℕ) = 2) (hw : ∀ j : Fin q, (w j.succ : ℕ) = 1)
    {c : (Fin (n + m) → ℝ) → ℝ} (hc : ContDiffOn ℝ (⊤ : ℕ∞) c (F.V : Set (Fin (n + m) → ℝ)))
    (hc0 : ∀ ξ ∈ (F.V : Set (Fin (n + m) → ℝ)), 0 < c ξ) (a b : TestFunction F.V ℝ (⊤ : ℕ∞))
    (hab : ∀ ξ, a ξ * b ξ = a ξ) (hParametrix : SignedParametrix F C.Xl c a b) :
    ∃ (P₁ P₂ : TypeOperator F 2) (F₁ F₂ : TypeOperator F 1),
      (∀ ξ η, ξ ≠ η → P₁.kernel ξ η = a ξ * F.Γs (F.Θ η ξ) * (b η / c η)) ∧
      (∀ ξ η, ξ ≠ η → P₂.kernel ξ η = b ξ / c ξ * (a η * F.Γ (F.Θ η ξ))) ∧
      (∀ ξ η, ξ ≠ η → P₂.kernel ξ η = P₁.kernel η ξ) ∧
      (∀ ξ η, ξ ≠ η → F₂.kernel ξ η = F₁.kernel η ξ) ∧
      IsTypeKernelOn F true 1 F₁.kernel ∧ IsTypeKernelOn F false 1 F₂.kernel ∧
      (∀ f φ : TestFunction F.V ℝ (⊤ : ℕ∞),
        IntegrableOn (fun ξ => P₁.apply f ξ * sumSquaresWithDrift C.Xl φ ξ)
          (F.V : Set (Fin (n + m) → ℝ)) ∧
        IntegrableOn (fun ξ => F₁.apply f ξ * φ ξ) (F.V : Set (Fin (n + m) → ℝ)) ∧
        (∫ ξ in (F.V : Set (Fin (n + m) → ℝ)), P₁.apply f ξ * sumSquaresWithDrift C.Xl φ ξ) =
          (∫ ξ in (F.V : Set (Fin (n + m) → ℝ)), a ξ * f ξ * φ ξ) -
            ∫ ξ in (F.V : Set (Fin (n + m) → ℝ)), F₁.apply f ξ * φ ξ) ∧
      (∀ f : TestFunction F.V ℝ (⊤ : ℕ∞), ∀ ξ ∈ (F.V : Set (Fin (n + m) → ℝ)),
        a ξ * f ξ = P₂.apply (sumSquaresWithDrift C.Xl f) ξ + F₂.apply f ξ) ∧
      (∀ (P : ℝ≥0∞) [Fact (1 ≤ P)] (hP1 : 1 < P) (hP : P ≠ ⊤) (g : (Fin (n + m) → ℝ) → ℝ),
        MemLp g P (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) →
        ∀ φ : TestFunction F.V ℝ (⊤ : ℕ∞),
          (∫ ξ in (F.V : Set (Fin (n + m) → ℝ)),
              P₁.lpAct hF hP1 hP g ξ * sumSquaresWithDrift C.Xl φ ξ) =
            (∫ ξ in (F.V : Set (Fin (n + m) → ℝ)), a ξ * g ξ * φ ξ) -
              ∫ ξ in (F.V : Set (Fin (n + m) → ℝ)), F₁.lpAct hF hP1 hP g ξ * φ ξ) ∧
      (∀ α : ℝ, 0 < α → α < 1 → ∀ g : (Fin (n + m) → ℝ) → ℝ,
        holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) g ≠ ⊤ →
        AEStronglyMeasurable g (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) →
        ∀ φ : TestFunction F.V ℝ (⊤ : ℕ∞),
          (∫ ξ in (F.V : Set (Fin (n + m) → ℝ)), P₁.apply g ξ * sumSquaresWithDrift C.Xl φ ξ) =
            (∫ ξ in (F.V : Set (Fin (n + m) → ℝ)), a ξ * g ξ * φ ξ) -
              ∫ ξ in (F.V : Set (Fin (n + m) → ℝ)), F₁.apply g ξ * φ ξ) ∧
      (∀ (P : ℝ≥0∞) [Fact (1 ≤ P)] (hP1 : 1 < P) (hP : P ≠ ⊤) (u : (Fin (n + m) → ℝ) → ℝ)
          (D : List (Fin (q + 1)) → (Fin (n + m) → ℝ) → ℝ),
        memSobolevXZero w C.Xl F.V 2 P u → IsWeakJet w C.Xl F.V 2 P u D →
        (fun x => a x * u x) =ᵐ[volume.restrict (F.V : Set (Fin (n + m) → ℝ))]
          fun ξ => P₂.lpAct hF hP1 hP (weakSumSquaresWithDrift D) ξ + F₂.lpAct hF hP1 hP u ξ) ∧
      (∀ u : (Fin (n + m) → ℝ) → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) u (F.V : Set (Fin (n + m) → ℝ)) →
        ∀ ξ ∈ (F.V : Set (Fin (n + m) → ℝ)),
          a ξ * u ξ = P₂.apply (sumSquaresWithDrift C.Xl u) ξ + F₂.apply u ξ) ∧
      (∀ (Ω₂ : Opens (Fin (n + m) → ℝ)) (G : S.DistanceGeometry Ω₂), G.d = C.dl →
        (F.V : Set (Fin (n + m) → ℝ)) ⊆ (Ω₂ : Set (Fin (n + m) → ℝ)) →
        ∀ α : ℝ, 0 < α → α < 1 → ∀ u : (Fin (n + m) → ℝ) → ℝ,
        memHolderXCompact w C.Xl C.dl F.V 2 α u →
        ∀ D : List (Fin (q + 1)) → (Fin (n + m) → ℝ) → ℝ,
        IsHolderWeakJet w C.Xl C.dl F.V 2 α u D →
        ∀ ξ ∈ (F.V : Set (Fin (n + m) → ℝ)),
          a ξ * u ξ = P₂.apply (weakSumSquaresWithDrift D) ξ + F₂.apply u ξ) := by
  obtain ⟨P₁, P₂, F₁, F₂, hk1, hk2, hk3, hk4, hF1, hF2, hadj, hzero⟩ := hParametrix hc hc0 hab
  have hXt := hF.lifted.contDiffOn_Xl
  refine ⟨P₁, P₂, F₁, F₂, hk1, hk2, hk3, hk4, hF1, hF2, hadj, hzero, ?_, ?_, ?_, ?_, ?_⟩
  · intro P _ hP1 hP g hg φ
    exact weakExtension_parametrix_adjoint hF (sumSquaresWithDriftTest F.V C.Xl hXt)
      (fun u => sumSquaresWithDriftTest_coe F.V C.Xl hXt u) (fun f φ => (hadj f φ).2.2) hP1 hP hg φ
  · intro α hα0 hα1 g hg hgm φ
    exact weakExtension_parametrix_adjoint_holder hF (sumSquaresWithDriftTest F.V C.Xl hXt)
      (fun u => sumSquaresWithDriftTest_coe F.V C.Xl hXt u) (fun f φ => (hadj f φ).2.2) hα0 hα1 hg
      hgm φ
  · intro P _ hP1 hP u D hu hD
    exact weakExtension_parametrix_left_drift hF hw0 hw hzero hP1 hP hu hD
  · intro u hu
    exact weakExtension_parametrix_left_smooth hF hzero hu
  · intro Ω₂ G hG hV α hα0 hα1 u hu D hD
    exact weakExtension_parametrix_left_holder hF hw0 hw hzero Ω₂ G hG hV hα0 hα1 hu hD

/-- **First-order representation: representation and the three extensions.** Under the hypotheses of
`representation_firstOrder_of`: type-1 `F_l` and endpoint type-0 `S_l` with
`X̃_l(a u) = F_l L̃u + S_l u` weakly on `V` for (i) tests `u` and (ii) smooth `u` on `V`; (iii) with the bounded
`L^P` extensions and the weak jet `D` for every `u ∈ W^{2,P}_{X̃,0}(V)`, `1 < P < ∞`; (iv) with the
pointwise actions on the Hölder jet for every compactly supported intrinsic `C^{2,α}` input (the
right-hand side is continuous and is an intrinsic derivative of `a u`). -/
theorem weakExtension_firstOrder_full_of (hF : C.IsStandardFrame F H K hQ)
    (hw0 : (w 0 : ℕ) = 2) (hw : ∀ j : Fin q, (w j.succ : ℕ) = 1) (hLeftDiff : LeftDifferentiation F w C.Xl)
    {c : (Fin (n + m) → ℝ) → ℝ} (hc : ContDiffOn ℝ (⊤ : ℕ∞) c (F.V : Set (Fin (n + m) → ℝ)))
    (hc0 : ∀ ξ ∈ (F.V : Set (Fin (n + m) → ℝ)), 0 < c ξ) (a : TestFunction F.V ℝ (⊤ : ℕ∞))
    (hParametrix : ∀ b : TestFunction F.V ℝ (⊤ : ℕ∞), SignedParametrix F C.Xl c a b) :
    ∃ (Fl : Fin q → TypeOperator F 1) (Sl : Fin q → TypeOperator F 0),
      (∀ l, IsEndpoint F C.Xl (Sl l)) ∧
      (∀ (l : Fin q) (u : TestFunction F.V ℝ (⊤ : ℕ∞)),
        hasWeakWordDeriv C.Xl F.V [l.succ] (fun x => a x * u x)
          (fun ξ => (Fl l).apply (sumSquaresWithDrift C.Xl u) ξ + (Sl l).apply u ξ)) ∧
      (∀ (l : Fin q) (u : (Fin (n + m) → ℝ) → ℝ),
        ContDiffOn ℝ (⊤ : ℕ∞) u (F.V : Set (Fin (n + m) → ℝ)) →
        hasWeakWordDeriv C.Xl F.V [l.succ] (fun x => a x * u x)
          (fun ξ => (Fl l).apply (sumSquaresWithDrift C.Xl u) ξ + (Sl l).apply u ξ)) ∧
      (∀ (P : ℝ≥0∞) [Fact (1 ≤ P)] (hP1 : 1 < P) (hP : P ≠ ⊤) (u : (Fin (n + m) → ℝ) → ℝ)
          (D : List (Fin (q + 1)) → (Fin (n + m) → ℝ) → ℝ),
        memSobolevXZero w C.Xl F.V 2 P u → IsWeakJet w C.Xl F.V 2 P u D → ∀ l : Fin q,
        hasWeakWordDeriv C.Xl F.V [l.succ] (fun x => a x * u x)
          (fun ξ => (Fl l).lpAct hF hP1 hP (weakSumSquaresWithDrift D) ξ +
            (Sl l).lpAct hF hP1 hP u ξ)) ∧
      (∀ (Ω₂ : Opens (Fin (n + m) → ℝ)) (G : S.DistanceGeometry Ω₂), G.d = C.dl →
        (F.V : Set (Fin (n + m) → ℝ)) ⊆ (Ω₂ : Set (Fin (n + m) → ℝ)) →
        ∀ α : ℝ, 0 < α → α < 1 → ∀ u : (Fin (n + m) → ℝ) → ℝ,
        memHolderXCompact w C.Xl C.dl F.V 2 α u →
        ∀ D : List (Fin (q + 1)) → (Fin (n + m) → ℝ) → ℝ,
        IsHolderWeakJet w C.Xl C.dl F.V 2 α u D → ∀ l : Fin q,
        hasWeakWordDeriv C.Xl F.V [l.succ] (fun x => a x * u x)
          (fun ξ => (Fl l).apply (weakSumSquaresWithDrift D) ξ + (Sl l).apply u ξ) ∧
        ContinuousOn (fun ξ => (Fl l).apply (weakSumSquaresWithDrift D) ξ + (Sl l).apply u ξ)
          (F.V : Set (Fin (n + m) → ℝ)) ∧
        hasIntrinsicWordDeriv C.Xl F.V [l.succ] (fun x => a x * u x)
          (fun ξ => (Fl l).apply (weakSumSquaresWithDrift D) ξ + (Sl l).apply u ξ)) := by
  obtain ⟨Fl, Sl, hend, hid, hext⟩ :=
    weakExtension_firstOrder_of hF hw0 hw hLeftDiff hc hc0 a hParametrix
  refine ⟨Fl, Sl, hend, hid, fun l u hu => weakExtension_firstOrder_smooth hF hid l hu, hext,
    fun Ω₂ G hG hV α hα0 hα1 u hu D hD l => ?_⟩
  obtain ⟨h1, h2⟩ := weakExtension_firstOrder_holder hF hw0 hw hid Ω₂ G hG hV hα0 hα1 hu hD l
  exact ⟨h1, h2, weakExtension_firstOrder_intrinsic hF hw0 hw hid Ω₂ G hG hV hα0 hα1 hu hD l⟩

/-- **Second-order representation: representation and the three extensions** (as for
`weakExtension_firstOrder_full_of`, under the hypotheses of `representation_secondOrder_of`; the Hölder
case gives the weak identity and continuity of the right-hand side). -/
theorem weakExtension_secondOrder_full_of (hF : C.IsStandardFrame F H K hQ)
    (hw0 : (w 0 : ℕ) = 2) (hw : ∀ j : Fin q, (w j.succ : ℕ) = 1)
    (B : Fin (n + m) → List (Fin (q + 1))) (hRowInt : TypeKernelIntegrable F) (hLeftDiff : LeftDifferentiation F w C.Xl)
    (hRightDiff : RightDifferentiation F w C.Xl hF.lifted.contDiffOn_Xl) (hTransfer : DerivativeTransfer F w C.Xl B)
    {c : (Fin (n + m) → ℝ) → ℝ} (hc : ContDiffOn ℝ (⊤ : ℕ∞) c (F.V : Set (Fin (n + m) → ℝ)))
    (hc0 : ∀ ξ ∈ (F.V : Set (Fin (n + m) → ℝ)), 0 < c ξ) (a : TestFunction F.V ℝ (⊤ : ℕ∞))
    (hParametrix : ∀ b : TestFunction F.V ℝ (⊤ : ℕ∞), SignedParametrix F C.Xl c a b) :
    ∃ (Sml : Fin q → Fin q → TypeOperator F 0)
      (Smlk : Fin q → Fin q → Fin q → TypeOperator F 0)
      (Sml0 : Fin q → Fin q → TypeOperator F 0),
      (∀ i l, IsEndpoint F C.Xl (Sml i l)) ∧ (∀ i l k, IsEndpoint F C.Xl (Smlk i l k)) ∧
      (∀ i l, IsEndpoint F C.Xl (Sml0 i l)) ∧
      (∀ (i l : Fin q) (u : TestFunction F.V ℝ (⊤ : ℕ∞)),
        hasWeakWordDeriv C.Xl F.V [i.succ, l.succ] (fun x => a x * u x)
          (fun ξ => (Sml i l).apply (sumSquaresWithDrift C.Xl u) ξ +
            (∑ k : Fin q, (Smlk i l k).apply
              (fieldDerivative (C.Xl k.succ) (u : (Fin (n + m) → ℝ) → ℝ)) ξ) +
            (Sml0 i l).apply u ξ)) ∧
      (∀ (i l : Fin q) (u : (Fin (n + m) → ℝ) → ℝ),
        ContDiffOn ℝ (⊤ : ℕ∞) u (F.V : Set (Fin (n + m) → ℝ)) →
        hasWeakWordDeriv C.Xl F.V [i.succ, l.succ] (fun x => a x * u x)
          (fun ξ => (Sml i l).apply (sumSquaresWithDrift C.Xl u) ξ +
            (∑ k : Fin q, (Smlk i l k).apply
              (fieldDerivative (C.Xl k.succ) (u : (Fin (n + m) → ℝ) → ℝ)) ξ) +
            (Sml0 i l).apply u ξ)) ∧
      (∀ (P : ℝ≥0∞) [Fact (1 ≤ P)] (hP1 : 1 < P) (hP : P ≠ ⊤) (u : (Fin (n + m) → ℝ) → ℝ)
          (D : List (Fin (q + 1)) → (Fin (n + m) → ℝ) → ℝ),
        memSobolevXZero w C.Xl F.V 2 P u → IsWeakJet w C.Xl F.V 2 P u D → ∀ i l : Fin q,
        hasWeakWordDeriv C.Xl F.V [i.succ, l.succ] (fun x => a x * u x)
          (fun ξ => (Sml i l).lpAct hF hP1 hP (weakSumSquaresWithDrift D) ξ +
            (∑ k : Fin q, (Smlk i l k).lpAct hF hP1 hP (D [k.succ]) ξ) +
            (Sml0 i l).lpAct hF hP1 hP u ξ)) ∧
      (∀ (Ω₂ : Opens (Fin (n + m) → ℝ)) (G : S.DistanceGeometry Ω₂), G.d = C.dl →
        (F.V : Set (Fin (n + m) → ℝ)) ⊆ (Ω₂ : Set (Fin (n + m) → ℝ)) →
        ∀ α : ℝ, 0 < α → α < 1 → ∀ u : (Fin (n + m) → ℝ) → ℝ,
        memHolderXCompact w C.Xl C.dl F.V 2 α u →
        ∀ D : List (Fin (q + 1)) → (Fin (n + m) → ℝ) → ℝ,
        IsHolderWeakJet w C.Xl C.dl F.V 2 α u D → ∀ i l : Fin q,
        hasWeakWordDeriv C.Xl F.V [i.succ, l.succ] (fun x => a x * u x)
          (fun ξ => (Sml i l).apply (weakSumSquaresWithDrift D) ξ +
            (∑ k : Fin q, (Smlk i l k).apply (D [k.succ]) ξ) + (Sml0 i l).apply u ξ) ∧
        ContinuousOn (fun ξ => (Sml i l).apply (weakSumSquaresWithDrift D) ξ +
            (∑ k : Fin q, (Smlk i l k).apply (D [k.succ]) ξ) + (Sml0 i l).apply u ξ)
          (F.V : Set (Fin (n + m) → ℝ))) := by
  obtain ⟨Sml, Smlk, Sml0, h1, h2, h3, hid, hext⟩ :=
    weakExtension_secondOrder_of hF hw0 hw B hRowInt hLeftDiff hRightDiff hTransfer hc hc0 a hParametrix
  exact ⟨Sml, Smlk, Sml0, h1, h2, h3, hid,
    fun i l u hu => weakExtension_secondOrder_smooth hF hid i l hu, hext,
    fun Ω₂ G hG hV α hα0 hα1 u hu D hD i l =>
      weakExtension_secondOrder_holder hF hw0 hw hid Ω₂ G hG hV hα0 hα1 hu hD i l⟩

end LiftedChart

namespace LiftedChart

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {F : KernelFrame (n + m)}
  {r : ℕ} {H : H1.StandingHypotheses C.G r} {K : H1.FundamentalKernel C.G H}
  {hQ : 2 < (C.G.homogeneousDimension : ℝ)}

/-- **Higher-order representation without drift: representation and the three extensions.** Under the hypotheses of
`representation_higher_noDrift_of` (all weights one), for every word `I` of length `m ≥ 2`, the endpoint
type-0 families `S_IJ, T_IK` satisfy `X̃_I(a u) = ∑_J S_IJ X̃_J L̃u + ∑_K T_IK X̃_K u` weakly on `V` for
(i) tests, (ii) smooth `u` on `V`, (iii) every `u ∈ W^{m,P}_{X̃,0}(V)`, `1 < P < ∞` (bounded `L^P` extensions
on the weak jet), (iv) every compactly supported intrinsic `C^{m,α}` input (pointwise actions on the Hölder
jet; the right-hand side is continuous on `V`). There is no higher formula with drift. -/
theorem weakExtension_higher_full_of (hF : C.IsStandardFrame F H K hQ) (hw : ∀ j, (w j : ℕ) = 1)
    (B : Fin (n + m) → List (Fin k)) (hRowInt : TypeKernelIntegrable F) (hLeftDiff : LeftDifferentiation F w C.Xl)
    (hRightDiff : RightDifferentiation F w C.Xl hF.lifted.contDiffOn_Xl) (hTransfer : DerivativeTransfer F w C.Xl B)
    {c : (Fin (n + m) → ℝ) → ℝ} (hc : ContDiffOn ℝ (⊤ : ℕ∞) c (F.V : Set (Fin (n + m) → ℝ)))
    (hc0 : ∀ ξ ∈ (F.V : Set (Fin (n + m) → ℝ)), 0 < c ξ) (a : TestFunction F.V ℝ (⊤ : ℕ∞))
    (hParametrix : ∀ b : TestFunction F.V ℝ (⊤ : ℕ∞), SignedParametrixNoDrift F C.Xl c a b)
    (I : List (Fin k)) (hI : 2 ≤ I.length) :
    ∃ Sf Tf : List (Fin k) → TypeOperator F 0,
      (∀ J, IsEndpoint F C.Xl (Sf J)) ∧ (∀ K, IsEndpoint F C.Xl (Tf K)) ∧
      (∀ u : TestFunction F.V ℝ (⊤ : ℕ∞),
        hasWeakWordDeriv C.Xl F.V I (fun x => a x * u x)
          (fun ξ => (∑ J ∈ repWords k (I.length - 2),
              (Sf J).apply (wordDerivative C.Xl J (sumSquares C.Xl (u : (Fin (n + m) → ℝ) → ℝ))) ξ) +
            ∑ K ∈ repWords k (I.length - 1),
              (Tf K).apply (wordDerivative C.Xl K (u : (Fin (n + m) → ℝ) → ℝ)) ξ)) ∧
      (∀ u : (Fin (n + m) → ℝ) → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) u (F.V : Set (Fin (n + m) → ℝ)) →
        hasWeakWordDeriv C.Xl F.V I (fun x => a x * u x)
          (fun ξ => (∑ J ∈ repWords k (I.length - 2),
              (Sf J).apply (wordDerivative C.Xl J (sumSquares C.Xl u)) ξ) +
            ∑ K ∈ repWords k (I.length - 1), (Tf K).apply (wordDerivative C.Xl K u) ξ)) ∧
      (∀ (P : ℝ≥0∞) [Fact (1 ≤ P)] (hP1 : 1 < P) (hP : P ≠ ⊤) (u : (Fin (n + m) → ℝ) → ℝ)
          (D : List (Fin k) → (Fin (n + m) → ℝ) → ℝ),
        memSobolevXZero w C.Xl F.V I.length P u → IsWeakJet w C.Xl F.V I.length P u D →
        hasWeakWordDeriv C.Xl F.V I (fun x => a x * u x)
          (fun ξ => (∑ J ∈ repWords k (I.length - 2),
              (Sf J).lpAct hF hP1 hP (weakSumSquares D J) ξ) +
            ∑ K ∈ repWords k (I.length - 1), (Tf K).lpAct hF hP1 hP (D K) ξ)) ∧
      (∀ (Ω₂ : Opens (Fin (n + m) → ℝ)) (G : S.DistanceGeometry Ω₂), G.d = C.dl →
        (F.V : Set (Fin (n + m) → ℝ)) ⊆ (Ω₂ : Set (Fin (n + m) → ℝ)) →
        ∀ α : ℝ, 0 < α → α < 1 → ∀ u : (Fin (n + m) → ℝ) → ℝ,
        memHolderXCompact w C.Xl C.dl F.V I.length α u →
        ∀ D : List (Fin k) → (Fin (n + m) → ℝ) → ℝ,
        IsHolderWeakJet w C.Xl C.dl F.V I.length α u D →
        hasWeakWordDeriv C.Xl F.V I (fun x => a x * u x)
          (fun ξ => (∑ J ∈ repWords k (I.length - 2), (Sf J).apply (weakSumSquares D J) ξ) +
            ∑ K ∈ repWords k (I.length - 1), (Tf K).apply (D K) ξ) ∧
        ContinuousOn (fun ξ => (∑ J ∈ repWords k (I.length - 2),
              (Sf J).apply (weakSumSquares D J) ξ) +
            ∑ K ∈ repWords k (I.length - 1), (Tf K).apply (D K) ξ) (F.V : Set (Fin (n + m) → ℝ))) := by
  obtain ⟨Sf, Tf, hS, hT, hid, hext⟩ :=
    weakExtension_higher_of hF hw B hRowInt hLeftDiff hRightDiff hTransfer hc hc0 a hParametrix I hI
  exact ⟨Sf, Tf, hS, hT, hid, fun u hu => weakExtension_higher_smooth hF I hid hu, hext,
    fun Ω₂ G hG hV α hα0 hα1 u hu D hD =>
      weakExtension_higher_holder hF hw I hI hid Ω₂ G hG hV hα0 hα1 hu hD⟩

end LiftedChart

end RothschildStein.P1
