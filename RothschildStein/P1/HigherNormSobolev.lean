-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.HigherNormOperators
public import RothschildStein.S.CompactSobolevZero
public import RothschildStein.S.SobolevZeroAE

/-!
# Higher-order gain, Sobolev part: `‖S f‖_{W^{k,p}_{X̃}(V)} ≤ C ‖f‖_{W^{k,p}_{X̃}(V)}`

Without drift (all weights one) let `S = ∑ⱼ X̃ⱼ Fⱼ` with `Fⱼ` of type `1`, so that `S f = ∑ⱼ Tⱼ f` with
`Tⱼ` of type `0` and `Tⱼ g = X̃ⱼ (Fⱼ g)` weakly on `V` for tests `g` (such `Tⱼ` exist by `LeftDifferentiation`,
`exists_typeZero_weakDeriv`; the action of `S` on tests, hence its bounded `L^p` extension, depends
only on the `Fⱼ`). BB pp. 567–568, Prop. 11.31. All statements assume the type-calculus hypotheses
`TypeKernelIntegrable`, `LeftDifferentiation`, `RightDifferentiation` and `DerivativeTransfer`, and use the standard frame of a lifted
chart (`LiftedChart.IsStandardFrame`).

What is proved, for every `k ≥ 0` and `1 < p < ∞`:

* `noDrift_sobolev_lp_of_transfer`: there is `C` (depending on the finite commuted family
  `𝒟_{S,k}` of `X̃_I`-commuted type-0 operators, `k`, `p`) such that every bounded operator `S̄` on
  `L^p(V)` that agrees with `S` on tests, such as the unique bounded extension supplied by
  `TypeOperator.exists_listExtension_standard`, maps `f ∈ L^p(V) ∩ W^{k,p}_{X̃,0}(V)` into `W^{k,p}_{X̃}(V)` with
  `‖S̄ f‖_{W^{k,p}} ≤ C ‖f‖_{W^{k,p}}`; the weak derivatives `X̃_I (S̄ f) = ∑_{|J| ≤ |I|} S̄_{I,J}(X̃_J f)`
  are identified by `hasWeakWordDeriv_family_extension` (approximation by tests in the closure space `W_0` and closedness of the weak-derivative graph);
* `noDrift_sobolev_tests_of_transfer`: the bound on tests `f ∈ C_c^∞(V)`, with `S f` the pointwise
  action `∑ⱼ Tⱼ f` (a test lies in `W_0`);
* `noDrift_sobolev_compact_support_of_transfer`: the bound for every `f ∈ W^{k,p}_{X̃}(V)` with
  compact support in `V` (by BB Cor 2.10 such an `f` lies in `W_0`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped ENNReal Topology
namespace RothschildStein.P1

section Tests

variable {N k : ℕ} {w : Fin k → ℕ+} {Xt : Fin k → (Fin N → ℝ) → (Fin N → ℝ)}
  {V : Opens (Fin N → ℝ)}

end Tests

namespace LiftedChart

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {F : KernelFrame (n + m)}
  {q : ℕ} {H : H1.StandingHypotheses C.G q} {K : H1.FundamentalKernel C.G H}
  {hQ : 2 < (C.G.homogeneousDimension : ℝ)}

/-- **Sobolev bound for endpoint commutators without drift** (BB pp. 567–568,
Prop. 11.31). Assume `TypeKernelIntegrable`, `LeftDifferentiation`, `RightDifferentiation` and `DerivativeTransfer`. Let `Fⱼ` be
type-1 operators and `Tⱼ` type-0 operators with `Tⱼ g = X̃ⱼ (Fⱼ g)` weakly on
`V` for every test `g` (`S = ∑ⱼ X̃ⱼ Fⱼ`, `S g = ∑ⱼ Tⱼ g`). For every `k ≥ 0` and `1 < P < ∞` there is `C`
with the following property. Every bounded operator `S̄` on `L^P(V)` that agrees with `S` on tests maps
every `f ∈ L^P(V)` that lies in the closure space `W^{k,P}_{X̃,0}(V)` (`memSobolevXZero`) into
`W^{k,P}_{X̃}(V)` (`memSobolevX`) with `‖S̄ f‖_{W^{k,P}_{X̃}(V)} ≤ C ‖f‖_{W^{k,P}_{X̃}(V)}`
(`sobolevXENorm`). -/
theorem noDrift_sobolev_lp_of_transfer (hF : C.IsStandardFrame F H K hQ)
    (hw : ∀ j, (w j : ℕ) = 1) (B : Fin (n + m) → List (Fin k)) (hRowInt : TypeKernelIntegrable F)
    (hLeftDiff : LeftDifferentiation F w C.Xl) (hRightDiff : RightDifferentiation F w C.Xl hF.lifted.contDiffOn_Xl)
    (hTransfer : DerivativeTransfer F w C.Xl B) (Fj : Fin k → TypeOperator F 1) (Tj : Fin k → TypeOperator F 0)
    (hT : ∀ (j : Fin k) (g : TestFunction F.V ℝ (⊤ : ℕ∞)),
      hasWeakWordDeriv C.Xl F.V [j] ((Fj j).apply (g : (Fin (n + m) → ℝ) → ℝ))
        ((Tj j).apply (g : (Fin (n + m) → ℝ) → ℝ)))
    (kk : ℕ) {P : ℝ≥0∞} [Fact (1 ≤ P)] (hP1 : 1 < P) (hP : P ≠ ⊤) :
    ∃ Cg : ℝ, 0 < Cg ∧
      ∀ Sb : Lp ℝ P (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) →L[ℝ]
          Lp ℝ P (volume.restrict (F.V : Set (Fin (n + m) → ℝ))),
        (∀ φ : TestFunction F.V ℝ (⊤ : ℕ∞),
          Sb (testToLp F.V hF.lifted.volume_lt_top P φ) =ᵐ[volume.restrict
            (F.V : Set (Fin (n + m) → ℝ))]
            fun ξ => ∑ j, (Tj j).apply (φ : (Fin (n + m) → ℝ) → ℝ) ξ) →
        ∀ f : Lp ℝ P (volume.restrict (F.V : Set (Fin (n + m) → ℝ))),
          memSobolevXZero w C.Xl F.V kk P (⇑f) →
          memSobolevX w C.Xl F.V kk P (⇑(Sb f)) ∧
            sobolevXENorm w C.Xl F.V kk P (⇑(Sb f)) ≤
              ENNReal.ofReal Cg * sobolevXENorm w C.Xl F.V kk P (⇑f) := by
  have hXt := hF.lifted.contDiffOn_Xl
  have hfin := hF.lifted.volume_lt_top
  obtain ⟨Tfam, hTfam⟩ := exists_commuted_typeZero_family hXt hw B hRowInt hLeftDiff hRightDiff hTransfer Fj Tj hT
  choose Λ hΛ Bl hBn hBt _ using fun L : List (TypeOperator F 0) =>
    TypeOperator.exists_listExtension_standard hF L hP1 hP
  refine ⟨∑ I ∈ wordFamily w kk, ∑ J ∈ wordsUpTo k I.length, Λ (Tfam I J) + 1,
    add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun I _ => Finset.sum_nonneg fun J _ => hΛ _)
      one_pos, fun Sb hSb f hf => ?_⟩
  have hAB : ∀ I ∈ wordFamily w kk, ∀ φ : TestFunction F.V ℝ (⊤ : ℕ∞),
      hasWeakWordDeriv C.Xl F.V I (⇑(Sb (testToLp F.V hfin P φ)))
        (⇑(∑ J ∈ wordsUpTo k I.length,
          Bl (Tfam I J) (testToLp F.V hfin P (S.wordDerivativeTest F.V C.Xl hXt J φ)))) :=
    fun I _ φ => commuted_lp_identity hXt hfin Tj Tfam hTfam Sb hSb (fun I J => Bl (Tfam I J))
      (fun I J φ => hBt (Tfam I J) φ) I φ
  obtain ⟨hmem, hnorm⟩ :=
    sobolevXENorm_family_extension_le hXt hfin hw kk Sb (fun I J => Bl (Tfam I J)) hAB f hf
  refine ⟨hmem, hnorm.trans ?_⟩
  have h : ∑ I ∈ wordFamily w kk, ∑ J ∈ wordsUpTo k I.length, ‖Bl (Tfam I J)‖ ≤
      ∑ I ∈ wordFamily w kk, ∑ J ∈ wordsUpTo k I.length, Λ (Tfam I J) + 1 :=
    (Finset.sum_le_sum fun I _ => Finset.sum_le_sum fun J _ => hBn _).trans
      (le_add_of_nonneg_right zero_le_one)
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal h) le_rfl

end LiftedChart

end RothschildStein.P1
