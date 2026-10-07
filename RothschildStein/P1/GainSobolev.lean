-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.GainExtension
public import RothschildStein.Definitions.memSobolevX
public import RothschildStein.Definitions.sobolevXENorm

/-!
# Gain: the `L^p → W^{k,p}_{X̃}` gain

For a type-`λ` operator `T` on a standard frame, and `LeftDifferentiation` (left differentiation of types):

* `TypeOperator.gain_lp_tests`: for `1 < p < ∞` and every test `f`, `T f ∈ W^{λ,p}_{X̃}(V)` (that is,
  `memSobolevX`, lifted fields `C.Xl`, weights `w`) and `‖T f‖_{W^{λ,p}_{X̃}(V)} ≤ C ‖f‖_p` (norm
  `sobolevXENorm`): the weak derivatives `X̃_I (T f)`, `|I|_w ≤ λ`, are `S_I f` with `S_I` of type
  `λ - |I|_w ≥ 0` (iterated `LeftDifferentiation`) bounded on `L^p` by the continuity theorem;
* `TypeOperator.gain_lp_extension`: the same for every `g ∈ L^p(V)` and the unique bounded
  extension `T̄ g` of `T` (the weak derivative identities pass to the limit).

The specializations `λ = 2` (`P`: `‖P f‖_{W^{2,p}} ≤ C ‖f‖_p`, with the weight-two derivative `X̃₀ P`
of type `0` but not `X̃₀ F`, since `X̃₀ F` has weight two exceeding the type `1` of `F`) and `λ = 1`
(`F`: `‖F f‖_{W^{1,p}} ≤ C ‖f‖_p`) are the `L^p` gain statements (BB pp. 567–568, Prop 11.30).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped ENNReal Topology
namespace RothschildStein.P1

/-- The weak word norm is at most the `L^P` norm of any weak derivative
representative. -/
theorem weakWordENorm_le_eLpNorm {N k : ℕ} {Xt : Fin k → (Fin N → ℝ) → (Fin N → ℝ)}
    {V : Opens (Fin N → ℝ)} {I : List (Fin k)} {P : ℝ≥0∞} {f g : (Fin N → ℝ) → ℝ}
    (h : hasWeakWordDeriv Xt V I f g)
    (hg : AEStronglyMeasurable g (volume.restrict (V : Set (Fin N → ℝ)))) :
    weakWordENorm Xt V I P f ≤ eLpNorm g P (volume.restrict (V : Set (Fin N → ℝ))) :=
  sInf_le ⟨g, h, hg, rfl⟩

/-- A bounded operator on `L^P` multiplies the `L^P` norm by at most its norm bound. -/
theorem eLpNorm_clm_le {E : Type*} [MeasurableSpace E] {μ : Measure E} {P : ℝ≥0∞} [Fact (1 ≤ P)]
    (A : Lp ℝ P μ →L[ℝ] Lp ℝ P μ) {Λ : ℝ} (hΛ : ‖A‖ ≤ Λ) (g : Lp ℝ P μ) :
    eLpNorm (A g) P μ ≤ ENNReal.ofReal Λ * eLpNorm g P μ := by
  have h : ‖A g‖ ≤ Λ * ‖g‖ := (A.le_opNorm g).trans (mul_le_mul_of_nonneg_right hΛ (norm_nonneg _))
  calc eLpNorm (A g) P μ = ‖A g‖ₑ := (Lp.enorm_def _).symm
    _ = ENNReal.ofReal ‖A g‖ := (ofReal_norm _).symm
    _ ≤ ENNReal.ofReal (Λ * ‖g‖) := ENNReal.ofReal_le_ofReal h
    _ = ENNReal.ofReal Λ * ‖g‖ₑ := by
        rw [ENNReal.ofReal_mul ((norm_nonneg A).trans hΛ), ofReal_norm]
    _ = ENNReal.ofReal Λ * eLpNorm g P μ := by rw [Lp.enorm_def]

namespace LiftedChart

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {F : KernelFrame (n + m)}
  {q : ℕ} {H : H1.StandingHypotheses C.G q} {K : H1.FundamentalKernel C.G H}
  {hQ : 2 < (C.G.homogeneousDimension : ℝ)} {lam : ℕ}

/-- **Gain for the bounded extension: `L^p → W^{λ,p}_{X̃}`**. For a type-`λ`
operator of a standard frame, `LeftDifferentiation` and `1 < P < ∞` there is `C_g` such that for every bounded
operator `T̄` on `L^P(V)` which agrees with `T` on tests (by the continuity theorem there is exactly one) and every
`g ∈ L^P(V)`, `T̄ g ∈ W^{λ,P}_{X̃}(V)` and `‖T̄ g‖_{W^{λ,P}_{X̃}(V)} ≤ C_g ‖g‖_{L^P(V)}`. The weak
derivatives `X̃_I (T̄ g)` are `S̄_I g` for the bounded extensions `S̄_I` of the operators `S_I` of
type `λ - |I|_w`. -/
theorem _root_.RothschildStein.P1.TypeOperator.gain_lp_extension (hF : C.IsStandardFrame F H K hQ)
    (hLeftDiff : LeftDifferentiation F w C.Xl) (T : TypeOperator F lam) {P : ℝ≥0∞} [Fact (1 ≤ P)] (hP1 : 1 < P)
    (hP : P ≠ ⊤) :
    ∃ Cg : ℝ, 0 < Cg ∧
      ∀ Tb : Lp ℝ P (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) →L[ℝ]
          Lp ℝ P (volume.restrict (F.V : Set (Fin (n + m) → ℝ))),
        (∀ f : TestFunction F.V ℝ (⊤ : ℕ∞),
          Tb (testToLp F.V hF.lifted.volume_lt_top P f) =ᵐ[volume.restrict
            (F.V : Set (Fin (n + m) → ℝ))] T.apply f) →
        ∀ g : Lp ℝ P (volume.restrict (F.V : Set (Fin (n + m) → ℝ))),
          memSobolevX w C.Xl F.V lam P (Tb g) ∧
          sobolevXENorm w C.Xl F.V lam P (Tb g) ≤
            ENNReal.ofReal Cg * eLpNorm g P (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) := by
  classical
  have key : ∀ I : List (Fin k),
      ∃ (Sb : Lp ℝ P (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) →L[ℝ]
          Lp ℝ P (volume.restrict (F.V : Set (Fin (n + m) → ℝ)))) (Λ : ℝ), 0 ≤ Λ ∧ ‖Sb‖ ≤ Λ ∧
        (wordWeight w I ≤ lam → ∃ b : TestFunction F.V ℝ (⊤ : ℕ∞) → (Fin (n + m) → ℝ) → ℝ,
          (∀ f : TestFunction F.V ℝ (⊤ : ℕ∞), Sb (testToLp F.V hF.lifted.volume_lt_top P f) =ᵐ[volume.restrict
            (F.V : Set (Fin (n + m) → ℝ))] b f) ∧
          ∀ f : TestFunction F.V ℝ (⊤ : ℕ∞), hasWeakWordDeriv C.Xl F.V I (T.apply f) (b f)) := by
    intro I
    by_cases hI : wordWeight w I ≤ lam
    · obtain ⟨Sop, hS⟩ := T.exists_wordOperator_standard hF hLeftDiff I hI
      obtain ⟨Λ, hΛ, Sb, hn, ht, -, -⟩ := Sop.exists_lpExtension_standard hF hP1 hP
      exact ⟨Sb, Λ, hΛ, hn, fun _ => ⟨fun f => Sop.apply f, fun f => (ht f).2, hS⟩⟩
    · exact ⟨0, 0, le_rfl, by simp, fun h => absurd h hI⟩
  choose Sb Λ hΛ hn hb using key
  have hmem : ∀ I ∈ wordFamily w lam, wordWeight w I ≤ lam := fun I hI =>
    (RothschildStein.S.mem_wordFamily_iff w lam I).mp hI
  refine ⟨∑ I ∈ wordFamily w lam, Λ I + 1,
    add_pos_of_nonneg_of_pos (Finset.sum_nonneg fun I _ => hΛ I) one_pos, fun Tb hTb g => ?_⟩
  have hweak : ∀ I ∈ wordFamily w lam, hasWeakWordDeriv C.Xl F.V I (Tb g) (Sb I g) := by
    intro I hI
    obtain ⟨b, hb1, hb2⟩ := hb I (hmem I hI)
    exact hasWeakWordDeriv_extension hF.lifted.contDiffOn_Xl hF.lifted.volume_lt_top hP I
      (fun f => T.apply f) b Tb (Sb I) hTb hb1 hb2 g
  refine ⟨?_, ?_⟩
  · unfold memSobolevX
    exact ⟨Lp.memLp (Tb g), fun I hI => ⟨Sb I g, hweak I hI, Lp.memLp (Sb I g)⟩⟩
  unfold sobolevXENorm
  calc ∑ I ∈ wordFamily w lam, weakWordENorm C.Xl F.V I P (Tb g)
      ≤ ∑ I ∈ wordFamily w lam, ENNReal.ofReal (Λ I) *
          eLpNorm g P (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) := by
        refine Finset.sum_le_sum fun I hI => ?_
        exact (weakWordENorm_le_eLpNorm (hweak I hI)
          (Lp.memLp (Sb I g)).aestronglyMeasurable).trans (eLpNorm_clm_le (Sb I) (hn I) g)
    _ = ENNReal.ofReal (∑ I ∈ wordFamily w lam, Λ I) *
          eLpNorm g P (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun I _ => hΛ I), Finset.sum_mul]
    _ ≤ ENNReal.ofReal (∑ I ∈ wordFamily w lam, Λ I + 1) *
          eLpNorm g P (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) := by
        gcongr
        linarith

end LiftedChart

end RothschildStein.P1
