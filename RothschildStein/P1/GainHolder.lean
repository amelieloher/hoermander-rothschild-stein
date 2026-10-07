-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.GainSobolev
public import RothschildStein.Definitions.memHolderX
public import RothschildStein.Definitions.holderXENorm
public import RothschildStein.S.WeakIntrinsicWords

/-!
# Gain: the `C^α → C^{λ,α}` gain

For a type-`λ` operator `T` on a standard frame, `LeftDifferentiation` and `0 < α < 1`:
`T f ∈ C^{λ,α}_{X̃}(V)` and `‖T f‖_{C^{λ,α}_{X̃}(V)} ≤ C ‖f‖_{C^α(V)}` for every `f` of finite Hölder
norm (`memHolderX`, `holderXENorm`, lifted fields `C.Xl`, weights `w`, lifted control distance
`C.dl`; `TypeOperator.gain_holder`). The weak derivatives `X̃_I (T f) = S_I f` (`I` of weight at most
`λ`; iterated `LeftDifferentiation` on tests, then to Hölder inputs by `L^2` approximation:
`TypeOperator.hasWeakWordDeriv_of_holder`) are continuous (`S_I f ∈ C^α(V)` by the Hölder continuity of type-`0` operators); a continuous weak
derivative is the intrinsic one (S's flow-integration converse, `hasIntrinsicWordDeriv_of_continuous_weak_subwords`),
which proves the Hölder gain without Hölder norm density. The specializations `λ = 2` (`P`: `C^α → C^{2,α}`,
including `X̃₀ P`) and `λ = 1` (`F`: `C^α → C^{1,α}`) are the Hölder gain statements
(BB p. 567, Prop 11.30).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped ENNReal Topology
namespace RothschildStein.P1

/-- The intrinsic word norm is at most the Hölder norm of any intrinsic derivative
representative. -/
theorem intrinsicWordENorm_le_holderENorm {N k : ℕ} {Xt : Fin k → (Fin N → ℝ) → (Fin N → ℝ)}
    {d : (Fin N → ℝ) → (Fin N → ℝ) → ℝ≥0∞} {V : Opens (Fin N → ℝ)} {I : List (Fin k)} {α : ℝ}
    {f g : (Fin N → ℝ) → ℝ} (h : hasIntrinsicWordDeriv Xt V I f g) :
    intrinsicWordENorm Xt d V I α f ≤ holderENorm d α (V : Set (Fin N → ℝ)) g :=
  sInf_le ⟨g, h, rfl⟩

namespace LiftedChart

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {F : KernelFrame (n + m)}
  {q : ℕ} {H : H1.StandingHypotheses C.G q} {K : H1.FundamentalKernel C.G H}
  {hQ : 2 < (C.G.homogeneousDimension : ℝ)} {lam : ℕ}

/-- **Gain, Hölder version: `C^α → C^{λ,α}_{X̃}`**. For a type-`λ` operator `T`
of a standard frame, `LeftDifferentiation` and `0 < α < 1` there is `C_g` such that for every `f` of finite
Hölder norm `T f ∈ C^{λ,α}_{X̃}(V)` and `‖T f‖_{C^{λ,α}_{X̃}(V)} ≤ C_g ‖f‖_{C^α(V)}` (in terms of
`memHolderX`, `holderXENorm`). The intrinsic derivatives `X̃_I (T f)`, `|I|_w ≤ λ`, are the actions
`S_I f` of the operators `S_I` of type `λ - |I|_w`. -/
theorem _root_.RothschildStein.P1.TypeOperator.gain_holder (hF : C.IsStandardFrame F H K hQ)
    (hLeftDiff : LeftDifferentiation F w C.Xl) (T : TypeOperator F lam) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ Cg : ℝ, 0 < Cg ∧ ∀ f : (Fin (n + m) → ℝ) → ℝ,
      holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) f ≠ ⊤ →
      memHolderX w C.Xl C.dl F.V lam α (T.apply f) ∧
      holderXENorm w C.Xl C.dl F.V lam α (T.apply f) ≤
        ENNReal.ofReal Cg * holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) f := by
  classical
  have key : ∀ I : List (Fin k), ∃ (g : ((Fin (n + m) → ℝ) → ℝ) → (Fin (n + m) → ℝ) → ℝ) (CH : ℝ),
      0 < CH ∧ (wordWeight w I ≤ lam → ∀ f : (Fin (n + m) → ℝ) → ℝ,
        holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) f ≠ ⊤ →
          hasWeakWordDeriv C.Xl F.V I (T.apply f) (g f) ∧
          holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) (g f) ≤
            ENNReal.ofReal CH * holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) f) ∧
        (I = [] → ∀ f, g f = T.apply f) := by
    intro I
    by_cases hI0 : I = []
    · subst hI0
      obtain ⟨CH, hCH, -, hb⟩ := T.exists_holderENorm_bound_standard hF hα0 hα1
      exact ⟨T.apply, CH, hCH, fun _ f hf =>
        ⟨RothschildStein.S.hasWeakWordDeriv_nil C.Xl F.V
          (T.locallyIntegrableOn_apply_holder hF hα0 hα1 hf), hb f⟩, fun _ _ => rfl⟩
    by_cases hI : wordWeight w I ≤ lam
    · obtain ⟨Sop, hS⟩ := T.exists_wordOperator_standard hF hLeftDiff I hI
      obtain ⟨CH, hCH, -, hb⟩ := Sop.exists_holderENorm_bound_standard hF hα0 hα1
      exact ⟨Sop.apply, CH, hCH, fun _ f hf =>
        ⟨T.hasWeakWordDeriv_of_holder hF Sop I hS hα0 hα1 hf, hb f⟩, fun h => absurd h hI0⟩
    · exact ⟨fun _ => 0, 1, one_pos, fun h => absurd h hI, fun h => absurd h hI0⟩
  choose g CH hCH hg h0 using key
  have hmem : ∀ I ∈ wordFamily w lam, wordWeight w I ≤ lam := fun I hI =>
    (RothschildStein.S.mem_wordFamily_iff w lam I).mp hI
  refine ⟨∑ I ∈ wordFamily w lam, CH I,
    Finset.sum_pos (fun I _ => hCH I) ⟨[], RothschildStein.S.nil_mem_wordFamily w lam⟩,
    fun f hf => ?_⟩
  have hfin : ∀ I ∈ wordFamily w lam,
      holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) (g I f) < ⊤ := fun I hI =>
    lt_of_le_of_lt (hg I (hmem I hI) f hf).2
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (lt_top_iff_ne_top.mpr hf))
  have hcont : ∀ I ∈ wordFamily w lam, ContinuousOn (g I f) (F.V : Set (Fin (n + m) → ℝ)) :=
    fun I hI => continuousOn_of_holderENorm_lt_top hF.lifted.subset_U hα0 (hfin I hI)
  have hint : ∀ I ∈ wordFamily w lam, hasIntrinsicWordDeriv C.Xl F.V I (T.apply f) (g I f) := by
    intro I hI
    refine RothschildStein.S.hasIntrinsicWordDeriv_of_continuous_weak_subwords F.V C.Xl
      hF.lifted.contDiffOn_Xl I (T.apply f) (fun J => g J f) (h0 [] rfl f) (fun J hJ => ?_)
      (fun J hJ => ?_)
    · exact (hg J (hmem J (RothschildStein.S.sublist_mem_wordFamily w lam hJ hI)) f hf).1
    · exact hcont J (RothschildStein.S.sublist_mem_wordFamily w lam hJ hI)
  have hnil : [] ∈ wordFamily w lam := RothschildStein.S.nil_mem_wordFamily w lam
  refine ⟨⟨?_, fun I hI => ⟨g I f, hint I hI, hfin I hI⟩⟩, ?_⟩
  · have := hfin [] hnil
    rwa [h0 [] rfl f] at this
  unfold holderXENorm
  calc ∑ I ∈ wordFamily w lam, intrinsicWordENorm C.Xl C.dl F.V I α (T.apply f)
      ≤ ∑ I ∈ wordFamily w lam, ENNReal.ofReal (CH I) *
          holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) f := by
        refine Finset.sum_le_sum fun I hI => ?_
        exact (intrinsicWordENorm_le_holderENorm (hint I hI)).trans (hg I (hmem I hI) f hf).2
    _ = ENNReal.ofReal (∑ I ∈ wordFamily w lam, CH I) *
          holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) f := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun I _ => (hCH I).le), Finset.sum_mul]

end LiftedChart

end RothschildStein.P1
