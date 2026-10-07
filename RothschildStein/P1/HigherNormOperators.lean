-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.HigherNormClosure
public import RothschildStein.P1.SCommutationTypeZero
public import RothschildStein.P1.ContinuityTheorem

/-!
# Higher-order gain: the type-0 data of the commuted identities

Finite families of type-0 operators and their bounded `L^P` extensions, together with the commuted
identities of `SCommutationTypeZero` under the type-calculus hypotheses
`TypeKernelIntegrable`, `LeftDifferentiation`, `RightDifferentiation` and `DerivativeTransfer`, in the form used by
`HigherNormClosure`.

* `TypeOperator.exists_listExtension_standard`: a finite list `T₁, …, T_r` of operators of type `λ` on
  a standard frame has a bounded `L^P(V)`-operator `B` (`1 < P < ∞`) with `B φ = ∑ᵢ Tᵢ φ` a.e. on
  tests and `B g = ∑ᵢ Tᵢ g` a.e. on every measurable `g` of finite Hölder norm (continuity theorem, sums of the
  extensions of the single operators; the two realizations agree on the intersection);
* `exists_commuted_typeZero_family`: for a type-0 family `Tⱼ` with `Tⱼ g = X̃ⱼ (Fⱼ g)` weakly on tests
  (`S = ∑ⱼ X̃ⱼ Fⱼ`, `Fⱼ` of type `1`), there are lists `S_{I,J}` of type-0 operators with
  `X̃_I (S φ) = ∑_{|J| ≤ |I|} ∑_{T ∈ S_{I,J}} T (X̃_J φ)` weakly on `V` for every test `φ`
  (`SCommutationTypeZero`, re-expressed through the given `Tⱼ` by uniqueness of weak derivatives);
* `commuted_lp_identity`: the same identity with the operators replaced by bounded `L^P`-extensions.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped ENNReal Topology
namespace RothschildStein.P1

section Sums

variable {N : ℕ}

/-- Almost-everywhere equal summands give almost-everywhere equal finite sums. -/
theorem ae_finset_sum_congr {ι : Type*} {μ : Measure (Fin N → ℝ)} (s : Finset ι)
    {f g : ι → (Fin N → ℝ) → ℝ} (h : ∀ i ∈ s, f i =ᵐ[μ] g i) :
    (fun x => ∑ i ∈ s, f i x) =ᵐ[μ] fun x => ∑ i ∈ s, g i x := by
  have := (Filter.eventually_all_finset s).2 h
  filter_upwards [this] with x hx
  exact Finset.sum_congr rfl hx

variable {F : KernelFrame N} {lam : ℕ}

end Sums

namespace LiftedChart

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {F : KernelFrame (n + m)}
  {q : ℕ} {H : H1.StandingHypotheses C.G q} {K : H1.FundamentalKernel C.G H}
  {hQ : 2 < (C.G.homogeneousDimension : ℝ)} {lam : ℕ}

/-- **Bounded `L^P`-extension of a finite list of operators** (sums of the extensions of
`TypeOperator.exists_lpExtension_standard`): for a list `Tl` of type-`λ` operators of a standard
frame and `1 < P < ∞` there are `Λ ≥ 0` and a bounded `B` on `L^P(V)` with `‖B‖ ≤ Λ`, equal almost
everywhere to `∑_{T ∈ Tl} T φ` on every test `φ` and to `∑_{T ∈ Tl} T g` on every measurable `g` of
finite Hölder norm (the `L^P` and Hölder realizations agree on the intersection). -/
theorem _root_.RothschildStein.P1.TypeOperator.exists_listExtension_standard
    (hF : C.IsStandardFrame F H K hQ) (Tl : List (TypeOperator F lam)) {P : ℝ≥0∞} [Fact (1 ≤ P)]
    (hP1 : 1 < P) (hP : P ≠ ⊤) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧
      ∃ Bl : Lp ℝ P (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) →L[ℝ]
          Lp ℝ P (volume.restrict (F.V : Set (Fin (n + m) → ℝ))),
        ‖Bl‖ ≤ Λ ∧
        (∀ φ : TestFunction F.V ℝ (⊤ : ℕ∞),
          Bl (testToLp F.V hF.lifted.volume_lt_top P φ) =ᵐ[volume.restrict
            (F.V : Set (Fin (n + m) → ℝ))] fun ξ => (Tl.map fun T => T.apply φ ξ).sum) ∧
        (∀ {α : ℝ}, 0 < α → α < 1 → ∀ g : (Fin (n + m) → ℝ) → ℝ,
          ∀ hg : holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) g ≠ ⊤,
          ∀ hgm : AEStronglyMeasurable g (volume.restrict (F.V : Set (Fin (n + m) → ℝ))),
          Bl ((memLp_of_holderENorm_ne_top F.V.isOpen.measurableSet hF.lifted.volume_lt_top hg hgm
              P).toLp g) =ᵐ[volume.restrict (F.V : Set (Fin (n + m) → ℝ))]
            fun ξ => (Tl.map fun T => T.apply g ξ).sum) := by
  induction Tl with
  | nil =>
    refine ⟨0, le_rfl, 0, by simp, fun φ => ?_, fun _ _ g hg hgm => ?_⟩
    · simp only [zero_apply, List.map_nil, List.sum_nil]
      exact Lp.coeFn_zero ℝ P _
    · simp only [zero_apply, List.map_nil, List.sum_nil]
      exact Lp.coeFn_zero ℝ P _
  | cons T Tl ih =>
    obtain ⟨Λ', hΛ', Bl', hn', ht', hh'⟩ := ih
    obtain ⟨Λ, hΛ, Tb, hn, ht, hh, -⟩ := T.exists_lpExtension_standard hF hP1 hP
    refine ⟨Λ + Λ', add_nonneg hΛ hΛ', Tb + Bl', (norm_add_le _ _).trans (add_le_add hn hn'),
      fun φ => ?_, fun hα0 hα1 g hg hgm => ?_⟩
    · filter_upwards [Lp.coeFn_add (Tb (testToLp F.V hF.lifted.volume_lt_top P φ))
        (Bl' (testToLp F.V hF.lifted.volume_lt_top P φ)), (ht φ).2, ht' φ] with ξ e1 e2 e3
      simp only [add_apply, e1, Pi.add_apply, e2, e3, List.map_cons,
        List.sum_cons]
    · filter_upwards [Lp.coeFn_add (Tb ((memLp_of_holderENorm_ne_top F.V.isOpen.measurableSet
          hF.lifted.volume_lt_top hg hgm P).toLp g))
        (Bl' ((memLp_of_holderENorm_ne_top F.V.isOpen.measurableSet
          hF.lifted.volume_lt_top hg hgm P).toLp g)), hh hα0 hα1 g hg hgm,
        hh' hα0 hα1 g hg hgm] with ξ e1 e2 e3
      simp only [add_apply, e1, Pi.add_apply, e2, e3, List.map_cons,
        List.sum_cons]

end LiftedChart

section Commuted

variable {N k : ℕ} {F : KernelFrame N} {w : Fin k → ℕ+}
  {Xt : Fin k → (Fin N → ℝ) → (Fin N → ℝ)}

/-- **The commuted type-0 family of `S = ∑ⱼ Tⱼ`, `Tⱼ = X̃ⱼ Fⱼ`** (no drift; BB pp. 567-568,
Prop 11.31; no-drift commutation): let `Fⱼ` be type-1 operators and
`Tⱼ` type-0 operators with `Tⱼ g = X̃ⱼ (Fⱼ g)` weakly on `V` for every test `g`. There are finite
lists `S_{I,J}` of type-0 operators such that for every word `I` and test `f`, weakly on `V`,
`X̃_I (∑ⱼ Tⱼ f) = ∑_{|J| ≤ |I|} ∑_{T ∈ S_{I,J}} T (X̃_J f)`.
Assume `TypeKernelIntegrable`, `LeftDifferentiation`, `RightDifferentiation` and `DerivativeTransfer`. -/
theorem exists_commuted_typeZero_family
    (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Xt i) (F.V : Set (Fin N → ℝ)))
    (hw : ∀ j, (w j : ℕ) = 1) (B : Fin N → List (Fin k))
    (hRowInt : TypeKernelIntegrable F) (hLeftDiff : LeftDifferentiation F w Xt) (hRightDiff : RightDifferentiation F w Xt hXt)
    (hTransfer : DerivativeTransfer F w Xt B) (Fj : Fin k → TypeOperator F 1) (Tj : Fin k → TypeOperator F 0)
    (hT : ∀ (j : Fin k) (g : TestFunction F.V ℝ (⊤ : ℕ∞)),
      hasWeakWordDeriv Xt F.V [j] ((Fj j).apply (g : (Fin N → ℝ) → ℝ))
        ((Tj j).apply (g : (Fin N → ℝ) → ℝ))) :
    ∃ Tfam : List (Fin k) → List (Fin k) → List (TypeOperator F 0),
      ∀ (I : List (Fin k)) (f : TestFunction F.V ℝ (⊤ : ℕ∞)),
        hasWeakWordDeriv Xt F.V I (fun ξ => ∑ j, (Tj j).apply (f : (Fin N → ℝ) → ℝ) ξ)
          (fun ξ => ∑ J ∈ wordsUpTo k I.length,
            ((Tfam I J).map fun T =>
              T.apply (wordDerivative Xt J (f : (Fin N → ℝ) → ℝ)) ξ).sum) := by
  obtain ⟨E, Tfam, hE, hfam⟩ := noDrift_typeZero_commutedFamily_of_endpointFamily_of_transfer
    hXt hw B hRowInt hRightDiff hTransfer hLeftDiff Fj
  refine ⟨Tfam, fun I f => ?_⟩
  have hae : (fun ξ => ∑ j, (E j).out f ξ) =ᵐ[volume.restrict (F.V : Set (Fin N → ℝ))]
      fun ξ => ∑ j, (Tj j).apply (f : (Fin N → ℝ) → ℝ) ξ := by
    refine ae_finset_sum_congr Finset.univ fun j _ => ?_
    have h1 := (E j).weak f
    obtain ⟨hl, ho⟩ := hE j
    rw [hl, ho] at h1
    exact S.hasWeakWordDeriv_unique Xt F.V h1 (hT j f)
  exact S.hasWeakWordDeriv_congr_ae Xt F.V (hfam I f) hae ae_eq_rfl

/-- **The commuted identity with bounded `L^P`-operators**: if `A` and `Bop I J` are bounded on
`L^P(V)` and agree on tests with `∑ⱼ Tⱼ` and with the list sums `∑_{T ∈ S_{I,J}} T` respectively, then
for every word `I` and test `φ`, the weak `X̃_I`-derivative of `A φ` is
`∑_{|J| ≤ |I|} Bop I J (X̃_J φ)` (`L^P`-valued sums). -/
theorem commuted_lp_identity
    (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Xt i) (F.V : Set (Fin N → ℝ)))
    (hfin : volume (F.V : Set (Fin N → ℝ)) < ⊤) {P : ℝ≥0∞} [Fact (1 ≤ P)]
    (Tj : Fin k → TypeOperator F 0)
    (Tfam : List (Fin k) → List (Fin k) → List (TypeOperator F 0))
    (hTfam : ∀ (I : List (Fin k)) (f : TestFunction F.V ℝ (⊤ : ℕ∞)),
      hasWeakWordDeriv Xt F.V I (fun ξ => ∑ j, (Tj j).apply (f : (Fin N → ℝ) → ℝ) ξ)
        (fun ξ => ∑ J ∈ wordsUpTo k I.length,
          ((Tfam I J).map fun T =>
            T.apply (wordDerivative Xt J (f : (Fin N → ℝ) → ℝ)) ξ).sum))
    (A : Lp ℝ P (volume.restrict (F.V : Set (Fin N → ℝ))) →L[ℝ]
      Lp ℝ P (volume.restrict (F.V : Set (Fin N → ℝ))))
    (hA : ∀ φ : TestFunction F.V ℝ (⊤ : ℕ∞), A (testToLp F.V hfin P φ) =ᵐ[volume.restrict
      (F.V : Set (Fin N → ℝ))] fun ξ => ∑ j, (Tj j).apply (φ : (Fin N → ℝ) → ℝ) ξ)
    (Bop : List (Fin k) → List (Fin k) → (Lp ℝ P (volume.restrict (F.V : Set (Fin N → ℝ))) →L[ℝ]
      Lp ℝ P (volume.restrict (F.V : Set (Fin N → ℝ)))))
    (hB : ∀ (I J : List (Fin k)) (φ : TestFunction F.V ℝ (⊤ : ℕ∞)),
      Bop I J (testToLp F.V hfin P φ) =ᵐ[volume.restrict (F.V : Set (Fin N → ℝ))]
        fun ξ => ((Tfam I J).map fun T => T.apply (φ : (Fin N → ℝ) → ℝ) ξ).sum)
    (I : List (Fin k)) (φ : TestFunction F.V ℝ (⊤ : ℕ∞)) :
    hasWeakWordDeriv Xt F.V I (⇑(A (testToLp F.V hfin P φ)))
      (⇑(∑ J ∈ wordsUpTo k I.length,
        Bop I J (testToLp F.V hfin P (S.wordDerivativeTest F.V Xt hXt J φ)))) := by
  refine S.hasWeakWordDeriv_congr_ae Xt F.V (hTfam I φ) (hA φ).symm ?_
  exact (ae_finset_sum_congr _ fun J _ => (hB I J (S.wordDerivativeTest F.V Xt hXt J φ)).symm).trans
    (Lp.coeFn_fun_finsetSum _ _).symm

end Commuted

end RothschildStein.P1
