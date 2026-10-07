-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.SolvabilityLp
public import RothschildStein.P1.ContinuityRegularAssembly
public import RothschildStein.P1.ContinuityTheorem

/-!
# Local solvability, `L^p` solutions: the integral operator of a type-`λ ≥ 1` kernel is the `L^p` extension

For a positive-type operator `T` of a standard frame, the continuity theorem gives the unique bounded extension
`T̄` of `L^P(V)` which agrees with `T` on tests, and identifies it with the pointwise action only on
tests and on the Hölder class. The local solvability argument applies the right parametrix to `L^p` data
(`E_r f`, `f ∈ L^p(U_r)`), so the identification is needed on all of `L^P(V)`:

* `LpBoundedOperator.restrict_extend`: a bounded `L^p(S)`-operator composed with the extension by zero
  from `V ⊆ S` is a bounded `L^p(V)`-operator;
* `PatchKernel.exists_lpBoundedOperator`: the integral operator `f ↦ ∫ κ(·, η) f(η) dη` of a patch
  kernel is an `LpBoundedOperator` on `L^p(V)` (Schur, with a.e. linearity from the a.e. absolute
  convergence of the rows);
* `TypeOperator.lpExtension_eq_apply_of_memLp`: for `T` of positive type on a standard frame and every
  bounded `T̄ : L^P(V) → L^P(V)` agreeing with `T` on tests, `T̄ g = T g` almost everywhere for every
  `g ∈ L^P(V)` (`T g = ∫ k(·, η) g(η) dη`), by uniqueness of the bounded extension (continuity theorem).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped ENNReal NNReal Topology
open RothschildStein.P1
namespace RothschildStein.P2

section Restrict

variable {E : Type*} [MeasurableSpace E] {μ : Measure E} {S V : Set E} {p : ℝ≥0∞} {Λ : ℝ}
  {T : (E → ℝ) → (E → ℝ)}

/-- A bounded `L^p(S)`-operator, applied to the extension by zero from a
measurable `V ⊆ S`, is a bounded `L^p(V)`-operator with the same norm bound. -/
theorem LpBoundedOperator.restrict_extend (hV : MeasurableSet V) (hVS : V ⊆ S)
    (hT : LpBoundedOperator (μ.restrict S) p T Λ) :
    LpBoundedOperator (μ.restrict V) p (fun f : E → ℝ => T (V.indicator f)) Λ := by
  have hmem : ∀ f : E → ℝ, MemLp f p (μ.restrict V) → MemLp (V.indicator f) p (μ.restrict S) := by
    intro f hf
    rw [memLp_indicator_iff_restrict hV, Measure.restrict_restrict hV, inter_eq_left.2 hVS]
    exact hf
  have hμ : μ.restrict V ≤ μ.restrict S := Measure.restrict_mono hVS le_rfl
  have hnorm : ∀ f : E → ℝ, eLpNorm (V.indicator f) p (μ.restrict S) =
      eLpNorm f p (μ.restrict V) := by
    intro f
    rw [eLpNorm_indicator_eq_eLpNorm_restrict hV, Measure.restrict_restrict hV,
      inter_eq_left.2 hVS]
  refine ⟨fun f hf => (hT.memLp _ (hmem f hf)).mono_measure hμ, fun f hf => ?_,
    fun f g hfg => ?_, fun f g hf hg => ?_, fun c f hf => ?_⟩
  · refine (eLpNorm_mono_measure _ hμ).trans ((hT.norm_le _ (hmem f hf)).trans ?_)
    rw [hnorm f]
  · have h1 : ∀ᵐ x ∂(μ.restrict S), x ∈ V → f x = g x :=
      ae_restrict_of_ae ((ae_restrict_iff' hV).1 hfg)
    have h2 : V.indicator f =ᵐ[μ.restrict S] V.indicator g := by
      filter_upwards [h1] with x hx
      by_cases hxV : x ∈ V
      · simp [Set.indicator_of_mem hxV, hx hxV]
      · simp [Set.indicator_of_notMem hxV]
    exact ae_restrict_of_ae_restrict_of_subset hVS (hT.ae_congr _ _ h2)
  · have h1 : V.indicator (f - g) = V.indicator f - V.indicator g := by
      funext x
      by_cases hxV : x ∈ V <;> simp [hxV]
    have h2 := hT.ae_sub (V.indicator f) (V.indicator g) (hmem f hf) (hmem g hg)
    rw [← h1] at h2
    exact ae_restrict_of_ae_restrict_of_subset hVS h2
  · have h1 : V.indicator (c • f) = c • V.indicator f := by
      funext x
      by_cases hxV : x ∈ V <;> simp [hxV]
    have h2 := hT.ae_smul c (V.indicator f) (hmem f hf)
    rw [← h1] at h2
    exact ae_restrict_of_ae_restrict_of_subset hVS h2

end Restrict

section PatchKernel

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {S V : Set (Fin (n + m) → ℝ)}
  {κ : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ}

/-- **The integral operator of a patch kernel is a bounded `L^p(V)`-operator**
for every `1 ≤ p < ∞` (Schur's lemma, BB Prop 11.10; the row integrals converge absolutely almost
everywhere, so the operator is linear up to null sets on `L^p`). -/
theorem _root_.RothschildStein.P1.LiftedChart.PatchKernel.exists_lpBoundedOperator
    (h : C.PatchKernel S V κ) :
    ∃ Λ : ℝ, 0 < Λ ∧ ∀ p : ℝ≥0∞, 1 ≤ p → p ≠ ⊤ →
      LpBoundedOperator (volume.restrict V) p (fun f ξ => ∫ η, κ ξ η * f η) Λ := by
  obtain ⟨ρ, Cv, hS⟩ := C.exists_shellData_patch h.isCompact h.subset_U
  obtain ⟨A, B, hK⟩ := C.exists_sliceBounds_of_hasKernelBounds h.subset_U h.bounds h.measurable
  have hA := hK.A_nonneg
  have hC := hS.Cv_nonneg
  have hρ := hS.ρ_pos
  have hΛ0 : 0 < A * (Cv * 2 ^ (C.G.homogeneousDimension - 1 + 1)) * (2 * ρ) + 1 := by positivity
  refine ⟨_, hΛ0, fun p hp1 hpt => ?_⟩
  have hp'1 : (1 : ℝ) ≤ p.toReal := one_le_toReal_of_ne_top hp1 hpt
  have h1 := lpBoundedOperator_of_sliceBounds hS hK hΛ0 (le_add_of_nonneg_right zero_le_one) hp'1
  rw [ENNReal.ofReal_toReal hpt] at h1
  have h2 := h1.restrict_extend h.measurableSet h.subset
  exact h2.congr_ae (fun f => Filter.Eventually.of_forall fun ξ => h.integral_eq f ξ)

end PatchKernel

section Identify

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {F : KernelFrame (n + m)}
  {q : ℕ} {H : H1.StandingHypotheses C.G q} {K : H1.FundamentalKernel C.G H}
  {hQ : 2 < (C.G.homogeneousDimension : ℝ)} {lam : ℕ}

/-- **The `L^P` extension of a positive-type operator is its integral.** Let `T`
be a type-`λ ≥ 1` operator of a standard frame, `1 < P < ∞`, and `T̄` any bounded operator of
`L^P(V)` which agrees almost everywhere with `T` on every test function (by the continuity theorem there is exactly one).
Then `T̄ g = T g = ∫ k(·, η) g(η) dη` almost everywhere on `V`, for every `g ∈ L^P(V)`. -/
theorem _root_.RothschildStein.P1.TypeOperator.lpExtension_eq_apply_of_memLp (hF : C.IsStandardFrame F H K hQ)
    (hlam : 1 ≤ lam) (T : TypeOperator F lam) {P : ℝ≥0∞} [Fact (1 ≤ P)] (hP1 : 1 < P)
    (hP : P ≠ ⊤)
    (Tb : Lp ℝ P (volume.restrict (F.V : Set (Fin (n + m) → ℝ))) →L[ℝ]
      Lp ℝ P (volume.restrict (F.V : Set (Fin (n + m) → ℝ))))
    (hTb : ∀ f : TestFunction F.V ℝ (⊤ : ℕ∞),
      Tb (testToLp F.V hF.lifted.volume_lt_top P f) =ᵐ[volume.restrict
        (F.V : Set (Fin (n + m) → ℝ))] T.apply f)
    {g : (Fin (n + m) → ℝ) → ℝ}
    (hg : MemLp g P (volume.restrict (F.V : Set (Fin (n + m) → ℝ)))) :
    Tb (hg.toLp g) =ᵐ[volume.restrict (F.V : Set (Fin (n + m) → ℝ))] T.apply g := by
  obtain ⟨Λ, hΛ, hop⟩ := (TypeOperator.patchKernel hF.lifted hlam T).exists_lpBoundedOperator
  have hopP := hop P hP1.le hP
  obtain ⟨Λ₀, -, Tb₀, -, ht₀, -, hu₀⟩ := T.exists_lpExtension_standard hF hP1 hP
  have happ : T.apply = fun f ξ => ∫ η, T.kernel ξ η * f η :=
    funext fun f => TypeOperator.apply_eq_integral (by omega) T f
  let T' := hopP.toCLM hΛ.le
  have hT'test : ∀ f : TestFunction F.V ℝ (⊤ : ℕ∞),
      T' (testToLp F.V hF.lifted.volume_lt_top P f) =ᵐ[volume.restrict
        (F.V : Set (Fin (n + m) → ℝ))] T.apply f := by
    intro f
    have h1 := hopP.coeFn_toLp (testToLp F.V hF.lifted.volume_lt_top P f)
    have h2 : ⇑(testToLp F.V hF.lifted.volume_lt_top P f) =ᵐ[volume.restrict
        (F.V : Set (Fin (n + m) → ℝ))] (f : (Fin (n + m) → ℝ) → ℝ) :=
      (testFunction_memLp F.V hF.lifted.volume_lt_top f P).coeFn_toLp
    have h3 := hopP.ae_congr _ _ h2
    refine h1.trans (h3.trans ?_)
    rw [happ]
  have hT'eq : T' = Tb₀ := hu₀ T' fun f => Lp.ext ((hT'test f).trans (ht₀ f).2.symm)
  have hTbeq : Tb = Tb₀ := hu₀ Tb fun f => Lp.ext ((hTb f).trans (ht₀ f).2.symm)
  rw [hTbeq, ← hT'eq]
  have h1 := hopP.coeFn_toLp (hg.toLp g)
  have h2 : ⇑(hg.toLp g) =ᵐ[volume.restrict (F.V : Set (Fin (n + m) → ℝ))] g :=
    MemLp.coeFn_toLp _
  have h3 := hopP.ae_congr _ _ h2
  refine h1.trans (h3.trans ?_)
  rw [happ]

end Identify

end RothschildStein.P2
