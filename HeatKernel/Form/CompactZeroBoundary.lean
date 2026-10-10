-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.ZeroBoundary
public import HeatKernel.Form.CompactGradientApproximation
import Mathlib.Tactic.Linter

/-! # Compact energy functions in zero-boundary domains -/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter TopologicalSpace RothschildStein
open scoped Topology

namespace HeatKernel

/-- A smooth compact function supported inside an open set has a global interior gradient pair. -/
theorem exists_interiorGradientPair {N q : ℕ} (U : Opens (Fin N → ℝ))
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)) {f : (Fin N → ℝ) → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f) (hs : tsupport f ⊆ U)
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) :
    ∃ v ∈ interiorGradientPairs U X, v.fst =ᵐ[volume] f ∧
      ∀ i, v.snd i =ᵐ[volume] fieldDerivative (X i) f := by
  obtain ⟨v, hv, hvf⟩ := exists_smoothGradientPair X hf hc hX
  have hvg : ∀ i, v.snd i =ᵐ[volume] fieldDerivative (X i) f := by
    intro i
    have hwk := smoothGradientSpan_le_weakGradientGraph ⊤ X (fun j => (hX j).contDiffOn)
      (Submodule.subset_span hv) i
    have hck := S.hasWeakWordDeriv_classical ⊤ X
      (fun j => (hX j).contDiffOn) [i] f hf.contDiffOn
    have hck' := S.hasWeakWordDeriv_congr_ae X ⊤ hck
      (by simpa only [Opens.coe_top, Measure.restrict_univ] using hvf.symm) Filter.EventuallyEq.rfl
    simpa only [Opens.coe_top, Measure.restrict_univ, wordDerivative, Function.comp_def] using
      S.hasWeakWordDeriv_unique X ⊤ hwk hck'
  exact ⟨v, ⟨f, hf, hc, hs, hvf, hvg⟩, hvf, hvg⟩

/-- Compact energy functions have interior smooth graph approximants, preserving nonnegativity. -/
theorem exists_interiorGradientPairs_approximation_of_compact_support {N q : ℕ} (U : Opens (Fin N → ℝ))
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (u : energyGraph (N := N) ⊤ X) {f : (Fin N → ℝ) → ℝ}
    (hc : HasCompactSupport f) (hs : tsupport f ⊆ U)
    (huf : (u : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume] f) :
    ∃ w : ℕ → GradientSpace (N := N) ⊤ q,
      (∀ n, w n ∈ interiorGradientPairs U X) ∧
      Tendsto w atTop (𝓝 (u : GradientSpace (N := N) ⊤ q)) ∧
      ((∀ᵐ x ∂volume, 0 ≤ f x) → ∀ n, ∀ᵐ x ∂volume, 0 ≤ (w n).fst x) := by
  let v : weakGradientGraph (N := N) ⊤ X (fun i => (hX i).contDiffOn) :=
    ⟨u, energyGraph_le_weakGradientGraph ⊤ X (fun i => (hX i).contDiffOn) u.property⟩
  have hvf : (v : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume] f := huf
  let V : GradientSpace (N := N) ⊤ q := v
  have hvf' : V.fst =ᵐ[volume.restrict (⊤ : Opens (Fin N → ℝ))] f := by
    simpa only [Opens.coe_top, Measure.restrict_univ] using hvf
  have hfp := (Lp.memLp V.fst).ae_eq hvf'
  have hwf : ∀ i, hasWeakWordDeriv X ⊤ [i] f (V.snd i) := fun i =>
    S.hasWeakWordDeriv_congr_ae X ⊤ (v.property i) hvf' Filter.EventuallyEq.rfl
  have hf : memSobolevX noDriftWeight X ⊤ 1 2 f :=
    memSobolevX_noDrift_one_two_iff.mpr ⟨hfp, fun i => ⟨V.snd i, hwf i, Lp.memLp _⟩⟩
  have H := S.tendsto_sobolevXENorm_mollifier_compact noDriftWeight X ⊤
    (fun i => (hX i).contDiffOn) 1 (by norm_num) hf hc (subset_univ _)
  have hword : ∀ I ∈ wordFamily noDriftWeight 1, Tendsto
      (fun ε : ℝ => weakWordENorm X ⊤ I 2
        (fun x => f x - S.euclideanRegularize N f ε x)) (𝓝[>] 0) (𝓝 0) := by
    intro I hI
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds H
      (fun _ => zero_le) (fun ε => weakWordENorm_le_sobolevXENorm noDriftWeight X ⊤ 1 2 _ hI)
  obtain ⟨δ, hδpos, hδ⟩ := S.exists_euclideanRegularize_support_inside_all_dimensions hc U.isOpen hs
  let ε : ℕ → ℝ := fun n => δ / (n + 1 : ℝ)
  have hεpos : ∀ n, 0 < ε n := fun n => by dsimp [ε]; exact div_pos hδpos (by positivity)
  have hεle : ∀ n, ε n ≤ δ := fun n =>
    div_le_self hδpos.le (by nlinarith [Nat.cast_nonneg (α := ℝ) n])
  have hε : Tendsto ε atTop (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, Filter.Eventually.of_forall hεpos⟩
    simpa only [mul_zero, mul_one_div] using
      (tendsto_const_nhds.mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) :
        Tendsto (fun n : ℕ => δ * (1 / (n + 1 : ℝ))) atTop (𝓝 (δ * 0)))
  have hl : LocallyIntegrable f volume := by
    have hp : MemLp f 2 volume := by
      simpa only [Opens.coe_top, Measure.restrict_univ] using hfp
    exact hp.locallyIntegrable (by norm_num)
  have hsm := fun n => S.euclideanRegularize_smooth_compact_all_dimensions hl hc (hεpos n)
  choose w hw hpairf hpairg using fun n => exists_interiorGradientPair U X
    (hsm n).1 (hsm n).2 (hδ (ε n) (hεpos n) (hεle n)) hX
  refine ⟨w, hw, (tendsto_GradientSpace_iff ⊤).mpr ⟨?_, ?_⟩, ?_⟩
  · apply tendsto_L2_of_representatives
      (fun n => by simpa only [Opens.coe_top, Measure.restrict_univ] using hpairf n)
      Filter.EventuallyEq.rfl
    simp only [Opens.coe_top, Measure.restrict_univ]
    have hn : hasWeakWordDeriv X ⊤ [] f f := S.hasWeakWordDeriv_nil X ⊤
        (locallyIntegrableOn_of_locallyIntegrable_restrict (hfp.locallyIntegrable (by norm_num)))
    have ht := (hword [] (S.nil_mem_wordFamily noDriftWeight 1)).comp hε
    apply ht.congr
    intro n
    have he := S.weakWordENorm_mollifier_error_eq ⊤ ⊤ (subset_refl _) X
      (fun i => (hX i).contDiffOn) (by norm_num) hfp [] hn (hεpos n)
    have he' : weakWordENorm X ⊤ [] 2 (fun x => f x - S.euclideanRegularize N f (ε n) x) =
        eLpNorm (S.euclideanRegularize N f (ε n) - f) 2 volume := by
      simpa only [Opens.coe_top, indicator_univ, Measure.restrict_univ, wordDerivative, Pi.sub_def] using he
    exact he'.trans (eLpNorm_congr_ae (Filter.EventuallyEq.rfl.sub hvf.symm))
  · intro i
    apply tendsto_L2_of_representatives
      (fun n => by simpa only [Opens.coe_top, Measure.restrict_univ] using hpairg n i)
      Filter.EventuallyEq.rfl
    simp only [Opens.coe_top, Measure.restrict_univ]
    have hi : [i] ∈ wordFamily noDriftWeight 1 :=
      (mem_wordFamily_noDrift_one_iff _).mpr (Or.inr ⟨i, rfl⟩)
    have ht := (hword [i] hi).comp hε
    apply ht.congr
    intro n
    have he := S.weakWordENorm_mollifier_error_eq ⊤ ⊤ (subset_refl _) X
      (fun j => (hX j).contDiffOn) (by norm_num) hfp [i] (hwf i) (hεpos n)
    simpa only [Opens.coe_top, indicator_univ, Measure.restrict_univ, wordDerivative, Function.comp_def, Pi.sub_def] using he
  · intro hnonneg n
    filter_upwards [hpairf n] with x hx
    rw [hx]
    apply integral_nonneg_of_ae
    filter_upwards [hnonneg] with y hy
    exact mul_nonneg (mul_nonneg (inv_nonneg.mpr (pow_nonneg (hεpos n).le _))
      ((S.euclideanJ_normalized N).1 _)) hy

/-- Compactly supported global energy functions belong to the corresponding zero-boundary domain. -/
theorem mem_zeroBoundaryGraph_of_compact_support {N q : ℕ} (U : Opens (Fin N → ℝ))
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (u : energyGraph (N := N) ⊤ X) {f : (Fin N → ℝ) → ℝ}
    (hc : HasCompactSupport f) (hs : tsupport f ⊆ U)
    (huf : (u : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume] f) :
    (u : GradientSpace (N := N) ⊤ q) ∈ zeroBoundaryGraph U X := by
  obtain ⟨w, hw, ht, _⟩ := exists_interiorGradientPairs_approximation_of_compact_support U X hX u hc hs huf
  exact (isClosed_zeroBoundaryGraph U X).mem_of_tendsto ht
    (Eventually.of_forall fun n => interiorGradientPairs_subset_zeroBoundaryGraph U X (hw n))



end HeatKernel
