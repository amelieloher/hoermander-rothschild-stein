-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.SmoothGraphLimits
public import HeatKernel.Moser.LocalHorizontalDerivatives
public import RothschildStein.S.CompactMollifierConvergence
import Mathlib.Tactic.Positivity

/-!
# Compact weak gradients belong to the energy graph

Ordinary mollification of compactly supported first-order horizontal Sobolev functions converges
in the graph norm. This identifies compact weak-gradient pairs with vectors in the closed smooth
graph (Bramanti–Brandolini, Corollary 2.10, p. 73).
-/

@[expose] public section

noncomputable section

open Set MeasureTheory Filter TopologicalSpace RothschildStein
open scoped ENNReal Topology

namespace HeatKernel

/-- Each weak-word seminorm is bounded by the Sobolev seminorm containing that word. -/
theorem weakWordENorm_le_sobolevXENorm {N q : ℕ} (w : Fin q → ℕ+)
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)) (U : Opens (Fin N → ℝ))
    (k : ℕ) (p : ℝ≥0∞) (f : (Fin N → ℝ) → ℝ) {I : List (Fin q)}
    (hI : I ∈ wordFamily w k) : weakWordENorm X U I p f ≤ sobolevXENorm w X U k p f := by
  unfold sobolevXENorm
  exact Finset.single_le_sum (f := fun J => weakWordENorm X U J p f) (fun _ _ => zero_le) hI

/-- A compactly supported weak-gradient pair lies in the closed smooth energy graph. -/
theorem mem_energyGraph_of_compact_weakGradient {N q : ℕ}
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (v : weakGradientGraph (N := N) ⊤ X (fun i => (hX i).contDiffOn))
    {f : (Fin N → ℝ) → ℝ} (hc : HasCompactSupport f)
    (hvf : (v : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume] f) :
    (v : GradientSpace (N := N) ⊤ q) ∈ energyGraph ⊤ X := by
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
  let ε : ℕ → ℝ := fun n => 1 / (n + 1 : ℝ)
  have hεpos : ∀ n, 0 < ε n := fun n => by dsimp [ε]; positivity
  have hε : Tendsto ε atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Filter.Eventually.of_forall hεpos⟩
  have hl : LocallyIntegrable f volume := by
    have hp : MemLp f 2 volume := by
      simpa only [Opens.coe_top, Measure.restrict_univ] using hfp
    exact hp.locallyIntegrable (by norm_num)
  have hsm := fun n => S.euclideanRegularize_smooth_compact_all_dimensions hl hc (hεpos n)
  apply mem_energyGraph_of_smooth_approximation X hX V (fun n => (hsm n).1) (fun n => (hsm n).2)
  · have hn : hasWeakWordDeriv X ⊤ [] f f := S.hasWeakWordDeriv_nil X ⊤
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
    have hi : [i] ∈ wordFamily noDriftWeight 1 :=
      (mem_wordFamily_noDrift_one_iff _).mpr (Or.inr ⟨i, rfl⟩)
    have ht := (hword [i] hi).comp hε
    apply ht.congr
    intro n
    have he := S.weakWordENorm_mollifier_error_eq ⊤ ⊤ (subset_refl _) X
      (fun j => (hX j).contDiffOn) (by norm_num) hfp [i] (hwf i) (hεpos n)
    simpa only [Opens.coe_top, indicator_univ, Measure.restrict_univ, wordDerivative, Function.comp_def, Pi.sub_def] using he

end HeatKernel
