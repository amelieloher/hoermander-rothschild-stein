-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.WeakWordUniformMollifier
public import RothschildStein.S.MollifierTubeLocality
public import RothschildStein.S.MollifierCompactAllDimensions
public import RothschildStein.S.FieldGermExtension
public import RothschildStein.S.WeakHolderRepresentatives

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory Function Filter Metric TopologicalSpace
open scoped Topology ContDiff
namespace RothschildStein.S
variable {n q : ℕ}

/-- One interior cutoff supplies smooth compact ordinary
mollifications whose entire weighted word family converges uniformly
on the chosen patch to the continuous weak representatives. The
cutoff is one on a fixed positive buffer and works for every word
(BB Thm 2.20 and Lemma 2.21, pp. 86–87; cutoff identity). -/
theorem exists_cutoff_uniform_word_approximation
    (w : Fin q → ℕ+) (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (Ω U : Opens (Fin n → ℝ))
    (hX : ∀ j,ContDiffOn ℝ (⊤ : ℕ∞) (X j) (Ω : Set (Fin n → ℝ)))
    (hc : IsCompact (closure (U : Set (Fin n → ℝ))))
    (hUΩ : closure (U : Set (Fin n → ℝ)) ⊆ Ω) (k : ℕ)
    (f : (Fin n → ℝ) → ℝ) (jet : List (Fin q) → (Fin n → ℝ) → ℝ)
    (hzero : jet [] = f)
    (hw : ∀ I ∈ wordFamily w k,hasWeakWordDeriv X Ω I f (jet I))
    (hct : ∀ I ∈ wordFamily w k,ContinuousOn (jet I) (Ω : Set (Fin n → ℝ))) :
    ∃ χ : TestFunction Ω ℝ (⊤ : ℕ∞),∃ δ : ℝ,0 < δ ∧
      EqOn (χ : (Fin n → ℝ) → ℝ) (fun _ => 1)
        (cthickening δ (closure (U : Set (Fin n → ℝ)))) ∧
      (∀ ε : ℝ,0 < ε →
        ContDiff ℝ (⊤ : ℕ∞) (euclideanRegularize n (fun x => f x*χ x) ε) ∧
        HasCompactSupport (euclideanRegularize n (fun x => f x*χ x) ε)) ∧
      ∀ I ∈ wordFamily w k,TendstoUniformlyOn
        (fun ε : ℝ => wordDerivative X I (euclideanRegularize n (fun x => f x*χ x) ε))
        (jet I) (𝓝[>] 0) (U : Set (Fin n → ℝ)) := by
  classical
  obtain ⟨δ,hd,hδ⟩ := exists_friedrichs_interior_radius Ω hc hUΩ
  obtain ⟨χ,W,hW,hKW,hWΩ,hχ⟩ := exists_test_plateau Ω
    ⟨cthickening δ (closure (U : Set (Fin n → ℝ))),hc.cthickening⟩ hδ
  have hχt : EqOn (χ : (Fin n → ℝ) → ℝ) (fun _ => 1)
      (cthickening δ (closure (U : Set (Fin n → ℝ)))) := fun _ hx => hχ (hKW hx)
  have hfc : ContinuousOn f (Ω : Set (Fin n → ℝ)) := by
    rw [← hzero]
    exact hct [] (nil_mem_wordFamily w k)
  have hg : Continuous (fun x => f x*χ x) := continuous_mul_test_of_continuousOn Ω hfc χ
  refine ⟨χ,δ,hd,hχt,fun ε hε =>
    euclideanRegularize_smooth_compact_all_dimensions hg.locallyIntegrable χ.hasCompactSupport.mul_left hε,?_⟩
  have he : ∀ j : Fin q,∃ B : (Fin n → ℝ) → (Fin n → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) B ∧
      ∀ z ∈ cthickening δ (closure (U : Set (Fin n → ℝ))),B =ᶠ[𝓝 z] X j := by
    intro j
    exact exists_global_field_germ_extension Ω
      ⟨cthickening δ (closure (U : Set (Fin n → ℝ))),hc.cthickening⟩ hδ (X j) (hX j)
  choose B hB hG using he
  intro I hI
  have hs : ∀ J,J.Sublist I → J ∈ wordFamily w k := by
    intro J hJ
    exact (mem_wordFamily_iff w k J).mpr
      ((wordWeight_sublist_le w hJ).trans ((mem_wordFamily_iff w k I).mp hI))
  have ht := tendstoUniformlyOn_weakWord_mollifier_of_coefficient_germs Ω X hX B hB
    U.isOpen hc hd hδ hG I f jet hzero (fun J hJ => hw J (hs J hJ))
    (fun J hJ => hct J (hs J hJ))
  apply ht.congr
  filter_upwards [Ioo_mem_nhdsGT hd] with ε hε
  apply wordDerivative_regularize_eqOn_of_eqOn_interior_tube X I U.isOpen hε
  intro x hx
  simp only [indicator_of_mem (hδ hx),hχt hx,mul_one]

end RothschildStein.S
