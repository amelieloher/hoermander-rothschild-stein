-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.UniformSupportExtension
public import RothschildStein.S.ContinuousCompactZeroExtension
public import RothschildStein.S.ContinuousWeakSupport

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory Function Filter Metric TopologicalSpace
open scoped Topology ContDiff
namespace RothschildStein.S
variable {n q : ℕ}

/-- Every weighted weak word with a continuous representative
is approximated uniformly on the whole local domain by the ordinary
mollifications of a compactly supported input's local zero extension.
The same mollifier family works for all words (BB Thm 2.20, p. 86). -/
theorem compact_uniform_weak_word_mollification
    (w : Fin q → ℕ+) (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (Ω : Opens (Fin n → ℝ))
    (hX : ∀ j,ContDiffOn ℝ (⊤ : ℕ∞) (X j) (Ω : Set (Fin n → ℝ)))
    (k : ℕ) (f : (Fin n → ℝ) → ℝ)
    (jet : List (Fin q) → (Fin n → ℝ) → ℝ) (hzero : jet [] = f)
    (hw : ∀ I ∈ wordFamily w k,hasWeakWordDeriv X Ω I f (jet I))
    (hct : ∀ I ∈ wordFamily w k,ContinuousOn (jet I) (Ω : Set (Fin n → ℝ)))
    {K : Set (Fin n → ℝ)} (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (hz : ∀ x ∈ (Ω : Set (Fin n → ℝ)) \ K,f x = 0) :
    ∀ I ∈ wordFamily w k,TendstoUniformlyOn
      (fun ε : ℝ => wordDerivative X I
        (euclideanRegularize n ((Ω : Set (Fin n → ℝ)).indicator f) ε))
      (jet I) (𝓝[>] 0) (Ω : Set (Fin n → ℝ)) := by
  classical
  obtain ⟨V,hV,hKV,hclV,hcV⟩ :=
    exists_open_between_and_isCompact_closure hK Ω.isOpen hKΩ
  let U : Opens (Fin n → ℝ) := ⟨V,hV⟩
  obtain ⟨δ,hd,hδ⟩ := exists_friedrichs_interior_radius Ω hcV hclV
  have he : ∀ j : Fin q,∃ B : (Fin n → ℝ) → (Fin n → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) B ∧
      ∀ z ∈ cthickening δ (closure V),B =ᶠ[𝓝 z] X j := by
    intro j
    exact exists_global_field_germ_extension Ω
      ⟨cthickening δ (closure V),hcV.cthickening⟩ hδ (X j) (hX j)
  choose B hB hG using he
  have hfc : ContinuousOn f (Ω : Set (Fin n → ℝ)) := by
    rw [← hzero]
    exact hct [] (nil_mem_wordFamily w k)
  obtain ⟨_,hc,hSupport⟩ :=
    continuous_compact_zeroExtension_of_local_support Ω hfc hK hKΩ hz
  obtain ⟨a,ha,hsa⟩ := exists_euclideanRegularize_support_inside_all_dimensions
    hc hV (hSupport.trans hKV)
  intro I hI
  have hs : ∀ J,J.Sublist I → J ∈ wordFamily w k := by
    intro J hJ
    exact (mem_wordFamily_iff w k J).mpr
      ((wordWeight_sublist_le w hJ).trans ((mem_wordFamily_iff w k I).mp hI))
  have ht := tendstoUniformlyOn_weakWord_mollifier_of_coefficient_germs Ω X hX B hB
    U.isOpen hcV hd hδ hG I f jet hzero (fun J hJ => hw J (hs J hJ))
    (fun J hJ => hct J (hs J hJ))
  apply tendstoUniformlyOn_of_eventual_support ht
  · intro x hx
    exact continuous_weakWord_zero_off_support Ω X I (hw I hI) (hct I hI)
      hK.isClosed hz x ⟨hx.1,fun hk => hx.2 (hKV hk)⟩
  · filter_upwards [Ioo_mem_nhdsGT ha] with ε hε
    exact (tsupport_wordDerivative_subset X I _).trans (hsa ε hε.1 hε.2.le)

end RothschildStein.S
