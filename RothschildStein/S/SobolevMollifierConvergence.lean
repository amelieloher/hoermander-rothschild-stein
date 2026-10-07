-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.WeakWordMollifierConvergence
public import RothschildStein.S.SobolevRepresentatives
public import RothschildStein.S.MollifierWeakNorm
public import RothschildStein.S.FieldGermExtension
public import RothschildStein.S.WeakKernelTransferPatch

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory Function Filter Metric TopologicalSpace
open scoped ENNReal Topology ContDiff BigOperators
namespace RothschildStein.S
variable {n q : ℕ} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Zero-extended ordinary mollification converges in the exact
Sobolev norm on every compactly contained open subdomain.
Weights may include a weight-two drift; only subword closure is used
(BB Thm 2.9, p. 73, drift paragraph p. 79). -/
theorem tendsto_sobolevXENorm_mollifier_local
    (w : Fin q → ℕ+) (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (Ω U : Opens (Fin n → ℝ))
    (hX : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (X j) (Ω : Set (Fin n → ℝ)))
    (hc : IsCompact (closure (U : Set (Fin n → ℝ))))
    (hUΩ : closure (U : Set (Fin n → ℝ)) ⊆ Ω)
    (k : ℕ) (hpt : p ≠ ⊤) {f : (Fin n → ℝ) → ℝ} (hf : memSobolevX w X Ω k p f) :
    Tendsto (fun ε : ℝ => sobolevXENorm w X U k p
      (fun x => f x-euclideanRegularize n ((Ω : Set (Fin n → ℝ)).indicator f) ε x))
      (𝓝[>] 0) (𝓝 0) := by
  classical
  obtain ⟨δ,hd,hδ⟩ := exists_friedrichs_interior_radius Ω hc hUΩ
  have he : ∀ j : Fin q, ∃ B : (Fin n → ℝ) → (Fin n → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) B ∧
      ∀ z ∈ cthickening δ (closure (U : Set (Fin n → ℝ))), B =ᶠ[𝓝 z] X j := by
    intro j
    exact exists_global_field_germ_extension Ω
      ⟨cthickening δ (closure (U : Set (Fin n → ℝ))),hc.cthickening⟩ hδ (X j) (hX j)
  choose B hB hG using he
  obtain ⟨jet,hzero,hjet⟩ := exists_sobolev_representatives w X Ω k hf
  have ht : ∀ I ∈ wordFamily w k, Tendsto
      (fun ε : ℝ => weakWordENorm X U I p
        (fun x => f x-euclideanRegularize n ((Ω : Set (Fin n → ℝ)).indicator f) ε x))
      (𝓝[>] 0) (𝓝 0) := by
    intro I hI
    have hs : ∀ J, J.Sublist I → J ∈ wordFamily w k := by
      intro J hJ
      exact (mem_wordFamily_iff w k J).mpr
        ((wordWeight_sublist_le w hJ).trans ((mem_wordFamily_iff w k I).mp hI))
    have H := tendsto_weakWord_mollifier_error_of_coefficient_germs Ω X hX B hB
      U.isOpen hc hd hδ hG hpt I f jet hzero
      (fun J hJ => (hjet J (hs J hJ)).1) (fun J hJ => (hjet J (hs J hJ)).2)
    apply H.congr'
    filter_upwards [Ioo_mem_nhdsGT hd] with ε hε
    exact (weakWordENorm_mollifier_error_eq Ω U (subset_closure.trans hUΩ) X hX
      Fact.out hf.1 I (hjet I hI).1 hε.1).symm
  unfold sobolevXENorm
  simpa only [Finset.sum_const_zero] using tendsto_finsetSum (wordFamily w k) ht

end RothschildStein.S
