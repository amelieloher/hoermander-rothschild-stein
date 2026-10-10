-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Bridge.TimeSpaceProducts
public import HeatKernel.Definitions.IsLocalWeakSolution
public import RothschildStein.Definitions.fieldDerivative
import Mathlib.Tactic.Linter

/-! # The literal parabolic tensor identity on a restricted time measure -/

@[expose] public section
open Set MeasureTheory TopologicalSpace RothschildStein
namespace HeatKernel

/-- A single weak gradient witness retains its local L² bounds and satisfies
the separated smooth weak equation on every time set containing the test support. -/
theorem IsLocalWeakSolution.exists_restricted_tensor_identity {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (a : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ)
    (I : Opens ℝ) (U : Opens (Fin N → ℝ))
    {u : ℝ → (Fin N → ℝ) → ℝ}
    (hu : IsLocalWeakSolution G hq hqpos hw hspan a I U u) :
    ∃ g : Fin q → ℝ → (Fin N → ℝ) → ℝ,
      (∀ᵐ t ∂(volume.restrict (I : Set ℝ)), ∀ i,
        hasWeakWordDeriv (G.horizontalFields hq) U [i] (u t) (g i t)) ∧
      (∀ (J : Set ℝ) (K : Set (Fin N → ℝ)),
        IsCompact J → J ⊆ (I : Set ℝ) → IsCompact K → K ⊆ (U : Set (Fin N → ℝ)) →
        ∀ i, MemLp (fun z : ℝ × (Fin N → ℝ) => g i z.1 z.2) 2 (volume.restrict (J ×ˢ K))) ∧
      ∀ (J : Set ℝ), J ⊆ (I : Set ℝ) →
        ∀ (ψ : ℝ → ℝ), ContDiff ℝ (⊤ : ℕ∞) ψ → HasCompactSupport ψ → tsupport ψ ⊆ J →
        ∀ (φ : (Fin N → ℝ) → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
          tsupport φ ⊆ (U : Set (Fin N → ℝ)) →
          Integrable (fun z : ℝ × (Fin N → ℝ) =>
            -(u z.1 z.2 * (deriv ψ z.1 * φ z.2)) +
              ∑ i, ∑ j, a z.1 z.2 i j * g j z.1 z.2 *
                (ψ z.1 * fieldDerivative (G.horizontalFields hq i) φ z.2))
            ((volume.restrict J).prod (volume : Measure (Fin N → ℝ))) ∧
          (∫ z : ℝ × (Fin N → ℝ),
            -(u z.1 z.2 * (deriv ψ z.1 * φ z.2)) +
              ∑ i, ∑ j, a z.1 z.2 i j * g j z.1 z.2 *
                (ψ z.1 * fieldDerivative (G.horizontalFields hq i) φ z.2)
            ∂(volume.restrict J).prod volume) = 0 := by
  obtain ⟨_, g, hg, hbound, hweak⟩ := hu
  refine ⟨g, hg, ?_, ?_⟩
  · intro J K hJ hJI hK hKU
    exact (hbound J K hJ hJI hK hKU).2
  · intro J hJI ψ hψ hcψ hsψ φ hφ hcφ hsφ
    have hprod : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℝ × (Fin N → ℝ) => ψ z.1 * φ z.2) :=
      (hψ.comp contDiff_fst).mul (hφ.comp contDiff_snd)
    have hcprod := hasCompactSupport_time_space_product hcψ hcφ
    have hsprod := (tsupport_time_space_product_subset ψ φ).trans (prod_mono hsψ hsφ)
    obtain ⟨hi, he⟩ := hweak _ hprod hcprod (hsprod.trans (prod_mono hJI Subset.rfl))
    have hip : Integrable (fun z : ℝ × (Fin N → ℝ) =>
        -(u z.1 z.2 * fderiv ℝ (fun z => ψ z.1 * φ z.2) z (1, 0)) +
          ∑ i, ∑ j, a z.1 z.2 i j * g j z.1 z.2 *
            fderiv ℝ (fun z => ψ z.1 * φ z.2) z (0, G.horizontalFields hq i z.2))
        ((volume : Measure ℝ).prod (volume : Measure (Fin N → ℝ))) := by
      simpa only [Measure.volume_eq_prod] using hi
    have hir := hip.restrict (s := J ×ˢ univ)
    rw [← Measure.restrict_prod_eq_prod_univ] at hir
    have her : (∫ z : ℝ × (Fin N → ℝ),
        -(u z.1 z.2 * fderiv ℝ (fun z => ψ z.1 * φ z.2) z (1, 0)) +
          ∑ i, ∑ j, a z.1 z.2 i j * g j z.1 z.2 *
            fderiv ℝ (fun z => ψ z.1 * φ z.2) z (0, G.horizontalFields hq i z.2)
        ∂(volume.restrict J).prod volume) = 0 := by
      rw [Measure.restrict_prod_eq_prod_univ, setIntegral_eq_integral_of_forall_compl_eq_zero]
      · simpa only [Measure.volume_eq_prod] using he
      · intro z hz
        have hn : z ∉ tsupport (fun z : ℝ × (Fin N → ℝ) => ψ z.1 * φ z.2) :=
          fun h => hz ⟨(hsprod h).1, mem_univ _⟩
        simp only [fderiv_of_notMem_tsupport ℝ hn, zero_apply, mul_zero, neg_zero,
          Finset.sum_const_zero, add_zero]
    have hdψ := hψ.differentiable (by simp)
    have hdφ := hφ.differentiable (by simp)
    have ht (z : ℝ × (Fin N → ℝ)) := fderiv_time_space_product_time (hdψ z.1) (hdφ z.2)
    have hx (z : ℝ × (Fin N → ℝ)) (i : Fin q) :=
      fderiv_time_space_product_space (hdψ z.1) (hdφ z.2) (G.horizontalFields hq i z.2)
    simpa only [ht, hx, fieldDerivative] using And.intro hir her

end HeatKernel
