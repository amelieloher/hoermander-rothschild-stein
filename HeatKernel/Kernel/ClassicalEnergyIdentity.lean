-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.DivergenceFreeTests

/-! # Local energy test identities for smooth heat solutions

One integration by parts in the time field and in each horizontal field
turns a smooth heat equation into its first-order local energy identity.
-/

@[expose] public section

noncomputable section

open MeasureTheory TopologicalSpace
open scoped BigOperators
open RothschildStein Hormander.Interface

namespace HeatKernel

/-- Smooth solutions for divergence-free fields satisfy the compact local energy identity. -/
theorem integral_classical_energy_test_eq_zero {n q : ℕ}
    (Ω : Opens (Fin n → ℝ))
    (X : Fin (q + 1) → (Fin n → ℝ) → Fin n → ℝ)
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (hdiv : ∀ i x, euclideanDivergence (X i) x = 0)
    (v : (Fin n → ℝ) → ℝ) (hv : ContDiffOn ℝ (⊤ : ℕ∞) v Ω)
    (heq : ∀ x ∈ Ω, fieldDerivative (X 0) v x =
      ∑ i : Fin q, fieldDerivative (X i.succ) (fieldDerivative (X i.succ) v) x)
    (φ : (Fin n → ℝ) → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ω) :
    Integrable (fun x => -(v x * fieldDerivative (X 0) φ x) +
      ∑ i : Fin q, fieldDerivative (X i.succ) v x * fieldDerivative (X i.succ) φ x) ∧
    (∫ x, -(v x * fieldDerivative (X 0) φ x) +
      ∑ i : Fin q, fieldDerivative (X i.succ) v x * fieldDerivative (X i.succ) φ x) = 0 := by
  have hgrad (i : Fin (q + 1)) :=
    S.contDiffOn_fieldDerivative Ω (X i) v (hX i).contDiffOn hv
  have hsecond (i : Fin q) := S.contDiffOn_fieldDerivative Ω (X i.succ)
    (fieldDerivative (X i.succ) v) (hX i.succ).contDiffOn (hgrad i.succ)
  have htime := integrable_mul_fieldDerivative_compact_test
    (hv.continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet) (X 0) (hX 0) φ hφ hc hs
  have hspace (i : Fin q) := integrable_mul_fieldDerivative_compact_test
    ((hgrad i.succ).continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet)
    (X i.succ) (hX i.succ) φ hφ hc hs
  have htime' := integrable_mul_compact_test_of_locallyIntegrableOn (μ := volume)
    ((hgrad 0).continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet) hφ.continuous hc hs
  have hspace' (i : Fin q) := integrable_mul_compact_test_of_locallyIntegrableOn (μ := volume)
    ((hsecond i).continuousOn.locallyIntegrableOn Ω.isOpen.measurableSet) hφ.continuous hc hs
  have hneg : Integrable (fun x => -(v x * fieldDerivative (X 0) φ x)) := htime.neg
  have hsum := integrable_finsetSum Finset.univ (fun i _ => hspace i)
  refine ⟨hneg.add hsum, ?_⟩
  have ht := integral_fieldDerivative_mul_compact_test_eq_neg Ω (X 0) (hX 0).contDiffOn
    (fun x _ => hdiv 0 x) v hv φ hφ hc hs
  have hi (i : Fin q) :
      (∫ x in (Ω : Set (Fin n → ℝ)),
        fieldDerivative (X i.succ) v x * fieldDerivative (X i.succ) φ x) =
      -(∫ x in (Ω : Set (Fin n → ℝ)),
        fieldDerivative (X i.succ) (fieldDerivative (X i.succ) v) x * φ x) := by
    have h := integral_fieldDerivative_mul_compact_test_eq_neg Ω (X i.succ)
      (hX i.succ).contDiffOn (fun x _ => hdiv i.succ x)
      (fieldDerivative (X i.succ) v) (hgrad i.succ) φ hφ hc hs
    simpa only [neg_neg] using (congrArg Neg.neg h).symm
  have hrestricted :
      (∫ x in (Ω : Set (Fin n → ℝ)), -(v x * fieldDerivative (X 0) φ x) +
        ∑ i : Fin q, fieldDerivative (X i.succ) v x * fieldDerivative (X i.succ) φ x) = 0 := by
    rw [integral_add hneg.integrableOn hsum.integrableOn, integral_neg,
      integral_finsetSum Finset.univ (fun i _ => (hspace i).integrableOn), ← ht]
    simp_rw [hi]
    rw [Finset.sum_neg_distrib, ← sub_eq_add_neg,
      ← integral_finsetSum Finset.univ (fun i _ => (hspace' i).integrableOn),
      ← integral_sub htime'.integrableOn
        (integrable_finsetSum Finset.univ (fun i _ => (hspace' i).integrableOn))]
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro x hx
    change fieldDerivative (X 0) v x * φ x -
      (∑ i : Fin q, fieldDerivative (X i.succ) (fieldDerivative (X i.succ) v) x * φ x) = 0
    rw [← Finset.sum_mul, ← heq x hx, sub_self]
  rw [← hrestricted]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  have hnot : x ∉ tsupport φ := fun h => hx (hs h)
  have hd (i : Fin (q + 1)) : fieldDerivative (X i) φ x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hnot (S.tsupport_fieldDerivative_subset (X i) φ h))
  simp only [hd, mul_zero, neg_zero, Finset.sum_const_zero, add_zero]

end HeatKernel
