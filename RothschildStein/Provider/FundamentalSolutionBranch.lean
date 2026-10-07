-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.Provider.FundamentalSolutionBridges

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology
namespace RothschildStein.Provider
variable {N q : ℕ}

/-- One branch of the fundamental-solution statement, including the drift bound. In the
no-drift case the zero drift term is removed. All distribution and principal-value predicates
are those of `RothschildStein.Definitions`. -/
def FundamentalSolutionBranch (G : HomogeneousGroup N) (ν : (Fin N → ℝ) → ℝ)
    (Y : Fin q → (Fin N → ℝ) → (Fin N → ℝ)) (Z : (Fin N → ℝ) → (Fin N → ℝ))
    (P Pt : ((Fin N → ℝ) → ℝ) → (Fin N → ℝ) → ℝ)
    (K : (Fin N → ℝ) → ℝ) (alpha : Fin q → Fin q → ℝ) : Prop :=
∃ T : Distribution (⊤ : TopologicalSpace.Opens (Fin N → ℝ)) ℝ (⊤ : ℕ∞),
  G.HasHomogeneousDistribution (2 - (G.homogeneousDimension : ℝ)) T ∧
  isFundamentalDistribution Pt T ∧
  (∀ S : Distribution (⊤ : TopologicalSpace.Opens (Fin N → ℝ)) ℝ (⊤ : ℕ∞),
    G.HasHomogeneousDistribution (2 - (G.homogeneousDimension : ℝ)) S →
    isFundamentalDistribution Pt S → S = T) ∧
  representsDistribution ⊤ T K ∧
  ContDiffOn ℝ (⊤ : ℕ∞) K ({0}ᶜ) ∧
  (∀ t : ℝ, 0 < t → ∀ x : Fin N → ℝ, x ≠ 0 →
    K (G.dilate t x) = t ^ (2 - (G.homogeneousDimension : ℝ)) * K x) ∧
  (∃ C : ℝ, 0 < C ∧ ∀ x : Fin N → ℝ, x ≠ 0 →
    |K x| ≤ C * ν x ^ (2 - (G.homogeneousDimension : ℝ)) ∧
    (∀ i : Fin q, |fieldDerivative (Y i) K x| ≤
      C * ν x ^ (1 - (G.homogeneousDimension : ℝ))) ∧
    (∀ i j : Fin q,
      |fieldDerivative (Y i) (fieldDerivative (Y j) K) x| + |fieldDerivative Z K x| ≤
        C * ν x ^ (-(G.homogeneousDimension : ℝ)))) ∧
  (∀ (D : SmoothDifferentialOperator N) (k : ℝ), D.IsHomogeneous G k →
    ∃ C : ℝ, 0 < C ∧ ∀ x : Fin N → ℝ, x ≠ 0 →
      |D.apply K x| ≤ C * ν x ^ (2 - (G.homogeneousDimension : ℝ) - k)) ∧
  (∀ (D : SmoothDifferentialOperator N), D.IsHomogeneous G 2 →
    ∀ r R : ℝ, 0 < r → r < R →
    ∀ Φ : ℝ → ℝ, ContinuousOn Φ (Icc r R) →
      IntegrableOn (fun x => D.apply K x * Φ (ν x)) {x | r < ν x ∧ ν x < R} ∧
      (∫ x in {x | r < ν x ∧ ν x < R}, D.apply K x * Φ (ν x)) = 0) ∧
  (∀ φ : TestFunction (⊤ : TopologicalSpace.Opens (Fin N → ℝ)) ℝ (⊤ : ℕ∞),
    ContDiff ℝ (⊤ : ℕ∞) (G.potential K φ) ∧
    (∀ v, P (G.potential K φ) v = φ v) ∧
    ∀ v : Fin N → ℝ,
      Integrable (fun u => P φ u * K (G.mul (G.inv u) v)) ∧
      φ v = G.potential K (P φ) v ∧
      (∀ j : Fin q,
        Integrable (fun u => P φ u * fieldDerivative (Y j) K (G.mul (G.inv u) v)) ∧
        fieldDerivative (Y j) φ v = G.potential (fieldDerivative (Y j) K) (P φ) v) ∧
      (∀ i j : Fin q,
        G.HasPrincipalValue ν (fieldDerivative (Y i) (fieldDerivative (Y j) K))
          (P φ) v (fieldDerivative (Y i) (fieldDerivative (Y j) φ) v - alpha i j * P φ v)))

/-- Fundamental-solution predicates agree when the operators agree on smooth inputs. -/
theorem isFundamentalDistribution_congr_smooth
    {P Q : ((Fin N → ℝ) → ℝ) → (Fin N → ℝ) → ℝ}
    (he : ∀ f, ContDiff ℝ (⊤ : ℕ∞) f → P f = Q f)
    (T : Distribution (⊤ : Opens (Fin N → ℝ)) ℝ (⊤ : ℕ∞)) :
    isFundamentalDistribution P T ↔ isFundamentalDistribution Q T := by
  constructor <;> intro h φ <;> obtain ⟨ψ, hψ, hv⟩ := h φ
  · exact ⟨ψ, fun x => (hψ x).trans (congrFun (he φ φ.contDiff) x), hv⟩
  · exact ⟨ψ, fun x => (hψ x).trans (congrFun (he φ φ.contDiff) x).symm, hv⟩

/-- The fundamental-kernel properties supply every branch conclusion.
Operator equality is needed only on smooth inputs, including the smooth potential. -/
theorem fundamentalSolutionBranch_of_properties {G : HomogeneousGroup N} {H : H1.StandingHypotheses G q}
    (K : H1.FundamentalKernel G H) (A : H1.FundamentalKernelProperties K)
    (P Pt : ((Fin N → ℝ) → ℝ) → (Fin N → ℝ) → ℝ)
    (heP : ∀ f, ContDiff ℝ (⊤ : ℕ∞) f → sumSquaresWithDrift H.fields f = P f)
    (hePt : ∀ f, ContDiff ℝ (⊤ : ℕ∞) f → sumSquaresWithDriftTranspose H.fields f = Pt f) :
    ∃ alpha, FundamentalSolutionBranch G H.norm (fun i => H.fields i.succ) (H.fields 0) P Pt K alpha := by
  obtain ⟨alpha, ha⟩ := A.principalValue_constants
  refine ⟨alpha, K.toDistribution, A.distribution_homogeneous,
    (isFundamentalDistribution_congr_smooth hePt _).mp A.distribution_fundamental, ?_,
    A.represents, K.smooth_off_zero, K.homogeneous, A.common_bounds, ?_, A.cancellation, ?_⟩
  · intro S hh hf
    exact A.unique_distribution S hh ((isFundamentalDistribution_congr_smooth hePt _).mpr hf)
  · intro D k hk
    exact (A.general_bounds D k hk).2.2
  · intro φ
    have hφ := heP φ φ.contDiff
    refine ⟨A.potential_smooth φ, ?_, ?_⟩
    · intro v
      rw [← heP _ (A.potential_smooth φ)]
      exact congrFun (A.potential_equation φ) v
    · intro v
      rw [← hφ]
      obtain ⟨hi, he⟩ := A.two_sided φ v
      exact ⟨hi, he, fun j => A.first_representation φ j v, fun i j => ha φ i j v⟩

/-- In the reversed branch, the horizontal fields and all absolute drift bounds
are unchanged; the operator and its test transpose are exchanged. -/
theorem fundamentalSolutionBranch_reverse_of_properties {G : HomogeneousGroup N}
    {H : H1.StandingHypotheses G q} (K : H1.FundamentalKernel G (H.reverseDrift G))
    (A : H1.FundamentalKernelProperties K) :
    ∃ alpha, FundamentalSolutionBranch G H.norm (fun i => H.fields i.succ) (H.fields 0)
      (sumSquaresWithDriftTranspose H.fields) (sumSquaresWithDrift H.fields) K alpha := by
  obtain ⟨alpha, ha⟩ := fundamentalSolutionBranch_of_properties K A _ _
    (fun f hf => funext (H.reverseDrift_operator G f hf))
    (fun f hf => funext (H.reverseDrift_transpose_operator G hf))
  refine ⟨alpha, ?_⟩
  simpa only [FundamentalSolutionBranch, H1.StandingHypotheses.reverseDrift,
    H1.driftSign, Fin.succ_ne_zero, ite_false, one_smul, ite_true,
    Pi.smul_apply, neg_one_smul, fieldDerivative, map_neg, abs_neg] using ha

/-- No drift gives inverse symmetry for the actual kernel representative,
including zero. Function-level uniqueness suffices for this symmetry. -/
theorem fundamentalKernel_inv_eq_of_zeroDrift {G : HomogeneousGroup N}
    {H : H1.StandingHypotheses G q} (K : H1.FundamentalKernel G H)
    (hQ : 2 < (G.homogeneousDimension : ℝ)) (hzero : H.fields 0 = 0) :
    ∀ x, K (G.inv x) = K x := by
  let R := K.reflection hQ
  have hfields : (H.reverseDrift G).fields = H.fields := by
    funext i
    by_cases hi : i = 0
    · subst i
      simp [H1.StandingHypotheses.reverseDrift, H1.driftSign, hzero]
    · simp [H1.StandingHypotheses.reverseDrift, H1.driftSign, hi]
  let J : H1.FundamentalKernel G H :=
    ⟨R, R.locallyIntegrable, R.smooth_off_zero, R.homogeneous,
      fun φ hs hc => by simpa only [hfields] using R.fundamental φ hs hc⟩
  have hae := J.unique_ae K hQ
  have he := Measure.eqOn_open_of_ae_eq (ae_restrict_of_ae hae) isOpen_compl_singleton
    J.smooth_off_zero.continuousOn K.smooth_off_zero.continuousOn
  intro x
  by_cases hx : x = 0
  · subst x; rw [G2.inv_zero]
  · exact he hx

end RothschildStein.Provider
