-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.AssemblyInputs
public import RothschildStein.H1.KernelCommonBounds
public import RothschildStein.H1.KernelPotential

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
namespace RothschildStein.H1
variable {N q : ℕ} {G : HomogeneousGroup N} {H : StandingHypotheses G q}

/-- The one-operator conclusion packages the basic kernel properties in
FundamentalKernel. It includes BB Theorem 11.5(a–d), the first-derivative
representation, and radial shell truncations, with no Euclidean surface integral. -/
structure FundamentalKernelProperties (K : FundamentalKernel G H) : Prop where
  distribution_homogeneous : G.HasHomogeneousDistribution
    (2 - (G.homogeneousDimension : ℝ)) K.toDistribution
  distribution_fundamental : isFundamentalDistribution (sumSquaresWithDriftTranspose H.fields) K.toDistribution
  represents : representsDistribution ⊤ K.toDistribution K
  unique_distribution : DistributionalKernelUniqueness K
  common_bounds : ∃ C > 0, ∀ x, x ≠ 0 →
    |K x| ≤ C * (H.norm x) ^ (2 - (G.homogeneousDimension : ℝ)) ∧
    (∀ i : Fin q, |fieldDerivative (H.fields i.succ) K x| ≤
      C * (H.norm x) ^ (1 - (G.homogeneousDimension : ℝ))) ∧
    (∀ i j : Fin q,
      |fieldDerivative (H.fields i.succ) (fieldDerivative (H.fields j.succ) K) x| +
        |fieldDerivative (H.fields 0) K x| ≤ C * (H.norm x) ^ (-(G.homogeneousDimension : ℝ)))
  word_smooth : ∀ I : List (Fin (q + 1)),
    ContDiffOn ℝ (⊤ : ℕ∞) (wordDerivative H.fields I K) ({(0 : Fin N → ℝ)}ᶜ)
  word_homogeneous : ∀ I : List (Fin (q + 1)), ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 →
    wordDerivative H.fields I K (G.dilate t x) =
      t ^ (2 - (G.homogeneousDimension : ℝ) - (differentialWordWeight I : ℝ)) * wordDerivative H.fields I K x
  low_weight_locallyIntegrable : ∀ I : List (Fin (q + 1)), differentialWordWeight I < 2 →
    LocallyIntegrable (wordDerivative H.fields I K)
  general_bounds : GeneralKernelBounds K
  potential_smooth : ∀ φ : TestFunction (⊤ : Opens (Fin N → ℝ)) ℝ (⊤ : ℕ∞),
    ContDiff ℝ (⊤ : ℕ∞) (G.potential K φ)
  potential_equation : ∀ φ : TestFunction (⊤ : Opens (Fin N → ℝ)) ℝ (⊤ : ℕ∞),
    sumSquaresWithDrift H.fields (G.potential K φ) = φ
  two_sided : ∀ φ : TestFunction (⊤ : Opens (Fin N → ℝ)) ℝ (⊤ : ℕ∞), ∀ x,
    Integrable (fun y => sumSquaresWithDrift H.fields φ y * K (G.mul (G.inv y) x)) ∧
    φ x = G.potential K (sumSquaresWithDrift H.fields φ) x
  first_representation : FirstKernelRepresentation K
  second_representation : Nonempty (SecondKernelRepresentation K)
  cancellation : KernelShellCancellation K
  unique_at_infinity : DistributionalKernelUniquenessAtInfinity K

/-- The uniform cutoff-limit formula supplies the pointwise principal-value
condition, including integrable truncations (BB (11.3), printed p. 539). -/
theorem SecondKernelRepresentation.principalValue {K : FundamentalKernel G H}
    (R : SecondKernelRepresentation K)
    (φ : TestFunction (⊤ : Opens (Fin N → ℝ)) ℝ (⊤ : ℕ∞)) (i j : Fin q) (x : Fin N → ℝ) :
    G.HasPrincipalValue H.norm (fieldDerivative (H.fields i.succ) (fieldDerivative (H.fields j.succ) K))
      (sumSquaresWithDrift H.fields φ) x
      (fieldDerivative (H.fields i.succ) (fieldDerivative (H.fields j.succ) φ) x -
        R.alpha i j * sumSquaresWithDrift H.fields φ x) :=
  ⟨R.truncated_integrable φ i j x, (R.uniform_convergence φ i j).tendsto_at x⟩

/-- A single matrix of PV constants works for every compact
smooth input and every evaluation point (BB (11.3), printed p. 539). -/
theorem FundamentalKernelProperties.principalValue_constants {K : FundamentalKernel G H}
    (P : FundamentalKernelProperties K) :
    ∃ alpha : Fin q → Fin q → ℝ,
      ∀ φ : TestFunction (⊤ : Opens (Fin N → ℝ)) ℝ (⊤ : ℕ∞), ∀ i j : Fin q, ∀ x,
        G.HasPrincipalValue H.norm (fieldDerivative (H.fields i.succ) (fieldDerivative (H.fields j.succ) K))
          (sumSquaresWithDrift H.fields φ) x
          (fieldDerivative (H.fields i.succ) (fieldDerivative (H.fields j.succ) φ) x -
            alpha i j * sumSquaresWithDrift H.fields φ x) := by
  obtain ⟨R⟩ := P.second_representation
  exact ⟨R.alpha, R.principalValue⟩

/-- The remaining hypotheses are uniqueness for arbitrary distributions,
the local kernel bound, principal-value convergence, and uniform
second-derivative estimates. The regular distribution, common bounds, and
potential identities follow from the preceding results (BB pp. 538–539). -/
theorem assemble_kernel_of_uniqueness_bounds_cancellation (K : FundamentalKernel G H)
    (hQ : 2 < (G.homogeneousDimension : ℝ))
    (hUniq : DistributionalKernelUniqueness K)
    (hBounds : GeneralKernelBounds K) (hCancel : KernelShellCancellation K)
    (hFirstRep : FirstKernelRepresentation K) (hSecondRep : Nonempty (SecondKernelRepresentation K))
    (hUniqInf : DistributionalKernelUniquenessAtInfinity K) : FundamentalKernelProperties K :=
  ⟨K.distribution_homogeneous, K.distribution_fundamental, K.represents, hUniq,
    K.common_bounds, H.wordDerivative_smooth_off_zero G K.smooth_off_zero,
    H.wordDerivative_homogeneous G K.smooth_off_zero K.homogeneous,
    H.wordDerivative_locallyIntegrable G K.smooth_off_zero K.homogeneous,
    hBounds, K.potential_smooth, K.potential_equation,
    K.potential_twoSided hQ, hFirstRep, hSecondRep, hCancel, hUniqInf⟩

end RothschildStein.H1
