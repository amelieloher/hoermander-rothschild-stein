-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.KernelReflection
public import RothschildStein.Definitions.HomogeneousGroup.HasPrincipalValue
public import Mathlib.Topology.UniformSpace.UniformConvergence

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
namespace RothschildStein.H1
variable {N q : ℕ} {G : HomogeneousGroup N} {H : StandingHypotheses G q}

/-- Exact remaining distributional uniqueness interface.
This does not follow merely from uniqueness of locally integrable kernels
(BB Theorem 6.18, printed p. 264). -/
def DistributionalKernelUniqueness (K : FundamentalKernel G H) : Prop :=
  ∀ T : Distribution (⊤ : Opens (Fin N → ℝ)) ℝ (⊤ : ℕ∞),
    G.HasHomogeneousDistribution (2 - (G.homogeneousDimension : ℝ)) T →
    isFundamentalDistribution (sumSquaresWithDriftTranspose H.fields) T → T = K.toDistribution

/-- The exact general homogeneous differential-operator bound.
This includes operators whose coefficients are not invariant
(BB Theorem 6.20(1), printed p. 269). -/
def GeneralKernelBounds (K : FundamentalKernel G H) : Prop :=
  ∀ D : SmoothDifferentialOperator N, ∀ k : ℝ, D.IsHomogeneous G k →
    ContDiffOn ℝ (⊤ : ℕ∞) (D.apply K) ({(0 : Fin N → ℝ)}ᶜ) ∧
    (∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 → D.apply K (G.dilate t x) =
      t ^ (2 - (G.homogeneousDimension : ℝ) - k) * D.apply K x) ∧
    ∃ C > 0, ∀ x, x ≠ 0 →
      |D.apply K x| ≤ C * (H.norm x) ^ (2 - (G.homogeneousDimension : ℝ) - k)

/-- Weighted shell cancellation holds for globally smooth degree-two
differential operators and continuous radial weights, without a surface
integral (BB Corollary 6.31, p. 280). -/
def KernelShellCancellation (K : FundamentalKernel G H) : Prop :=
  ∀ D : SmoothDifferentialOperator N, D.IsHomogeneous G 2 →
    ∀ r R : ℝ, 0 < r → r < R → ∀ Φ : ℝ → ℝ, ContinuousOn Φ (Icc r R) →
      IntegrableOn (fun x => D.apply K x * Φ (H.norm x)) {x | r < H.norm x ∧ H.norm x < R} ∧
      (∫ x in {x | r < H.norm x ∧ H.norm x < R}, D.apply K x * Φ (H.norm x)) = 0

/-- The complete first-derivative representation, including
absolute convergence (BB (6.45), printed p. 281). -/
def FirstKernelRepresentation (K : FundamentalKernel G H) : Prop :=
  ∀ φ : TestFunction (⊤ : Opens (Fin N → ℝ)) ℝ (⊤ : ℕ∞), ∀ j : Fin q, ∀ x,
    Integrable (fun y => sumSquaresWithDrift H.fields φ y *
      fieldDerivative (H.fields j.succ) K (G.mul (G.inv y) x)) ∧
    fieldDerivative (H.fields j.succ) φ x =
      G.potential (fieldDerivative (H.fields j.succ) K) (sumSquaresWithDrift H.fields φ) x

/-- The second-derivative estimate includes uniform convergence, the cutoff
formula for the constants, and absolute convergence of every truncation
(BB pp. 281–285). -/
structure SecondKernelRepresentation (K : FundamentalKernel G H) where
  alpha : Fin q → Fin q → ℝ
  truncated_integrable : ∀ φ : TestFunction (⊤ : Opens (Fin N → ℝ)) ℝ (⊤ : ℕ∞),
    ∀ i j : Fin q, ∀ x, ∀ ε : ℝ, 0 < ε →
      IntegrableOn (fun y => sumSquaresWithDrift H.fields φ y *
        fieldDerivative (H.fields i.succ) (fieldDerivative (H.fields j.succ) K) (G.mul (G.inv y) x))
        {y | ε < H.norm (G.mul (G.inv y) x)}
  uniform_convergence : ∀ φ : TestFunction (⊤ : Opens (Fin N → ℝ)) ℝ (⊤ : ℕ∞), ∀ i j : Fin q,
    TendstoUniformly
      (fun ε : ℝ => fun x => ∫ y in {y | ε < H.norm (G.mul (G.inv y) x)},
        sumSquaresWithDrift H.fields φ y *
          fieldDerivative (H.fields i.succ) (fieldDerivative (H.fields j.succ) K) (G.mul (G.inv y) x))
      (fun x => fieldDerivative (H.fields i.succ) (fieldDerivative (H.fields j.succ) φ) x -
        alpha i j * sumSquaresWithDrift H.fields φ x) (nhdsWithin 0 (Ioi 0))
  cutoff_formula : ∀ ϑ : (Fin N → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) ϑ →
    (∃ r > 0, ∀ x, H.norm x ≤ r → ϑ x = 0) →
    ∀ R : ℝ, 0 < R → (∀ x, R ≤ H.norm x → ϑ x = 1) → ∀ i j : Fin q,
      alpha i j = ∫ x in {x | H.norm x ≤ R},
        fieldDerivative (H.fields i.succ) (fun y => ϑ y * fieldDerivative (H.fields j.succ) K y) x

/-- Exact uniqueness at infinity for arbitrary fundamental
distributions whose tails have a continuous decaying representative.
The tail representation is expressed by compact-test pairings
(BB uniqueness and Liouville arguments, pp. 264, 271). -/
def DistributionalKernelUniquenessAtInfinity (K : FundamentalKernel G H) : Prop :=
  ∀ T : Distribution (⊤ : Opens (Fin N → ℝ)) ℝ (⊤ : ℕ∞),
    isFundamentalDistribution (sumSquaresWithDriftTranspose H.fields) T →
    (∃ R : ℝ, ∃ f : (Fin N → ℝ) → ℝ, ContinuousOn f {x | R < ‖x‖} ∧
      (∀ ε > 0, ∃ A : ℝ, ∀ x, A ≤ ‖x‖ → ‖f x‖ ≤ ε) ∧
      ∀ φ : TestFunction (⊤ : Opens (Fin N → ℝ)) ℝ (⊤ : ℕ∞),
        tsupport (φ : (Fin N → ℝ) → ℝ) ⊆ {x | R < ‖x‖} → T φ = ∫ x, f x * φ x) →
    T = K.toDistribution

end RothschildStein.H1
