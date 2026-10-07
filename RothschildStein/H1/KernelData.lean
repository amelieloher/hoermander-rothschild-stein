-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.FullHomogeneity
public import RothschildStein.H1.FundamentalUniqueness
public import RothschildStein.H1.KernelIntegrability
public import RothschildStein.H1.PotentialEquation
public import RothschildStein.H1.TwoSidedInverse
public import RothschildStein.Definitions.representsDistribution
public import RothschildStein.Definitions.HomogeneousGroup.potential
public import RothschildStein.G2.DistributionHomogeneity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
namespace RothschildStein.H1
variable {N q : ℕ}

/-- A homogeneous fundamental kernel with local integrability and
smoothness away from zero. Its value at zero is unrestricted
(BB Theorems 6.18 and 11.5(a), pp. 264, 538). -/
structure FundamentalKernel (G : HomogeneousGroup N) (H : StandingHypotheses G q) where
  toFun : (Fin N → ℝ) → ℝ
  locallyIntegrable : LocallyIntegrable toFun
  smooth_off_zero : ContDiffOn ℝ (⊤ : ℕ∞) toFun ({(0 : Fin N → ℝ)}ᶜ)
  homogeneous : ∀ t : ℝ, 0 < t → ∀ x, x ≠ 0 →
    toFun (G.dilate t x) = t ^ (2 - (G.homogeneousDimension : ℝ)) * toFun x
  fundamental : ∀ φ : (Fin N → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
    (∫ x, toFun x * sumSquaresWithDriftTranspose H.fields φ x) = φ 0

instance FundamentalKernel.instCoeFun {G : HomogeneousGroup N} {H : StandingHypotheses G q} :
    CoeFun (FundamentalKernel G H) (fun _ => (Fin N → ℝ) → ℝ) := ⟨FundamentalKernel.toFun⟩

variable (G : HomogeneousGroup N) (H : StandingHypotheses G q)

variable {G H}

/-- The regular distribution of the locally integrable kernel
(BB Definition 6.16, printed p. 264). -/
def FundamentalKernel.toDistribution (K : FundamentalKernel G H) :
    Distribution (⊤ : Opens (Fin N → ℝ)) ℝ (⊤ : ℕ∞) :=
  Distribution.ofFun ⊤ K volume (⊤ : ℕ∞)

/-- The distribution is represented by the actual kernel in the
representation condition (BB pp. 264–267). -/
theorem FundamentalKernel.represents (K : FundamentalKernel G H) :
    representsDistribution ⊤ K.toDistribution K :=
  ⟨locallyIntegrableOn_univ.mpr K.locallyIntegrable, rfl⟩

/-- The kernel's actual distribution has degree 2-Q
(BB Definition 6.16, printed p. 264). -/
theorem FundamentalKernel.distribution_homogeneous (K : FundamentalKernel G H) :
    G.HasHomogeneousDistribution (2 - (G.homogeneousDimension : ℝ)) K.toDistribution := by
  rw [G2.hasHomogeneousDistribution_iff]
  intro t ht φ
  have he : -(G.homogeneousDimension : ℝ) - (2 - (G.homogeneousDimension : ℝ)) = -2 := by ring
  rw [he]
  have hl : LocallyIntegrableOn K (univ : Set (Fin N → ℝ)) volume :=
    locallyIntegrableOn_univ.mpr K.locallyIntegrable
  change Distribution.ofFun ⊤ K volume (⊤ : ℕ∞) (G2.dilatedTest G t ht φ) =
    t ^ (-2 : ℝ) * Distribution.ofFun ⊤ K volume (⊤ : ℕ∞) φ
  rw [Distribution.ofFun_apply hl, Distribution.ofFun_apply hl]
  simpa only [smul_eq_mul, G2.dilatedTest_apply, mul_comm] using
    fundamental_distributionHomogeneity G K.homogeneous ht φ

/-- The regular distribution satisfies the fixed fundamental
predicate, using the actual transpose test (BB Definition 6.16, p. 264). -/
theorem FundamentalKernel.distribution_fundamental (K : FundamentalKernel G H) :
    isFundamentalDistribution (sumSquaresWithDriftTranspose H.fields) K.toDistribution := by
  rw [H.isFundamentalDistribution_iff G]
  intro φ
  change Distribution.ofFun ⊤ K volume (⊤ : ℕ∞)
    (sumSquaresWithDriftTransposeTest ⊤ H.fields (fun i => (H.fields_smooth G i).contDiffOn) φ) = _
  rw [Distribution.ofFun_apply (locallyIntegrableOn_univ.mpr K.locallyIntegrable)]
  have he := K.fundamental φ φ.contDiff φ.hasCompactSupport
  simpa only [smul_eq_mul, H.transposeTest_apply G, mul_comm] using he

/-- Any two such kernel packages agree almost everywhere
(BB Theorem 6.18, printed p. 264). -/
theorem FundamentalKernel.unique_ae (K J : FundamentalKernel G H)
    (hQ : 2 < (G.homogeneousDimension : ℝ)) : (K : (Fin N → ℝ) → ℝ) =ᵐ[volume] J :=
  H.fundamental_unique_ae G hQ K.locallyIntegrable J.locallyIntegrable
    K.smooth_off_zero.continuousOn J.smooth_off_zero.continuousOn
    (K.homogeneous 2 (by norm_num)) (J.homogeneous 2 (by norm_num)) K.fundamental J.fundamental

end RothschildStein.H1
