-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.OperatorIntegrationByParts
public import RothschildStein.H1.TransposeLocality
public import RothschildStein.H1.LocalizedKernelSmoothness

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped Topology
namespace RothschildStein.H1
variable {N q : ℕ} (G : HomogeneousGroup N)

private theorem integrable_kernel_transpose_test (H : StandingHypotheses G q)
    {Γ : (Fin N → ℝ) → ℝ} (hΓ : LocallyIntegrable Γ)
    {Ω : Opens (Fin N → ℝ)} (φ : TestFunction Ω ℝ (⊤ : ℕ∞)) :
    Integrable (fun x => Γ x * sumSquaresWithDriftTranspose H.fields φ x) := by
  let ψ := sumSquaresWithDriftTransposeTest Ω H.fields
    (fun i => (H.fields_smooth G i).contDiffOn) φ
  have hp : (ψ : (Fin N → ℝ) → ℝ) = sumSquaresWithDriftTranspose H.fields φ :=
    funext (H.transposeTest_apply G Ω φ)
  exact hΓ.integrable_smul_right_of_hasCompactSupport
    (hp ▸ ψ.contDiff.continuous) (hp ▸ ψ.hasCompactSupport)

/-- The nested cutoffs turn the complete local fundamental
identity into the unscaled global identity with the actual error kernel
(BB p. 265; cutoff and punctured integration by parts). -/
theorem StandingHypotheses.localizedKernel_pairing
    (H : StandingHypotheses G q) (Ω : Opens (Fin N → ℝ))
    {γ : (Fin N → ℝ) → ℝ}
    (hγ : LocallyIntegrableOn γ (Ω : Set (Fin N → ℝ)) volume)
    (hcγ : ContDiffOn ℝ (⊤ : ℕ∞) γ ((Ω : Set (Fin N → ℝ)) ∩ {(0 : Fin N → ℝ)}ᶜ))
    (η₁ η₂ : TestFunction Ω ℝ (⊤ : ℕ∞))
    (hη₁ : ∀ x ∈ tsupport (η₂ : (Fin N → ℝ) → ℝ), η₁ x = 1)
    (hη₂ : (η₂ : (Fin N → ℝ) → ℝ) =ᶠ[𝓝 (0 : Fin N → ℝ)] 1)
    (hlocal : ∀ ψ : TestFunction Ω ℝ (⊤ : ℕ∞),
      (∫ x, γ x * sumSquaresWithDriftTranspose H.fields ψ x) = ψ 0)
    (φ : (Fin N → ℝ) → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hsφ : HasCompactSupport φ) :
    (∫ x, (γ x * η₁ x) * sumSquaresWithDriftTranspose H.fields φ x) = φ 0 +
      ∫ x, sumSquaresWithDrift H.fields (fun y => γ y * η₁ y) x * (1 - η₂ x) * φ x := by
  let Γ := fun x => γ x * η₁ x
  have hiΓ : Integrable Γ := S.integrable_mul_test Ω hγ η₁
  have hcΓ := contDiffOn_localizedKernel Ω hcγ η₁
  let A : TestFunction Ω ℝ (⊤ : ℕ∞) := testMultiplierOn Ω φ hφ.contDiffOn η₂
  let B : (Fin N → ℝ) → ℝ := fun x => φ x - A x
  have hB : ContDiff ℝ (⊤ : ℕ∞) B := hφ.sub A.contDiff
  have hsB : HasCompactSupport B := hsφ.sub A.hasCompactSupport
  have hzB : B =ᶠ[𝓝 (0 : Fin N → ℝ)] 0 := by
    filter_upwards [hη₂] with x hx
    change φ x - η₂ x * φ x = 0
    change η₂ x = 1 at hx
    rw [hx, one_mul, sub_self]
  have hBs : tsupport B ⊆ {(0 : Fin N → ℝ)}ᶜ := by
    intro x hx
    change x ≠ 0
    intro hzero
    subst x
    exact (notMem_tsupport_iff_eventuallyEq.mpr hzB) hx
  let U : Opens (Fin N → ℝ) := ⟨{(0 : Fin N → ℝ)}ᶜ, isOpen_compl_singleton⟩
  let Btest : TestFunction U ℝ (⊤ : ℕ∞) := ⟨B, hB, hsB, hBs⟩
  have hA : (∫ x, Γ x * sumSquaresWithDriftTranspose H.fields A x) = φ 0 := by
    calc
      _ = ∫ x, γ x * sumSquaresWithDriftTranspose H.fields A x := by
        apply integral_congr_ae
        apply Eventually.of_forall
        intro x
        by_cases hx : x ∈ tsupport (η₂ : (Fin N → ℝ) → ℝ)
        · change (γ x * η₁ x) * _ = _
          rw [hη₁ x hx, mul_one]
        · have ha : tsupport (A : (Fin N → ℝ) → ℝ) ⊆ tsupport (η₂ : (Fin N → ℝ) → ℝ) :=
            tsupport_mul_subset_left
          have hp := image_eq_zero_of_notMem_tsupport (fun ht => hx
            (ha (tsupport_sumSquaresTranspose_subset H.fields A ht)))
          change Γ x * sumSquaresWithDriftTranspose H.fields A x =
            γ x * sumSquaresWithDriftTranspose H.fields A x
          rw [hp, mul_zero, mul_zero]
      _ = A 0 := hlocal A
      _ = φ 0 := by
        have he : η₂ 0 = 1 := hη₂.self_of_nhds
        change η₂ 0 * φ 0 = φ 0
        rw [he, one_mul]
  have hBpair : (∫ x, Γ x * sumSquaresWithDriftTranspose H.fields B x) =
      ∫ x, sumSquaresWithDrift H.fields Γ x * B x := by
    have he := H.integral_operator_test_on G U Γ hcΓ Btest
    have hl : (∫ x in (U : Set (Fin N → ℝ)), sumSquaresWithDrift H.fields Γ x * Btest x) =
        ∫ x, sumSquaresWithDrift H.fields Γ x * B x :=
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
        simp only [Btest.zero_on_compl hx, Pi.zero_apply, mul_zero])
    have hr : (∫ x in (U : Set (Fin N → ℝ)), Γ x * sumSquaresWithDriftTranspose H.fields Btest x) =
        ∫ x, Γ x * sumSquaresWithDriftTranspose H.fields B x :=
      setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
        have hp := image_eq_zero_of_notMem_tsupport (fun ht => hx
          (Btest.tsupport_subset (tsupport_sumSquaresTranspose_subset H.fields Btest ht)))
        rw [hp, mul_zero])
    rw [hl, hr] at he
    exact he.symm
  have hpart : φ = (A : (Fin N → ℝ) → ℝ) + B := by funext x; change φ x = A x + (φ x - A x); ring
  have hiA := integrable_kernel_transpose_test G H hiΓ.locallyIntegrable A
  have hiB : Integrable (fun x => Γ x * sumSquaresWithDriftTranspose H.fields B x) :=
    integrable_kernel_transpose_test G H hiΓ.locallyIntegrable Btest
  have hp : ∀ x, sumSquaresWithDriftTranspose H.fields φ x =
      sumSquaresWithDriftTranspose H.fields A x + sumSquaresWithDriftTranspose H.fields B x := by
    intro x
    rw [hpart]
    exact H.transpose_add G A.contDiff hB x
  change (∫ x, Γ x * sumSquaresWithDriftTranspose H.fields φ x) = _
  simp_rw [hp, mul_add]
  rw [integral_add hiA hiB, hA, hBpair]
  congr 1
  apply integral_congr_ae
  apply Eventually.of_forall
  intro x
  change sumSquaresWithDrift H.fields Γ x * (φ x - η₂ x * φ x) = _
  ring

end RothschildStein.H1
