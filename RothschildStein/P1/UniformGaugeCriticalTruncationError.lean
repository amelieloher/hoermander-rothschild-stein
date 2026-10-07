-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.UniformGaugeCriticalTestBound
public import RothschildStein.H1.PrincipalValueErrorIdentity
public import RothschildStein.H1.PrincipalValueScalarPairing
public import RothschildStein.G2.PowerBochner

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
namespace RothschildStein.P1
variable {N : ℕ}

/-- The actual subtracted small-ball integral
has a uniform O(ε) bound for a compact family of model centers. -/
theorem exists_uniformGaugeCritical_smallIntegral_bound
    (G : HomogeneousGroup N) {ν : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    (Ψ : (Fin N → ℝ) → (Fin N → ℝ) → (Fin N → ℝ) → ℝ)
    (hcΨ : ContinuousOn (kernelUncurry Ψ) {z | z.2.2 ≠ 0})
    (hhom : ∀ ξ η, ∀ r : ℝ, 0 < r → ∀ u, u ≠ 0 →
      Ψ ξ η (G.dilate r u) = r ^ (-(G.homogeneousDimension : ℝ)) * Ψ ξ η u)
    {U : Set (Fin N → ℝ)} (hU : IsOpen U)
    (ψ : (Fin N → ℝ) × (Fin N → ℝ) → ℝ)
    (hψ : ContDiffOn ℝ 1 ψ (U ×ˢ (univ : Set (Fin N → ℝ))))
    {K : Set (Fin N → ℝ)} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ ξ ∈ K, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ‖∫ u in {u | ν u ≤ ε}, Ψ ξ ξ u * (ψ (ξ, u) - ψ (ξ, 0))‖ ≤ A * ε := by
  obtain ⟨M, hM, hb⟩ := exists_uniformGaugeCriticalTest_near_bound G hν Ψ hcΨ hhom hU ψ hψ hK hKU
  let Q : ℝ := G.homogeneousDimension
  let V : ℝ := (volume {u | ν u < 1}).toReal
  refine ⟨M * (Q * V), mul_nonneg hM (mul_nonneg (Nat.cast_nonneg _) ENNReal.toReal_nonneg), ?_⟩
  intro ξ hξ ε hε hε1
  have hi : IntegrableOn (fun u => ν u ^ (1 - Q)) {u | ν u ≤ ε} volume := by
    have hp := (G2.integrableOn_power_near_iff hν (Q - 1) hε).mpr (by dsimp only [Q]; linarith)
    have he : -(Q - 1) = 1 - Q := by ring
    rw [he] at hp
    exact hp
  have hnorm : ‖∫ u in {u | ν u ≤ ε}, Ψ ξ ξ u * (ψ (ξ, u) - ψ (ξ, 0))‖ ≤
      ∫ u in {u | ν u ≤ ε}, M * ν u ^ (1 - Q) := by
    apply norm_integral_le_of_norm_le (hi.const_mul M)
    filter_upwards [ae_restrict_mem (isClosed_le hν.1 continuous_const).measurableSet] with u hu
    by_cases h0 : u = 0
    · subst u
      simp only [sub_self, mul_zero, norm_zero]
      exact mul_nonneg hM (Real.rpow_nonneg (hν.2.1 0) _)
    · exact hb ξ hξ u h0 (hu.trans hε1)
  have he : (∫ u in {u | ν u ≤ ε}, ν u ^ (1 - Q)) = Q * V * ε := by
    have hp := G2.integral_power_near hν (β := Q - 1) (by dsimp only [Q]; linarith) hε
    have hneg : -(Q - 1) = 1 - Q := by ring
    have hdiff : (G.homogeneousDimension : ℝ) - (Q - 1) = 1 := by dsimp only [Q]; ring
    simpa only [hneg, hdiff, Real.rpow_one, div_one, Q, V] using hp
  calc
    _ ≤ ∫ u in {u | ν u ≤ ε}, M * ν u ^ (1 - Q) := hnorm
    _ = M * (Q * V * ε) := by rw [integral_const_mul, he]
    _ = (M * (Q * V)) * ε := by ring

/-- The prescribed scalar principal-value
truncations converge uniformly with an actual O(ε) error on every
compact parameter patch. No finite-truncation bound is assumed. -/
theorem exists_uniformGaugeCritical_truncation_error_bound
    (G : HomogeneousGroup N) {ν : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    (Ψ : (Fin N → ℝ) → (Fin N → ℝ) → (Fin N → ℝ) → ℝ)
    (hcΨ : ContinuousOn (kernelUncurry Ψ) {z | z.2.2 ≠ 0})
    (hhom : ∀ ξ η, ∀ r : ℝ, 0 < r → ∀ u, u ≠ 0 →
      Ψ ξ η (G.dilate r u) = r ^ (-(G.homogeneousDimension : ℝ)) * Ψ ξ η u)
    (hcancel : ∀ ξ, H1.HasVanishingShellIntegrals ν (Ψ ξ ξ))
    {U : Set (Fin N → ℝ)} (hU : IsOpen U)
    (ψ : (Fin N → ℝ) × (Fin N → ℝ) → ℝ)
    (hψ : ContDiffOn ℝ (⊤ : ℕ∞) ψ (U ×ˢ (univ : Set (Fin N → ℝ))))
    {K : Set (Fin N → ℝ)} (hK : IsCompact K) (hKU : K ⊆ U)
    {L : Set (Fin N → ℝ)} (hL : IsCompact L)
    (hs : ∀ ξ ∈ K, ∀ u, u ∉ L → ψ (ξ, u) = 0) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ ξ ∈ K, ∀ ε : ℝ, 0 < ε → ε < 1 →
      ‖(∫ u in {u | ε < ν u}, Ψ ξ ξ u * ψ (ξ, u)) -
        H1.principalValueConvolution G ν (Ψ ξ ξ) ((fun u => ψ (ξ, u)) ∘ G.inv) 0‖ ≤ A * ε := by
  obtain ⟨A, hA, hb⟩ := exists_uniformGaugeCritical_smallIntegral_bound G hν Ψ hcΨ hhom
    hU ψ (hψ.of_le (by simp)) hK hKU
  refine ⟨A, hA, ?_⟩
  intro ξ hξ ε hε hε1
  have hcφ : ContDiff ℝ (⊤ : ℕ∞) (fun u => ψ (ξ, u)) := by
    apply contDiffOn_univ.mp
    exact hψ.comp (contDiffOn_const.prodMk contDiffOn_id)
      (fun u (_ : u ∈ (univ : Set (Fin N → ℝ))) => ⟨hKU hξ, mem_univ u⟩)
  have hsφ : HasCompactSupport (fun u => ψ (ξ, u)) :=
    hL.of_isClosed_subset isClosed_closure
      (closure_minimal (fun u hu => by by_contra hn; exact hu (hs ξ hξ u hn)) hL.isClosed)
  obtain ⟨hcInv, hsInv⟩ := H1.compactSmooth_comp_inv G hcφ hsφ
  have hcKernel : ContinuousOn (Ψ ξ ξ) {(0 : Fin N → ℝ)}ᶜ :=
    hcΨ.comp (continuous_const.prodMk (continuous_const.prodMk continuous_id)).continuousOn
      (fun u hu => hu)
  have he := H1.principalValueTruncation_sub_eq_neg_smallIntegral G hν hcKernel
    (hhom ξ ξ) (hcancel ξ) (hcInv.of_le (by simp)) hsInv hε hε1 (0 : Fin N → ℝ)
  simp only [H1.principalValueTruncation, Function.comp_apply, G2.zero_mul, G2.inv_inv,
    G2.inv_zero] at he
  rw [he, norm_neg]
  exact hb ξ hξ ε hε hε1.le

end RothschildStein.P1
