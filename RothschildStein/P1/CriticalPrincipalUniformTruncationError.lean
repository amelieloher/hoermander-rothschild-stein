-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.CriticalFamilyUniformTruncationError
public import RothschildStein.P1.ContinuityReconstruction
public import RothschildStein.P1.StandardFrame

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped Topology
namespace RothschildStein.P1.LiftedChart
variable {n k m q : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)}
  {hΩ : IsOpen Ω} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {F : KernelFrame (n + m)}
  {H : H1.StandingHypotheses C.G q} {K : H1.FundamentalKernel C.G H}
  {hQ : 2 < (C.G.homogeneousDimension : ℝ)}

/-- Each actual critical principal term, including
both endpoint cutoffs, has uniform O(ε) convergence to its prescribed
sharp principal value on compact patches of a standard frame. -/
theorem exists_criticalPrincipal_uniform_truncation_error_bound
    (hF : C.IsStandardFrame F H K hQ) (t : PrincipalTerm F) (hd : t.degree = 2)
    (φ : TestFunction F.V ℝ (⊤ : ℕ∞))
    {L : Set (Fin (n + m) → ℝ)} (hL : IsCompact L)
    (hLV : L ⊆ (F.V : Set (Fin (n + m) → ℝ))) :
    ∃ r A : ℝ, 0 < r ∧ 0 ≤ A ∧ ∀ ξ ∈ L, ∀ ε : ℝ, 0 < ε → ε < r →
      ‖(∫ η in {η | ε < F.rho ξ η}, t.kernel ξ η * φ η) -
        limUnder (𝓝[>] (0 : ℝ)) (fun ε : ℝ => ∫ η in {η | ε < F.rho ξ η},
          t.kernel ξ η * φ η)‖ ≤ A * ε := by
  have hVU : (F.V : Set (Fin (n + m) → ℝ)) ⊆ C.U :=
    subset_closure.trans hF.lifted.closure_subset
  let ψ : TestFunction C.chartOpens ℝ (⊤ : ℕ∞) :=
    ⟨fun η => t.b η * φ η, t.b.contDiff.mul φ.contDiff,
      φ.hasCompactSupport.mul_left,
      tsupport_mul_subset_right.trans (φ.tsupport_subset.trans hVU)⟩
  let SF := t.toSplitFamily hF.lifted.G_eq hd
  have hΓ := hF.lifted.pole_smooth t.star
  have hh : ∀ r : ℝ, 0 < r → ∀ u : Fin (n + m) → ℝ, u ≠ 0 →
      F.pole t.star (C.G.dilate r u) = r ^ (2 - (C.G.homogeneousDimension : ℝ)) * F.pole t.star u :=
    hF.lifted.pole_homogeneous t.star
  obtain ⟨r, A, hr, hA, hb⟩ := C.exists_criticalFamily_uniform_truncation_error_bound SF
    (F.pole t.star) hΓ hh H.norm.gauge ψ hL (hLV.trans hVU)
  obtain ⟨B, hB⟩ := t.a.hasCompactSupport.exists_bound_of_continuous t.a.contDiff.continuous
  refine ⟨r, max B 0 * A, hr, mul_nonneg (le_max_right _ _) hA, ?_⟩
  intro ξ hξ ε hε hεr
  let raw := fun ε : ℝ => ∫ η in {η | ε < H.norm (C.Θ η ξ)},
    (t.D ξ η).apply (F.pole t.star) (C.Θ η ξ) * ψ η
  have he (ε : ℝ) : (∫ η in {η | ε < F.rho ξ η}, t.kernel ξ η * φ η) = t.a ξ * raw ε := by
    dsimp only [raw]
    simp only [KernelFrame.rho, hF.lifted.Θ_eq, hF.gauge_eq]
    rw [← integral_const_mul]
    apply integral_congr_ae
    apply Eventually.of_forall
    intro η
    simp only [PrincipalTerm.kernel, hF.lifted.Θ_eq, ψ, TestFunction.coe_mk]
    ring
  have htRaw := (C.criticalVariableFamily_inputChart_principalValue SF (F.pole t.star)
    hΓ hh (hVU (hLV hξ)) H.norm.gauge ψ).2
  have ht := (htRaw.const_mul (t.a ξ)).congr'
    (Eventually.of_forall (fun ε => (he ε).symm))
  have hePV : limUnder (𝓝[>] (0 : ℝ)) (fun ε : ℝ =>
      ∫ η in {η | ε < F.rho ξ η}, t.kernel ξ η * φ η) =
      t.a ξ * limUnder (𝓝[>] (0 : ℝ)) raw := by
    rw [ht.limUnder_eq, htRaw.limUnder_eq]
  rw [he ε, hePV, ← mul_sub, norm_mul]
  have hbRaw : ‖raw ε - limUnder (𝓝[>] (0 : ℝ)) raw‖ ≤ A * ε := hb ξ hξ ε hε hεr
  calc
    _ ≤ max B 0 * (A * ε) :=
      mul_le_mul ((hB ξ).trans (le_max_left _ _)) hbRaw (norm_nonneg _)
        (le_max_right _ _)
    _ = (max B 0 * A) * ε := by ring

end RothschildStein.P1.LiftedChart
