-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.CutoffCoefficientIndependence
public import RothschildStein.H1.SmoothShellCutoff
public import RothschildStein.H1.Integration

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter Topology
namespace RothschildStein.H1
variable {N q : ℕ} (G : HomogeneousGroup N) (H : StandingHypotheses G q)

/-- A punctured smooth function times a cutoff vanishing near zero is smooth. -/
theorem contDiff_punctured_mul_vanishing
    {f θ : (Fin N → ℝ) → ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f {(0 : Fin N → ℝ)}ᶜ)
    (hθ : ContDiff ℝ (⊤ : ℕ∞) θ)
    (he : θ =ᶠ[𝓝 (0 : Fin N → ℝ)] fun _ => 0) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => f x * θ x) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x = 0
  · subst x
    have hz : (fun x => f x * θ x) =ᶠ[𝓝 (0 : Fin N → ℝ)] fun _ => 0 := by
      filter_upwards [he] with y hy
      rw [hy, mul_zero]
    exact contDiffAt_const.congr_of_eventuallyEq hz
  · exact (hf.contDiffAt (isOpen_compl_singleton.mem_nhds (by simpa using hx))).mul hθ.contDiffAt

/-- Exterior coefficients at a common radius are independent
of arbitrary smooth cutoffs; no range bound is needed (BB pp. 281–283). -/
theorem StandingHypotheses.exteriorCoefficient_eq_sameRadius
    (i : Fin q) {f θ₁ θ₂ : (Fin N → ℝ) → ℝ} {R : ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f {(0 : Fin N → ℝ)}ᶜ)
    (h₁ : ContDiff ℝ (⊤ : ℕ∞) θ₁) (h₂ : ContDiff ℝ (⊤ : ℕ∞) θ₂)
    (he₁ : θ₁ =ᶠ[𝓝 (0 : Fin N → ℝ)] fun _ => 0)
    (he₂ : θ₂ =ᶠ[𝓝 (0 : Fin N → ℝ)] fun _ => 0)
    (hout₁ : ∀ x, R ≤ H.norm x → θ₁ x = 1)
    (hout₂ : ∀ x, R ≤ H.norm x → θ₂ x = 1) :
    (∫ x in {x | H.norm x ≤ R}, fieldDerivative (H.fields i.succ) (fun y => f y * θ₁ y) x) =
      ∫ x in {x | H.norm x ≤ R}, fieldDerivative (H.fields i.succ) (fun y => f y * θ₂ y) x := by
  let A := fun x => f x * θ₁ x
  let B := fun x => f x * θ₂ x
  have hA := contDiff_punctured_mul_vanishing hf h₁ he₁
  have hB := contDiff_punctured_mul_vanishing hf h₂ he₂
  have hs : tsupport (A - B) ⊆ {x | H.norm x ≤ R} := by
    apply closure_minimal
    · intro x hx
      by_contra hn
      have hh : R ≤ H.norm x := (lt_of_not_ge hn).le
      exact hx (by change f x * θ₁ x - f x * θ₂ x = 0; rw [hout₁ x hh, hout₂ x hh]; ring)
    · exact isClosed_le H.norm.gauge.1 continuous_const
  have hc : HasCompactSupport (A - B) :=
    (G2.isCompact_gauge_le H.norm.gauge R).of_isClosed_subset isClosed_closure hs
  let φ : TestFunction (⊤ : Opens (Fin N → ℝ)) ℝ (⊤ : ℕ∞) :=
    ⟨A - B, hA.sub hB, hc, subset_univ _⟩
  have hφ : (φ : (Fin N → ℝ) → ℝ) = A - B := rfl
  have hz := H.integral_field_test G ⊤ i.succ (fun _ => 1) contDiffOn_const φ
  rw [hφ] at hz
  have hzero : (∫ x, fieldDerivative (H.fields i.succ) (A - B) x) = 0 := by
    simpa only [Opens.coe_top, setIntegral_univ, fieldDerivative, fderiv_const_apply,
      zero_apply, zero_mul, integral_zero, one_mul, neg_eq_zero] using hz.symm
  have hd : fieldDerivative (H.fields i.succ) (A - B) =
      fun x => fieldDerivative (H.fields i.succ) A x - fieldDerivative (H.fields i.succ) B x := by
    funext x
    unfold fieldDerivative
    rw [fderiv_sub (hA.differentiable (by simp)).differentiableAt
      (hB.differentiable (by simp)).differentiableAt]
    rfl
  have hout (x) (hx : x ∉ {x | H.norm x ≤ R}) :
      fieldDerivative (H.fields i.succ) (A - B) x = 0 := by
    exact image_eq_zero_of_notMem_tsupport
      (fun h => hx (hs (S.tsupport_fieldDerivative_subset _ _ h)))
  have he := setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume) hout
  rw [hzero, hd] at he
  have hiA := (smooth_fieldDerivative _ (H.fields_smooth G i.succ) A hA).continuous.continuousOn.integrableOn_compact (μ := volume)
    (G2.isCompact_gauge_le H.norm.gauge R)
  have hiB := (smooth_fieldDerivative _ (H.fields_smooth G i.succ) B hB).continuous.continuousOn.integrableOn_compact (μ := volume)
    (G2.isCompact_gauge_le H.norm.gauge R)
  rw [integral_sub hiA hiB] at he
  exact sub_eq_zero.mp he

/-- A bounded interior cutoff with any prescribed enclosing gauge radius. -/
theorem exists_compactGaugeCutoff_atRadius {ν : (Fin N → ℝ) → ℝ}
    (hν : G.IsHomogeneousGauge ν) {R : ℝ} (hR : 0 < R) :
    ∃ η : (Fin N → ℝ) → ℝ, ContDiff ℝ (⊤ : ℕ∞) η ∧ HasCompactSupport η ∧
      η =ᶠ[𝓝 (0 : Fin N → ℝ)] (fun _ => 1) ∧
      (∀ x, R ≤ ν x → η x = 0) ∧ (∀ x, ‖η x‖ ≤ 1) := by
  let U : Opens (Fin N → ℝ) := ⟨{x | ν x < R}, isOpen_lt hν.1 continuous_const⟩
  obtain ⟨η, W, hW, hKW, he, hb⟩ := exists_test_eq_one_near_compact U
    (isCompact_singleton (x := (0 : Fin N → ℝ)))
    (by intro x hx; change ν x < R; rw [mem_singleton_iff.mp hx, (hν.2.2.1 0).mpr rfl]; exact hR)
  refine ⟨η, η.contDiff, η.hasCompactSupport, ?_, ?_, ?_⟩
  · filter_upwards [hW.mem_nhds (hKW (mem_singleton 0))] with x hx
    exact he x hx
  · intro x hx
    exact η.zero_on_compl (not_lt_of_ge hx)
  · intro x
    rw [Real.norm_of_nonneg (hb x).1]
    exact (hb x).2

end RothschildStein.H1
