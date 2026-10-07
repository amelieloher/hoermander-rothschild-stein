-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.GaugeWordBounds
public import RothschildStein.H3.RadialFieldChain
public import RothschildStein.H3.WordTranslation

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set Filter
open scoped Topology
variable {N q : ℕ} (G : HomogeneousGroup N)

/-- Every field derivative of the radial profile vanishes at the
origin, where the profile is constant on an open neighborhood. -/
theorem radialProfile_fieldDerivative_zero_origin (ν : G2.HomogeneousNorm G)
    (V : (Fin N → ℝ) → (Fin N → ℝ)) {t s : ℝ}
    (ht : 0 < t) (hts : t < s) :
    fieldDerivative V (quasiballProfile t s ∘ ν) 0 = 0 := by
  have hz : ν 0 = 0 := (ν.gauge.2.2.1 0).mpr rfl
  have hU : {y | ν y < t} ∈ 𝓝 (0 : Fin N → ℝ) :=
    (isOpen_lt ν.gauge.1 continuous_const).mem_nhds (by
      change ν 0 < t
      rw [hz]
      exact ht)
  have he : (quasiballProfile t s ∘ ν) =ᶠ[𝓝 (0 : Fin N → ℝ)]
      (fun _ => (1 : ℝ)) := by
    filter_upwards [hU] with y hy
    exact quasiballProfile_one hts hy.le
  unfold fieldDerivative
  rw [he.fderiv_eq, fderiv_const_apply, zero_apply]

/-- Horizontal cutoff derivatives have uniform inverse-gap bounds
at every center and every positive inner radius, with no analytic premises. -/
theorem exists_horizontal_cutoff_bound (H : H1.StandingHypotheses G q)
    (ν : G2.HomogeneousNorm G) (hν : ν.Smooth) (i : Fin q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x₀ : Fin N → ℝ, ∀ t s : ℝ,
      0 < t → t < s → ∀ x : Fin N → ℝ,
      |fieldDerivative (H.fields i.succ) (smoothQuasiballCutoff G ν x₀ t s) x| ≤
        C / (s - t) := by
  obtain ⟨M, hM, hb⟩ := gauge_horizontalDerivative_bound G H ν hν i
  obtain ⟨κ, hκ, hk⟩ := exists_quasiballProfile_derivative_bound (by norm_num : 0 < (1 : ℕ))
  have hrad : ∀ t s : ℝ, 0 < t → t < s → ∀ x : Fin N → ℝ,
      |fieldDerivative (H.fields i.succ) (quasiballProfile t s ∘ ν) x| ≤
        (2 * κ * M) / (s - t) := by
    intro t s ht hts x
    by_cases hx : x = 0
    · subst x
      rw [radialProfile_fieldDerivative_zero_origin G ν _ ht hts, abs_zero]
      positivity
    · rw [fieldDerivative_quasiballProfile G ν hν _ t s hx, abs_mul]
      have hk' : |deriv (quasiballProfile t s) (ν x)| ≤ κ * (2 / (s - t)) := by
        simpa only [iteratedDeriv_one, pow_one] using hk t s hts (ν x)
      have hprod := mul_le_mul hk' (hb x hx) (abs_nonneg _) (by positivity)
      exact hprod.trans_eq (by ring)
  refine ⟨2 * κ * M, by positivity, ?_⟩
  intro x₀ t s ht hts x
  have he := congrFun (wordDerivative_smoothQuasiballCutoff G ν hν H.fields
    (H.fields_smooth G) H.invariant [i.succ] x₀ ht hts) x
  simp only [wordDerivative, Function.comp_apply] at he
  rw [he]
  exact hrad t s ht hts _

end RothschildStein.H3
