-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.FieldCutoffSupport
public import RothschildStein.H1.SmallDilationTransportBound

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory Filter Topology
namespace RothschildStein.H1
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Step 3: the actual compact-cutoff derivative pairing
has a uniform Cε transport error, with only punctured continuity of
the original kernel. -/
theorem exists_fieldCutoff_transport_bound
    {V : (Fin N → ℝ) → (Fin N → ℝ)} (hV : ContDiff ℝ (⊤ : ℕ∞) V)
    {f η ψ ν : (Fin N → ℝ) → ℝ} (hν : G.IsHomogeneousGauge ν)
    (hf : ContinuousOn f {(0 : Fin N → ℝ)}ᶜ)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hsη : HasCompactSupport η)
    (heη : η =ᶠ[𝓝 (0 : Fin N → ℝ)] fun _ => 1)
    (hcψ : ContDiff ℝ 1 ψ) (hsψ : HasCompactSupport ψ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ∀ x,
      ‖∫ v, (f v * fieldDerivative V η v) *
        (ψ (G.mul x (G.inv (G.dilate ε v))) - ψ x)‖ ≤ C * ε := by
  have ha := integrable_mul_fieldDerivative_cutoff V hV hf hη hsη heη
  obtain ⟨M, hM⟩ := hsη.isCompact.bddAbove_image hν.1.continuousOn
  let R := max 1 M
  have hR : 0 < R := zero_lt_one.trans_le (le_max_left _ _)
  have hvanish : ∀ v, R < ν v → f v * fieldDerivative V η v = 0 := by
    intro v hv
    have hsupp : v ∉ tsupport η := by
      intro h
      exact (not_le_of_gt hv) ((hM ⟨v, h, rfl⟩).trans (le_max_right _ _))
    have hd : v ∉ tsupport (fieldDerivative V η) :=
      fun h => hsupp (S.tsupport_fieldDerivative_subset V η h)
    rw [image_eq_zero_of_notMem_tsupport hd, mul_zero]
  exact exists_smallDilationTransport_integral_bound G hν ha hR hvanish hcψ hsψ

end RothschildStein.H1
