-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.ClassicalWords
public import RothschildStein.H1.QuadraticTest

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set Filter TopologicalSpace MeasureTheory
open scoped Topology
namespace RothschildStein.H1
variable {N : ℕ}

/-- A field annihilates a cutoff equal to one near
zero, independently of its value at the origin. -/
theorem fieldDerivative_cutoff_eventually_zero
    (V : (Fin N → ℝ) → (Fin N → ℝ)) {θ : (Fin N → ℝ) → ℝ}
    (he : θ =ᶠ[𝓝 (0 : Fin N → ℝ)] fun _ => 1) :
    fieldDerivative V θ =ᶠ[𝓝 (0 : Fin N → ℝ)] fun _ => 0 := by
  have hd := fieldDerivative_eventuallyEq V he
  filter_upwards [hd] with x hx
  rw [hx]
  change fderiv ℝ (fun _ : Fin N → ℝ => (1 : ℝ)) x (V x) = 0
  rw [fderiv_const_apply]
  rfl

/-- Pairing a compact cutoff derivative with a
punctured continuous kernel is absolutely integrable. -/
theorem integrable_mul_fieldDerivative_cutoff
    (V : (Fin N → ℝ) → (Fin N → ℝ)) (hV : ContDiff ℝ (⊤ : ℕ∞) V)
    {f θ : (Fin N → ℝ) → ℝ} (hf : ContinuousOn f {(0 : Fin N → ℝ)}ᶜ)
    (hθ : ContDiff ℝ (⊤ : ℕ∞) θ) (hs : HasCompactSupport θ)
    (he : θ =ᶠ[𝓝 (0 : Fin N → ℝ)] fun _ => 1) :
    Integrable (fun x => f x * fieldDerivative V θ x) := by
  let U : Opens (Fin N → ℝ) := ⟨{0}ᶜ, isOpen_compl_singleton⟩
  have hz : (0 : Fin N → ℝ) ∉ tsupport (fieldDerivative V θ) :=
    notMem_tsupport_iff_eventuallyEq.mpr (fieldDerivative_cutoff_eventually_zero V he)
  have hd : HasCompactSupport (fieldDerivative V θ) :=
    hs.of_isClosed_subset isClosed_closure (S.tsupport_fieldDerivative_subset V θ)
  let φ : TestFunction U ℝ (⊤ : ℕ∞) :=
    ⟨fieldDerivative V θ, smooth_fieldDerivative V hV θ hθ, hd,
      by intro x hx; change x ∈ ({0}ᶜ : Set (Fin N → ℝ));
         simp only [mem_compl_iff, mem_singleton_iff]; intro he; exact hz (he ▸ hx)⟩
  exact S.integrable_mul_test U (hf.locallyIntegrableOn isOpen_compl_singleton.measurableSet) φ

end RothschildStein.H1
