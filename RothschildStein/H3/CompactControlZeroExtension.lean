-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.CompactGaugeHolderInput

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped ENNReal
namespace RothschildStein.H3

/-- The fixed compact intrinsic input has a continuous compact zero
extension with finite full control norm. -/
theorem continuous_compact_finite_zeroExtension_of_memHolderXCompact {N m : ℕ}
    (G : HomogeneousGroup N) (w : Fin m → ℕ+)
    (X : Fin m → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i))
    (C : G2.ControlNormConclusion G w X) (U : Opens (Fin N → ℝ)) (k : ℕ)
    {α : ℝ} (hα : 0 < α) {f : (Fin N → ℝ) → ℝ}
    (hf : memHolderXCompact w X (controlDistance univ w X) U k α f) :
    let f₀ := (U : Set (Fin N → ℝ)).indicator f
    Continuous f₀ ∧ HasCompactSupport f₀ ∧ tsupport f₀ ⊆ U ∧
      holderENorm (controlDistance univ w X) α univ f₀ < ⊤ := by
  obtain ⟨K, hKU, jet, hzero, hj⟩ :=
    exists_global_holder_intrinsic_jets_of_memHolderXCompact_of_controlNorm G U w X hX C k hα hf
  have hn : wordWeight w [] ≤ k := by simp [wordWeight]
  have hh := hj [] hn
  obtain ⟨A, hA⟩ := hh.2.2.2.2
  have hfinite := holderENorm_finite_of_compact_gauge_holder G w X C hα.le
    hh.2.1 hh.2.2.1 hA
  rw [hzero] at hh hfinite
  exact ⟨hh.2.1, hh.2.2.1, hh.2.2.2.1.trans hKU, hfinite⟩

end RothschildStein.H3
