-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.Distribution.AdjointTest
public import Mathlib.MeasureTheory.Measure.OpenPos

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
namespace RothschildStein.Distribution

/-- continuous local representatives of the same actual
real-test distribution agree pointwise on every open overlap. -/
theorem distributionRepresentatives_agree_on_overlap {N : ℕ}
    (Ω : Opens (Fin N → ℝ)) (T : Distribution Ω ℂ (⊤ : ℕ∞))
    (U V : Set (Fin N → ℝ)) (hU : IsOpen U) (hV : IsOpen V)
    (hUΩ : U ⊆ Ω) (_hVΩ : V ⊆ Ω)
    (f g : (Fin N → ℝ) → ℂ) (hf : ContinuousOn f U) (hg : ContinuousOn g V)
    (hTf : ∀ ψ : TestFunction Ω ℝ (⊤ : ℕ∞), tsupport ψ ⊆ U → T ψ = ∫ x, ψ x • f x)
    (hTg : ∀ ψ : TestFunction Ω ℝ (⊤ : ℕ∞), tsupport ψ ⊆ V → T ψ = ∫ x, ψ x • g x) :
    EqOn f g (U ∩ V) := by
  let W : Opens (Fin N → ℝ) := ⟨U ∩ V, hU.inter hV⟩
  have hfW : LocallyIntegrableOn f (W : Set (Fin N → ℝ)) volume :=
    (hf.mono inter_subset_left).locallyIntegrableOn W.isOpen.measurableSet
  have hgW : LocallyIntegrableOn g (W : Set (Fin N → ℝ)) volume :=
    (hg.mono inter_subset_right).locallyIntegrableOn W.isOpen.measurableSet
  have he : Distribution.ofFun W f volume (⊤ : ℕ∞) = Distribution.ofFun W g volume (⊤ : ℕ∞) := by
    ext ψ
    let φ : TestFunction Ω ℝ (⊤ : ℕ∞) :=
      ⟨ψ, ψ.contDiff, ψ.hasCompactSupport, ψ.tsupport_subset.trans (inter_subset_left.trans hUΩ)⟩
    have hφU : tsupport φ ⊆ U := ψ.tsupport_subset.trans inter_subset_left
    have hφV : tsupport φ ⊆ V := ψ.tsupport_subset.trans inter_subset_right
    rw [Distribution.ofFun_apply hfW, Distribution.ofFun_apply hgW]
    exact (hTf φ hφU).symm.trans (hTg φ hφV)
  have hae := Distribution.ofFun_injective hfW hgW he
  exact MeasureTheory.Measure.eqOn_open_of_ae_eq hae W.isOpen
    (hf.mono inter_subset_left) (hg.mono inter_subset_right)

end RothschildStein.Distribution
