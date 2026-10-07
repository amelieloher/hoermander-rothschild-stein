-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.UniformWordApproximation

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set Filter
namespace RothschildStein.S
variable {n : ℕ} {ι : Type*}

/-- Uniform convergence on an interior set extends to a
larger local domain when both the limit and the approximants vanish
outside the interior set. Support confinement is eventual
(BB Thm 2.20, p. 86; compact-support assembly). -/
theorem tendstoUniformlyOn_of_eventual_support
    {l : Filter ι} {U V : Set (Fin n → ℝ)}
    {F : ι → (Fin n → ℝ) → ℝ} {f : (Fin n → ℝ) → ℝ}
    (ht : TendstoUniformlyOn F f l U)
    (hf : ∀ x ∈ V \ U,f x = 0)
    (hs : ∀ᶠ i in l,tsupport (F i) ⊆ U) :
    TendstoUniformlyOn F f l V := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro η hη
  filter_upwards [(Metric.tendstoUniformlyOn_iff.mp ht) η hη,hs] with i hi hsi
  intro x hx
  by_cases hu : x ∈ U
  · exact hi x hu
  · have he : F i x = 0 := image_eq_zero_of_notMem_tsupport
      (fun hm => hu (hsi hm))
    simpa only [hf x ⟨hx,hu⟩,he,dist_self] using hη

end RothschildStein.S
