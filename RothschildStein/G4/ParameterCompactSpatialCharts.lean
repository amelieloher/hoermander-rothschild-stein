-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.ParameterLocalChartData
public import RothschildStein.G4.CompactSpatialChartData

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
namespace RothschildStein.G4

/-- Actual compact external-family shifted charts on any compact
spatial patch inside the open domain. Finite spatial buffers supply common
positive constants without a global convexity requirement (BB p. 452). -/
theorem exists_parameter_compact_spatial_charts {P : Type*}
    [UniformSpace P] [CompactSpace P] (k n s h q : ℕ)
    (hn : 0 < n) (hs : 0 < s) (horder : q+1 = n*s+s) (hq : q+1 ≤ h)
    (w : Fin (k+1) → ℕ+) (Ω K : Set (Fin n → ℝ))
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (X : P → Fin (k+1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ p j, ContDiffOn ℝ (⊤ : ℕ∞) (X p j) Ω)
    (hstep : ∀ p, bracketStepOn Ω w (X p) s)
    (hjoint : ∀ J, ∀ i ≤ max (2*(n*s)+2*s) (max ((q+1)*s) (h+1+s)),
      ContinuousOn (fun z : P × (Fin n → ℝ) => iteratedFDeriv ℝ i (X z.1 J) z.2)
        (univ ×ˢ Ω))
    (t : ℝ) (ht : 0 < t) (ht1 : t < 1) :
    let m := Fintype.card (ShortWord w s)
    let wf : Fin m → ℕ+ := fun J => shortWeight w (shortIndex w J)
    let Zf := fun p J => shortField w (X p) (shortIndex w J)
    Nonempty (CompactSpatialChartData Ω K wf Zf t) := by
  intro m wf Zf
  exact exists_compact_spatial_chart_data hn Ω K hK wf Zf t
    (fun x hx => exists_parameter_local_chart_data k n s h q hn hs horder hq
      w Ω hΩ X hX hstep hjoint t ht ht1 (hKΩ hx))

end RothschildStein.G4
