-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.ExpandingCutoffLeibniz
public import RothschildStein.S.WeakSub

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped Topology ENNReal
namespace RothschildStein.H3

/-- Expanding cutoff multiplication approximates every selected weak
word in Lp. The limit is independent of the representative selection. -/
theorem tendsto_expandingCutoff_weakWord_eLpNorm {N q : ℕ}
    (G : HomogeneousGroup N) (H : H1.StandingHypotheses G q)
    (ν : G2.HomogeneousNorm G) (hν : ν.Smooth)
    (I : List (Fin (q+1))) (u : (Fin N → ℝ) → ℝ)
    (F : List (Fin (q+1)) → (Fin N → ℝ) → ℝ)
    (hF0 : F [] = u)
    (hF : ∀ J, J.Sublist I → hasWeakWordDeriv H.fields ⊤ J u (F J))
    {p : ℝ} (hp : 1 ≤ p)
    (hFLp : ∀ J, J.Sublist I → MemLp (F J) (ENNReal.ofReal p) volume) :
    Tendsto (fun R : ℝ => eLpNorm
      (fun x => S.leibnizWordValue H.fields I F
          (smoothQuasiballCutoff G ν 0 R (2*R)) x - F I x)
      (ENNReal.ofReal p) volume) atTop (𝓝 0) := by
  have hc := S.hasWeakWordDeriv_mul_word H.fields ⊤
    (fun i => (H.fields_smooth G i).contDiffOn) I u (fun _ => (1 : ℝ))
    contDiffOn_const F hF0 hF
  have he : (fun x => u x * (1 : ℝ)) = u := by funext x; exact mul_one _
  rw [he] at hc
  have hae := S.hasWeakWordDeriv_unique H.fields ⊤ hc (hF I (List.Sublist.refl I))
  simp only [Opens.coe_top, Measure.restrict_univ] at hae
  have ht := tendsto_expandingCutoff_leibniz_eLpNorm G H ν hν I F hp hFLp
  apply ht.congr
  intro R
  apply eLpNorm_congr_ae
  filter_upwards [hae] with x hx
  rw [hx]

end RothschildStein.H3
