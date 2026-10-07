-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.SobolevWordApproximation
public import RothschildStein.H3.InterpolationSum

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open MeasureTheory Filter
open scoped Topology ENNReal

/-- The weak Sobolev one-field interpolation estimate under the global
group-flow and density hypotheses. No smoothness of the Sobolev input is
assumed. -/
theorem sobolev_interpolation_single_of_flow_and_density {n m : ℕ} (G : HomogeneousGroup n)
    (w : Fin m → ℕ+) (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) (j : Fin m) (hj : (w j : ℕ) = 1)
    (E : ℝ → (Fin n → ℝ)) (hE : Continuous E) (hE0 : E 0 = 0)
    (hflow : ∀ x, IsIntegralCurve (fun t => G.mul x (E t)) (fun _ => X j))
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞)
    (hdensity : ∀ u, memSobolevX w X ⊤ 2 p u → Nonempty (SobolevWordApproximation w X p u))
    {u : (Fin n → ℝ) → ℝ} (hu : memSobolevX w X ⊤ 2 p u)
    {ε : ℝ} (hε : 0 < ε) :
    weakWordENorm X ⊤ [j] p u ≤ ENNReal.ofReal (2/ε) * eLpNorm u p volume +
      ENNReal.ofReal (ε/2) * weakWordENorm X ⊤ [j,j] p u := by
  classical
  have hj1 : [j] ∈ wordFamily w 2 := by
    simp [RothschildStein.S.mem_wordFamily_iff,wordWeight,hj]
  have hj2 : [j,j] ∈ wordFamily w 2 := by
    simp [RothschildStein.S.mem_wordFamily_iff,wordWeight,hj]
  obtain ⟨g,hg,hgp⟩ := hu.2 [j] hj1
  obtain ⟨h,hh,hhp⟩ := hu.2 [j,j] hj2
  have hup : MemLp u p volume := by simpa using hu.1
  have hgp' : MemLp g p volume := by simpa using hgp
  have hhp' : MemLp h p volume := by simpa using hhp
  obtain ⟨A⟩ := hdensity u hu
  have hb : ∀ k, eLpNorm (wordDerivative X [j] (A.functions k)) p volume ≤
      ENNReal.ofReal (2/ε) * eLpNorm (A.functions k) p volume +
      ENNReal.ofReal (ε/2) * eLpNorm (wordDerivative X [j,j] (A.functions k)) p volume := by
    intro k
    simpa only [wordDerivative] using
      (field_step_interpolation_compact_of_group_integralCurve G E hE hE0
        (X j) (hX j) hflow hp hpt (A.smooth k) (A.compact k) hε).2
  have hn := interpolation_bound_of_lp_approximation volume hp hup hgp' hhp'
    (fun k => by simpa only [wordDerivative] using
      memLp_wordDerivative_compact X hX [] (A.smooth k) (A.compact k) p)
    (fun k => memLp_wordDerivative_compact X hX [j] (A.smooth k) (A.compact k) p)
    (fun k => memLp_wordDerivative_compact X hX [j,j] (A.smooth k) (A.compact k) p)
    A.zero (A.word [j] hj1 g hg hgp') (A.word [j,j] hj2 h hh hhp') (2/ε) (ε/2) hb
  rw [RothschildStein.S.weakWordENorm_eq X ⊤ [j] p u g hg,
    RothschildStein.S.weakWordENorm_eq X ⊤ [j,j] p u h hh]
  simpa using hn

end RothschildStein.H3
