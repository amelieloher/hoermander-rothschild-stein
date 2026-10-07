-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.SobolevFiniteCoverEstimate
public import RothschildStein.H3.BufferedGaugeCover

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
namespace RothschildStein.H3
open Set MeasureTheory TopologicalSpace
open scoped ENNReal BigOperators

/-- The interior Sobolev estimate follows from global control-norm
comparison and the uniform half-radius estimate. Its positive constant is
chosen before the input function or weak operator data. -/
theorem interior_estimate_of_controlNorm_and_halfRadius {n q m : ℕ}
    (G : HomogeneousGroup n) (ν : G2.HomogeneousNorm G)
    (X : Fin (q+1) → (Fin n → ℝ) → (Fin n → ℝ))
    {w : Fin m → ℕ+} {Y : Fin m → (Fin n → ℝ) → (Fin n → ℝ)}
    (H : G2.ControlNormConclusion G w Y)
    (a B : ℝ) (ha : 0 < a) (hB : 0 < B)
    (hcmp : ∀ z, a*H.norm z ≤ ν z ∧ ν z ≤ B*H.norm z)
    (Ω U : Opens (Fin n → ℝ)) (hcompact : IsCompact (closure (U : Set (Fin n → ℝ))))
    (hU : closure (U : Set (Fin n → ℝ)) ⊆ Ω)
    (p : ℝ≥0∞) (hp : 1 ≤ p) (A : ℝ) (hA : 0 ≤ A)
    (hest : HalfRadiusEstimate G ν X p A) :
    ∃ c : ℝ, 0 < c ∧ ∀ u : (Fin n → ℝ) → ℝ,
      memSobolevX driftWeight X Ω 2 p u →
      ∀ D : WeakDriftOperatorData X Ω p u,
        (sobolevXENorm driftWeight X U 2 p u).toReal ≤
          c*((eLpNorm D.operator p (volume.restrict (Ω : Set (Fin n → ℝ)))).toReal+
            (eLpNorm u p (volume.restrict (Ω : Set (Fin n → ℝ)))).toReal) := by
  classical
  obtain ⟨r,θ,hr,_,_,s,hcover,hballs,_⟩ := buffered_quasiBall_cover_of_controlNorm
    H ν ha hB hcmp hcompact Ω.isOpen hU
  have hratio : 1 ≤ B/a := (smoothGauge_quasitriangle_of_controlNorm H ν ha hB hcmp).1
  have hratioPos : 0 < B/a := div_pos hB ha
  let R := r/(B/a)
  have hR : 0 < R := div_pos hr hratioPos
  have hRr : R ≤ r := by
    apply (div_le_iff₀ hratioPos).mpr
    nlinarith
  have hballsR : ∀ i ∈ s, (quasiballDomain G ν i.1 R : Set (Fin n → ℝ)) ⊆ Ω := by
    intro i hi
    exact (quasiballDomain_subset_of_le G ν i.1 (hRr.trans (by linarith))).trans (hballs i hi)
  have hcoverR : ∀ x ∈ U, ∃ i ∈ s, x ∈ quasiballDomain G ν i.1 (R/2) := by
    intro x hx
    obtain ⟨i,hi,hxi⟩ := hcover x (subset_closure hx)
    refine ⟨i,hi,?_⟩
    have he : r/(2*(B/a)) = R/2 := by dsimp only [R]; ring
    change x ∈ G2.gaugeBall G ν i.1 (R/2)
    simpa only [he] using hxi
  let L : ℝ := (s.card : ℝ)*((wordFamily (driftWeight (q := q)) 2).card : ℝ)*(1+R+R^2)*A
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  refine ⟨1+L*(1+R⁻¹^2), by positivity, ?_⟩
  intro u hu D
  have hb := finite_cover_estimate_of_halfRadius G ν X Ω U (subset_closure.trans hU)
    p hp A hA hest s (fun i => i.1) R hR hballsR hcoverR u hu D
  have hF : 0 ≤ (eLpNorm D.operator p (volume.restrict (Ω : Set (Fin n → ℝ)))).toReal := ENNReal.toReal_nonneg
  have hu0 : 0 ≤ (eLpNorm u p (volume.restrict (Ω : Set (Fin n → ℝ)))).toReal := ENNReal.toReal_nonneg
  have hscale : (eLpNorm D.operator p (volume.restrict (Ω : Set (Fin n → ℝ)))).toReal+
      R⁻¹^2*(eLpNorm u p (volume.restrict (Ω : Set (Fin n → ℝ)))).toReal ≤
      (1+R⁻¹^2)*((eLpNorm D.operator p (volume.restrict (Ω : Set (Fin n → ℝ)))).toReal+
        (eLpNorm u p (volume.restrict (Ω : Set (Fin n → ℝ)))).toReal) := by
    nlinarith [mul_nonneg (sq_nonneg R⁻¹) hF]
  have hm := mul_le_mul_of_nonneg_left hscale hL
  change _ ≤ L* _ at hb
  exact hb.trans (hm.trans (by nlinarith))

end RothschildStein.H3
