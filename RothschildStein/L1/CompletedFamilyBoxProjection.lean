-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.CompletedFamilyCoefficientDomains
public import RothschildStein.L1.CompletedFamilyProjection
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
namespace RothschildStein.L1

/-- The actual paired families have the same horizontal
endpoint throughout the mixed weighted box. Both coefficient-domain
conditions follow from the box radii and the completed determinant. -/
theorem completed_family_box_projection {q n m s : ℕ} {w : Fin q → ℕ+}
    {Ω Uo : Set (Fin n → ℝ)} {Ul : Set (Fin (n+m) → ℝ)}
    (hΩ : IsOpen Ω) (hUoΩ : Uo ⊆ Ω) (hUlΩ : Ul ⊆ basePoint ⁻¹' Ω)
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (P : Fin q → Fin m → MvPolynomial (Fin (n+m)) ℝ)
    {zo : Fin n → ℝ} {zl : Fin (n+m) → ℝ} {tO tl : ℝ}
    (Fo : JointShortChartFamily (n := n) (s := s) w Uo X zo tO)
    (Fl : JointShortChartFamily (n := n+m) (s := s) w Ul (triangularLift X P) zl tl)
    (B : Fin n → G4.ShortWord w s) (J : Fin m → G4.ShortWord w s)
    (ξ : Fin (n+m) → ℝ)
    (hξo : basePoint ξ ∈ closedBall zo (Fo.R/16))
    (hξl : ξ ∈ closedBall zl (Fl.R/16))
    (hdet : G4.frameDet (G4.shortField w (triangularLift X P)) (Fin.addCases B J) ξ ≠ 0)
    {al au av b r : ℝ} (hal : 0 < al) (hala₀ : al ≤ Fl.a₀)
    (hau : 0 < au) (haua₀ : au ≤ Fo.a₀) (hav : 0 < av)
    (haual : au ≤ al) (haval : av ≤ al) (havb : av ≤ b) (hbau : b ≤ au)
    (hr : 0 < r) (hrl : r ≤ Fl.r₀) (hro : r ≤ Fo.r₀)
    {u : Fin n → ℝ} {v : Fin m → ℝ}
    (hu : u ∈ G4.weightedBox (G4.shortWeight w ∘ B) (au*r))
    (hv : v ∈ G4.weightedBox (G4.shortWeight w ∘ J) (av*r)) :
    basePoint (Fl.Φ (Fin.addCases B J) ((Fin.append (Fin.append u v) 0,ξ),1)) =
      Fo.Φ B ((Fin.append u (completionShift w J v),basePoint ξ),1) := by
  have hpl := completed_lifted_parameters_mem_flowDomain (q := q) (n := n) (m := m)
    (s := s) Fl B J hal hala₀ hau.le hav.le haual haval hr hrl hu hv
  have hpo := completed_original_parameters_mem_flowDomain (q := q) (n := n) (m := m)
    (s := s) Fo B J (G4.shortField w (triangularLift X P)) ξ hdet
    hau haua₀ hav havb hbau hr hro hu hv
  exact completed_family_projection (q := q) (n := n) (m := m) (s := s)
    hΩ hUoΩ hUlΩ X hX P Fo Fl B J ξ u v hξo hξl hpo hpl

end RothschildStein.L1
