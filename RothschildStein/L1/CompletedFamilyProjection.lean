-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.JointShortChartFamilyProperties
public import RothschildStein.L1.CompletedChartFamilyProjection
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
namespace RothschildStein.L1

/-- The two constructed joint families give the completed
lifted and shifted original charts the same horizontal endpoint,
from coefficient-domain membership and compact-center membership
alone. Their actual ODE and initial data are extracted from the
families (BB pp. 520–521). -/
theorem completed_family_projection {q n m s : ℕ} {w : Fin q → ℕ+}
    {Ω Uo : Set (Fin n → ℝ)} {Ul : Set (Fin (n+m) → ℝ)}
    (hΩ : IsOpen Ω) (hUoΩ : Uo ⊆ Ω) (hUlΩ : Ul ⊆ basePoint ⁻¹' Ω)
    (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (P : Fin q → Fin m → MvPolynomial (Fin (n+m)) ℝ)
    {zo : Fin n → ℝ} {zl : Fin (n+m) → ℝ} {tO tl : ℝ}
    (Fo : JointShortChartFamily (s := s) w Uo X zo tO)
    (Fl : JointShortChartFamily (s := s) w Ul (triangularLift X P) zl tl)
    (B : Fin n → G4.ShortWord w s) (J : Fin m → G4.ShortWord w s)
    (ξ : Fin (n+m) → ℝ) (u : Fin n → ℝ) (v : Fin m → ℝ)
    (hξo : basePoint ξ ∈ closedBall zo (Fo.R/16))
    (hξl : ξ ∈ closedBall zl (Fl.R/16))
    (hpo : Fin.append u (completionShift w J v) ∈ ball 0 Fo.coeffRadius)
    (hpl : Fin.append (Fin.append u v)
      (0 : Fin (Fintype.card (G4.ShortWord w s)) → ℝ) ∈ ball 0 Fl.coeffRadius) :
    basePoint (Fl.Φ (Fin.addCases B J) ((Fin.append (Fin.append u v) 0,ξ),1)) =
      Fo.Φ B ((Fin.append u (completionShift w J v),basePoint ξ),1) := by
  obtain ⟨hlzero,hl⟩ := Fl.flow_on_domain (Fin.addCases B J) _ hpl hξl
  obtain ⟨hozero,ho⟩ := Fo.flow_on_domain B _ hpo hξo
  apply completed_chart_family_projection hΩ w X hX P B J ξ u v
    (Fl.Φ (Fin.addCases B J)) (Fo.Φ B) hlzero hozero
  · intro τ hτ
    exact ⟨hUlΩ (hl τ hτ).2,(hl τ hτ).1⟩
  · intro τ hτ
    exact ⟨hUoΩ (ho τ hτ).2,(ho τ hτ).1⟩

end RothschildStein.L1
