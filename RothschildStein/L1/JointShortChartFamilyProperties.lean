-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.JointShortChartFamily
public import RothschildStein.L1.SelectedChartCoefficientDomain
public import RothschildStein.G4.SelectedFlowDerivativeBounds
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
open scoped BigOperators
namespace RothschildStein.L1.JointShortChartFamily

/-- Every permitted compact center lies in the joint flow's base domain. -/
theorem center_mem_flowDomain {q n s : ℕ} {w : Fin q → ℕ+}
    {Ω : Set (Fin n → ℝ)} {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)}
    {z : Fin n → ℝ} {t : ℝ} (F : JointShortChartFamily (s := s) w Ω X z t)
    {x : Fin n → ℝ} (hx : x ∈ closedBall z (F.R/16)) : x ∈ ball z (F.R/4) :=
  closedBall_subset_ball (by linarith [F.R_pos]) hx

/-- Both selected and shifted parameters fit in the fixed joint domain. -/
theorem parameters_mem_flowDomain {q n s : ℕ} {w : Fin q → ℕ+}
    {Ω : Set (Fin n → ℝ)} {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)}
    {z : Fin n → ℝ} {t : ℝ} (F : JointShortChartFamily (s := s) w Ω X z t)
    (B : Fin n → G4.ShortWord w s) {a b r : ℝ}
    (ha : 0 < a) (haa₀ : a ≤ F.a₀) (hb : 0 ≤ b) (hba : b ≤ a)
    (hr : 0 ≤ r) (hrr : r ≤ F.r₀)
    {u : Fin n → ℝ} {v : Fin (Fintype.card (G4.ShortWord w s)) → ℝ}
    (hu : u ∈ G4.weightedBox (G4.shortWeight w ∘ B) (a*r))
    (hv : v ∈ G4.weightedBox (fun j => G4.shortWeight w (G4.shortIndex w j)) (b*r)) :
    Fin.append u v ∈ ball 0 F.coeffRadius :=
  selected_chart_parameters_mem_ball w B ha.le hb hr (haa₀.trans F.a₀_lt_one.le)
    hba (haa₀.trans_lt F.a₀_lt_coeffRadius) (hrr.trans F.r₀_le_one) u v hu hv

/-- The retained actual flow solves its ODE on the entire common time
interval and stays in the coefficient patch (BB pp. 520–521). -/
theorem flow_on_domain {q n s : ℕ} {w : Fin q → ℕ+}
    {Ω : Set (Fin n → ℝ)} {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)}
    {z : Fin n → ℝ} {t : ℝ} (F : JointShortChartFamily (s := s) w Ω X z t)
    (B : Fin n → G4.ShortWord w s)
    (p : Fin (n+Fintype.card (G4.ShortWord w s)) → ℝ) (hp : p ∈ ball 0 F.coeffRadius)
    {x : Fin n → ℝ} (hx : x ∈ closedBall z (F.R/16)) :
    F.Φ B ((p,x),0) = x ∧ ∀ τ ∈ Ioo (-2 : ℝ) 2,
      HasDerivAt (fun v => F.Φ B ((p,x),v))
        (∑ j, p j • G4.shortField w X (G4.selectedAuxiliaryIndex w B j) (F.Φ B ((p,x),τ))) τ ∧
        F.Φ B ((p,x),τ) ∈ Ω := by
  obtain ⟨hzero,hflow⟩ := (F.flow B).2 p hp x (F.center_mem_flowDomain hx)
  refine ⟨hzero,?_⟩
  intro τ hτ
  exact ⟨(hflow τ hτ).2,F.buffer_subset (ball_subset_closedBall (hflow τ hτ).1)⟩

end RothschildStein.L1.JointShortChartFamily
