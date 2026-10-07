-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.L1.StarredFiberGeometry
public import RothschildStein.L1.MixedChartBallContainments
public import RothschildStein.L1.CompletedFamilyCoefficientDomains

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
open scoped ENNReal
namespace RothschildStein.L1.StarredFiber

/-- The zero-shift lifted chart of the completed frame `(B, J)`
at the centre `η`, as a map of the joined coordinates (BB pp. 520-521). -/
abbrev liftedChart {q n m s : ℕ} {w : Fin q → ℕ+} {Ω : Set (Fin (n + m) → ℝ)}
    {X : Fin q → (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ)} {z : Fin (n + m) → ℝ} {t : ℝ}
    (H : JointShortChartFamily (s := s) w Ω X z t)
    (B : Fin n → G4.ShortWord w s) (J : Fin m → G4.ShortWord w s) (η : Fin (n + m) → ℝ) :
    (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) :=
  fun x => H.Φ (completedFrame B J)
    ((Fin.append x (0 : Fin (Fintype.card (G4.ShortWord w s)) → ℝ),η),1)

/-- The shifted original chart of the selected frame `B`, shifted by
the vertical parameters of the completion `J` (BB pp. 520-521). -/
abbrev shiftedChart {q n m s : ℕ} {w : Fin q → ℕ+} {Ω : Set (Fin n → ℝ)}
    {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)} {z : Fin n → ℝ} {t : ℝ}
    (H : JointShortChartFamily (s := s) w Ω X z t)
    (B : Fin n → G4.ShortWord w s) (J : Fin m → G4.ShortWord w s) (x : Fin n → ℝ) :
    (Fin n → ℝ) → (Fin m → ℝ) → (Fin n → ℝ) :=
  fun u v => H.Φ B ((Fin.append u (completionShift w J v),x),1)

/-- Smoothness, injectivity and Jacobian bounds of the lifted
zero-shift chart on the full box, and the two containments of the lifted starred
balls with the mixed image `Q_{a δ} × Q'_{c δ}` (BB pp. 520-521). -/
theorem lifted_chart_data {q n m s : ℕ} {w : Fin q → ℕ+}
    {Ω : Set (Fin (n + m) → ℝ)} {X : Fin q → (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ)}
    {z : Fin (n + m) → ℝ} {t : ℝ} (H : JointShortChartFamily (s := s) w Ω X z t)
    {η : Fin (n + m) → ℝ} (hη : η ∈ closedBall z (H.R / 16))
    {a b c δ : ℝ} (ha : 0 < a) (hc : 0 < c) (hca : c ≤ a) (hδ : 0 < δ) (hδr : δ ≤ H.r₀)
    (hg : ZeroShiftGeometry H a b) (B : Fin n → G4.ShortWord w s)
    (J : Fin m → G4.ShortWord w s)
    (hsub : ∀ r : ℝ, 0 < r → G4.IsSuboptimal (G4.shortField w X) (G4.shortWeight w)
      (completedFrame B J) η t r) :
    ContDiffOn ℝ (⊤ : ℕ∞) (liftedChart H B J η)
      (G4.weightedBox (G4.shortWeight w ∘ completedFrame B J) (a * δ)) ∧
    InjOn (liftedChart H B J η)
      (G4.weightedBox (G4.shortWeight w ∘ completedFrame B J) (a * δ)) ∧
    (∀ p ∈ G4.weightedBox (G4.shortWeight w ∘ completedFrame B J) (a * δ),
      |G4.frameDet (G4.shortField w X) (completedFrame B J) η| / 4 ≤
        |(fderiv ℝ (liftedChart H B J η) p).det| ∧
      |(fderiv ℝ (liftedChart H B J η) p).det| ≤
        4 * |G4.frameDet (G4.shortField w X) (completedFrame B J) η|) ∧
    {y | G4.auxiliaryDistance (s := s) Ω w X η y < ENNReal.ofReal ((b * c / a) * δ)} ⊆
      (fun p => liftedChart H B J η (joinPoint p.1 p.2)) ''
        (G4.weightedBox (G4.shortWeight w ∘ B) (a * δ) ×ˢ
          G4.weightedBox (G4.shortWeight w ∘ J) (c * δ)) ∧
    (fun p => liftedChart H B J η (joinPoint p.1 p.2)) ''
        (G4.weightedBox (G4.shortWeight w ∘ B) (a * δ) ×ˢ
          G4.weightedBox (G4.shortWeight w ∘ J) (c * δ)) ⊆
      {y | G4.auxiliaryDistance (s := s) Ω w X η y < ENNReal.ofReal (a * δ)} := by
  have hw := completed_shortWeight_eq w B J
  have hgδ := hg η hη δ hδ hδr (completedFrame B J) (hsub δ hδ)
  have hinner : ∀ r : ℝ, 0 < r → r ≤ H.r₀ →
      {y | G4.auxiliaryDistance (s := s) Ω w X η y < ENNReal.ofReal (b * r)} ⊆
        liftedChart H B J η '' G4.weightedBox
          (Fin.addCases (G4.shortWeight w ∘ B) (G4.shortWeight w ∘ J)) (a * r) := by
    intro r hr hrr
    have h := (hg η hη r hr hrr (completedFrame B J) (hsub r hr)).2.2.2.1
    rw [hw] at h
    exact h
  have houter : liftedChart H B J η '' G4.weightedBox
      (Fin.addCases (G4.shortWeight w ∘ B) (G4.shortWeight w ∘ J)) (a * δ) ⊆
      {y | G4.auxiliaryDistance (s := s) Ω w X η y < ENNReal.ofReal (a * δ)} := by
    have h := hgδ.2.2.2.2
    rw [hw] at h
    exact h
  have hmix := mixed_chart_image_ball_containments (s := s) Ω w X η
    (G4.shortWeight w ∘ B) (G4.shortWeight w ∘ J) (liftedChart H B J η)
    (a := a) (b := b) (au := a) (av := c) (c := c) (r₀ := H.r₀) (δ := δ)
    ha ha.le hc.le hc hca le_rfl le_rfl hca hδ hδr hinner houter
  exact ⟨hgδ.1,hgδ.2.1,hgδ.2.2.1,hmix.1,hmix.2⟩

/-- Injectivity, coverage of the original starred ball of radius
`b δ` and Jacobian bounds of the shifted original charts, for every vertical
parameter of the weighted box `Q'_{b δ}` of the completion (BB pp. 520-521). -/
theorem shifted_chart_data {q n m s : ℕ} {w : Fin q → ℕ+}
    {Ω : Set (Fin n → ℝ)} {X : Fin q → (Fin n → ℝ) → (Fin n → ℝ)}
    {z : Fin n → ℝ} {t : ℝ} (H : JointShortChartFamily (s := s) w Ω X z t)
    {x : Fin n → ℝ} (hx : x ∈ closedBall z (H.R / 16))
    {a b δ : ℝ} (hδ : 0 < δ) (hδr : δ ≤ H.r₀)
    (hg : ShiftedGeometry H a b) (B : Fin n → G4.ShortWord w s)
    (hB : G4.IsSuboptimal (G4.shortField w X) (G4.shortWeight w) B x t δ)
    (J : Fin m → G4.ShortWord w s)
    (hshift : ∀ v ∈ G4.weightedBox (G4.shortWeight w ∘ J) (b * δ),
      completionShift w J v ∈ G4.weightedBox
        (fun j => G4.shortWeight w (G4.shortIndex (s := s) w j)) (b * δ)) :
    (∀ v ∈ G4.weightedBox (G4.shortWeight w ∘ J) (b * δ),
      InjOn (fun u => shiftedChart H B J x u v)
        (G4.weightedBox (G4.shortWeight w ∘ B) (a * δ))) ∧
    (∀ y ∈ {y | G4.auxiliaryDistance (s := s) Ω w X x y < ENNReal.ofReal (b * δ)},
      ∀ v ∈ G4.weightedBox (G4.shortWeight w ∘ J) (b * δ),
      ∃ u ∈ G4.weightedBox (G4.shortWeight w ∘ B) (a * δ), shiftedChart H B J x u v = y) ∧
    (∀ u ∈ G4.weightedBox (G4.shortWeight w ∘ B) (a * δ),
      ∀ v ∈ G4.weightedBox (G4.shortWeight w ∘ J) (b * δ),
      |G4.frameDet (G4.shortField w X) B x| / 4 ≤
        |(fderiv ℝ (fun y => shiftedChart H B J x y v) u).det| ∧
      |(fderiv ℝ (fun y => shiftedChart H B J x y v) u).det| ≤
        4 * |G4.frameDet (G4.shortField w X) B x|) := by
  refine ⟨fun v hv => (hg x hx δ hδ hδr B hB (completionShift w J v) (hshift v hv)).1,?_,?_⟩
  · intro y hy v hv
    obtain ⟨u,hu,hue⟩ := (hg x hx δ hδ hδr B hB (completionShift w J v) (hshift v hv)).2.2 hy
    exact ⟨u,hu,hue⟩
  · intro u hu v hv
    exact (hg x hx δ hδ hδr B hB (completionShift w J v) (hshift v hv)).2.1 u hu

end RothschildStein.L1.StarredFiber
