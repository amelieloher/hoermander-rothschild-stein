-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.SmoothJointShiftedBallBox
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric Filter MeasureTheory
open scoped BigOperators Topology
namespace RothschildStein.L1
open G4

/-- The actual slice properties retained by the joint G4 family,
including its whole-image inverse (BB pp. 448–449, 520–521). -/
def ShortChartSlices {q n s : ℕ} (w : Fin q → ℕ+)
    (Ω : Set (Fin n → ℝ)) (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (z : Fin n → ℝ) (R t a b r₀ D κ : ℝ)
    (Φ : (Fin n → ShortWord w s) →
      (((Fin (n+Fintype.card (ShortWord w s)) → ℝ) × (Fin n → ℝ)) × ℝ) → (Fin n → ℝ)) : Prop :=
    let m := Fintype.card (ShortWord w s)
    let wf : Fin m → ℕ+ := fun j => shortWeight w (shortIndex w j)
    let Zf : Fin m → (Fin n → ℝ) → (Fin n → ℝ) := fun j => shortField w X (shortIndex w j)
    ∀ x ∈ closedBall z (R / 16), ∀ r : ℝ, 0 < r → r ≤ r₀ →
      ∀ B : Fin n → ShortWord w s,
        IsSuboptimal (shortField w X) (shortWeight w) B x t r →
      ∀ v ∈ weightedBox wf (b * r),
      let F := fun u => Φ B ((Fin.append u v, x), 1)
      let Q := weightedBox (shortWeight w ∘ B) (a * r)
      ChartAnalyticBounds Ω wf Zf ((Fintype.equivFin (ShortWord w s)) ∘ B) F Q r κ D ∧
      ChartTrajectories Ω Zf ((Fintype.equivFin (ShortWord w s)) ∘ B) F Q x v
        (fun u τ => Φ B ((Fin.append u v, x), τ)) ∧
      (v = 0 → F 0 = x) ∧ InjOn F Q ∧
      (∀ u ∈ Q, |frameDet (shortField w X) B x| / 4 ≤
        |Matrix.det (coordinateDerivativeMatrix (fderiv ℝ F u))| ∧
        |Matrix.det (coordinateDerivativeMatrix (fderiv ℝ F u))| ≤
          4 * |frameDet (shortField w X) B x|) ∧
      ({y | auxiliaryDistance (s := s) Ω w X x y < ENNReal.ofReal (b * r)} ⊆ F '' Q) ∧
      (F '' Q ⊆ {y | constantShortDistance (s := s) Ω w X x y < ENNReal.ofReal (2 * a * r)}) ∧
      ({y | constantShortDistance (s := s) Ω w X x y < ENNReal.ofReal (2 * a * r)} ⊆
        {y | auxiliaryDistance (s := s) Ω w X x y < ENNReal.ofReal (2 * a * r)}) ∧
      (v = 0 → F '' Q ⊆
        {y | constantShortDistance (s := s) Ω w X x y < ENNReal.ofReal (a * r)}) ∧
      IsOpen (F '' Q) ∧
      ∃ Ψ : (Fin n → ℝ) → (Fin n → ℝ), ContDiffOn ℝ (⊤ : ℕ∞) Ψ (F '' Q) ∧
        (∀ y ∈ F '' Q, Ψ y ∈ Q ∧ F (Ψ y) = y) ∧ (∀ u ∈ Q, Ψ (F u) = u) ∧
        ∀ y ∈ F '' Q, ∀ ℓ i : Fin n,
          |(fderiv ℝ Ψ y (shortField w X (B ℓ) y)) i| ≤ (4 / 3 : ℝ) *
            r ^ (((shortWeight w (B i) : ℕ) : ℤ) - ((shortWeight w (B ℓ) : ℕ) : ℤ))

/-- One actual joint flow family with fresh shifted slices at every
smaller horizontal radius. This record retains proof data; it adds no
control-distance or coordinate convention (BB pp. 520–521). -/
structure JointShortChartFamily {q n s : ℕ} (w : Fin q → ℕ+)
    (Ω : Set (Fin n → ℝ)) (X : Fin q → (Fin n → ℝ) → (Fin n → ℝ))
    (z : Fin n → ℝ) (t : ℝ) where
  R : ℝ
  R_pos : 0 < R
  buffer_subset : closedBall z R ⊆ Ω
  coeffRadius : ℝ
  a₀ : ℝ
  a₀_pos : 0 < a₀
  a₀_lt_one : a₀ < 1
  a₀_lt_coeffRadius : a₀ < coeffRadius
  r₀ : ℝ
  r₀_pos : 0 < r₀
  r₀_le_one : r₀ ≤ 1
  D : ℝ
  D_nonneg : 0 ≤ D
  κ : ℝ
  κ_pos : 0 < κ
  κ_small : (n : ℝ)*κ ≤ 1/4
  Φ : (Fin n → ShortWord w s) →
    (((Fin (n+Fintype.card (ShortWord w s)) → ℝ) × (Fin n → ℝ)) × ℝ) → (Fin n → ℝ)
  flow : ∀ B, ContDiffOn ℝ (⊤ : ℕ∞) (Φ B)
    ((ball 0 coeffRadius ×ˢ ball z (R/4)) ×ˢ Ioo (-2) 2) ∧
    ∀ p ∈ ball 0 coeffRadius, ∀ x ∈ ball z (R/4), Φ B ((p,x),0) = x ∧
      ∀ τ ∈ Ioo (-2 : ℝ) 2, Φ B ((p,x),τ) ∈ ball z R ∧
        HasDerivAt (fun v => Φ B ((p,x),v))
          (∑ j, p j • shortField w X (selectedAuxiliaryIndex w B j) (Φ B ((p,x),τ))) τ
  slices : ∀ a : ℝ, 0 < a → a ≤ a₀ →
    ∃ b : ℝ, 0 < b ∧ b < a/4 ∧ 2*b ≤ 1 ∧
      ShortChartSlices w Ω X z R t a b r₀ D κ Φ

/-- Smooth local bracket generation constructs the complete joint
family, including its fixed coefficient domain and fresh-radius order
(BB pp. 448–449, 520–521). -/
theorem nonempty_jointShortChartFamily {k n s : ℕ}
    (hn : 0 < n) (hs : 0 < s) (w : Fin (k+1) → ℕ+)
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1)
    {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω)
    (X : Fin (k+1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (hstep : bracketStepOn Ω w X s) {z : Fin n → ℝ} (hz : z ∈ Ω) :
    Nonempty (JointShortChartFamily (s := s) w Ω X z t) := by
  obtain ⟨R,M,hR,_hM,hRΩ,a₀,r₀,D,κ,ha₀,ha₀1,ha₀δ,hr₀,hr₀1,hD,hκ,hκsmall,Φ,hflow,hslices⟩ :=
    exists_smooth_joint_shifted_short_ball_box hn hs w ht ht1 hΩ X hX hstep hz
  refine ⟨{
    R := R
    R_pos := hR
    buffer_subset := hRΩ
    coeffRadius := R/(64*(1+((n+Fintype.card (ShortWord w s) : ℕ) : ℝ)*wordJetBase n 0 s M ^ s))
    a₀ := a₀
    a₀_pos := ha₀
    a₀_lt_one := ha₀1
    a₀_lt_coeffRadius := ha₀δ
    r₀ := r₀
    r₀_pos := hr₀
    r₀_le_one := hr₀1
    D := D
    D_nonneg := hD
    κ := κ
    κ_pos := hκ
    κ_small := hκsmall
    Φ := Φ
    flow := hflow
    slices := ?_ }⟩
  intro a ha haa₀
  obtain ⟨b,hb,hba,hb1,hcharts⟩ := hslices a ha haa₀
  exact ⟨b,hb,hba,hb1,hcharts⟩

end RothschildStein.L1
