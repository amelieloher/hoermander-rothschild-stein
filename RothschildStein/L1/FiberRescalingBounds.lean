-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.L1.FiberRescalingScales
public import RothschildStein.L1.FiberAssemblyInterfaces
public import RothschildStein.L1.FiberChartVolumeBounds

/-!
# Fixed-factor rescaling: pointwise fiber bounds

Given the single-scale starred fiber bounds at one radius (`StarredFiberBoundsAt`), the
compact starred comparison of the ordinary balls at the target radius, and a real
comparison of the ordinary ball quotients at the two radii, the fiber clauses of
`GaugeFiberData.ball_bounds` follow at the target radius (BB pp. 521–522).
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped BigOperators ENNReal
namespace RothschildStein.L1

/-- The real quotient of the ordinary lifted and original ball volumes at
radius `δ` about `η` and `basePoint η`, as it appears in `StarredFiberBounds`
(BB pp. 521–522). -/
def fiberRescalingRatio {n k m : ℕ} (Ω : Set (Fin n → ℝ)) (w : Fin k → ℕ+)
    (X : Fin k → (Fin n → ℝ) → (Fin n → ℝ))
    (P : Fin k → Fin m → MvPolynomial (Fin (n + m)) ℝ) (η : Fin (n + m) → ℝ) (δ : ℝ) : ℝ :=
  (volume (rsBall {ξ : Fin (n + m) → ℝ | basePoint ξ ∈ Ω} w (triangularLift X P) η δ)).toReal /
    (volume (rsBall Ω w X (basePoint η) δ)).toReal

/-- The fiber clauses of `StarredFiberBounds` at one centre `η`, one radius
`δ` and fixed constants (BB (10.45)–(10.49), pp. 520–522). -/
def StarredFiberBoundsAt {n k s m : ℕ} {w : Fin k → ℕ+}
    {Ω : Set (Fin n → ℝ)} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)}
    {x₀ : Fin n → ℝ} (L : FixedLiftData w s Ω X x₀ m) (η : Fin (n + m) → ℝ)
    (δ cw cs cl cf Cf : ℝ) : Prop :=
  ∀ y : Fin n → ℝ,
    G4.auxiliaryDistance (s := s) (basePoint (n := n) (m := m) '' (L.U : Set _)) w X
      (basePoint η) y < ENNReal.ofReal (cw * δ) →
    ENNReal.ofReal (cf * fiberRescalingRatio Ω w X L.P η δ) ≤
        fiberVolume {ξ | G4.auxiliaryDistance (s := s)
          (L.U : Set (Fin (n + m) → ℝ)) w (triangularLift X L.P) η ξ <
            ENNReal.ofReal (cl * δ)} y ∧
    fiberVolume {ξ | G4.auxiliaryDistance (s := s)
        (L.U : Set (Fin (n + m) → ℝ)) w (triangularLift X L.P) η ξ <
          ENNReal.ofReal (cs * δ)} y ≤
      ENNReal.ofReal (Cf * fiberRescalingRatio Ω w X L.P η δ)

/-- Monotonicity of `rsBall` in the radius. -/
theorem fiberRescaling_rsBall_mono {a n : ℕ} (Ω : Set (Fin n → ℝ)) (p : Fin a → ℕ+)
    (Y : Fin a → (Fin n → ℝ) → (Fin n → ℝ)) (x : Fin n → ℝ) {r r' : ℝ} (h : r ≤ r') :
    rsBall Ω p Y x r ⊆ rsBall Ω p Y x r' := by
  rintro y ⟨hy, hd⟩
  exact ⟨hy, lt_of_lt_of_le hd (ENNReal.ofReal_le_ofReal h)⟩

variable {n k s m : ℕ} {w : Fin k → ℕ+}
    {Ω : Set (Fin n → ℝ)} {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)}
    {x₀ : Fin n → ℝ}

/-- Upper fiber bound of the ordinary lifted ball at radius `r` from the
starred fiber bound at the enlarged scale `Λ r` and a real quotient comparison
(BB pp. 521–522). -/
theorem fiberRescaling_upper (L : FixedLiftData w s Ω X x₀ m) {η : Fin (n + m) → ℝ}
    {r Λ C cw cs cl cf Cf Cf' : ℝ} (hr : 0 < r) (hCw : C ≤ cw * Λ) (hCs : C ≤ cs * Λ)
    (hV : rsBall Ω w X (basePoint η) r ⊆
      {y | G4.auxiliaryDistance (s := s) (basePoint (n := n) (m := m) '' (L.U : Set _)) w X
        (basePoint η) y < ENNReal.ofReal (C * r)})
    (hU : rsBall {ξ : Fin (n + m) → ℝ | basePoint ξ ∈ Ω} w (triangularLift X L.P) η r ⊆
      {ξ | G4.auxiliaryDistance (s := s) (L.U : Set (Fin (n + m) → ℝ)) w
        (triangularLift X L.P) η ξ < ENNReal.ofReal (C * r)})
    (hS : StarredFiberBoundsAt L η (Λ * r) cw cs cl cf Cf)
    (hH : Cf * fiberRescalingRatio Ω w X L.P η (Λ * r) ≤
      Cf' * fiberRescalingRatio Ω w X L.P η r)
    {z : Fin n → ℝ} (hz : z ∈ rsBall Ω w X (basePoint η) r) :
    fiberVolume (rsBall {ξ : Fin (n + m) → ℝ | basePoint ξ ∈ Ω} w
        (triangularLift X L.P) η r) z ≤
      ENNReal.ofReal (Cf' * (volume (rsBall {ξ : Fin (n + m) → ℝ | basePoint ξ ∈ Ω} w
        (triangularLift X L.P) η r)).toReal / (volume (rsBall Ω w X (basePoint η) r)).toReal) := by
  have hCr : C * r ≤ cw * (Λ * r) := by
    have := mul_le_mul_of_nonneg_right hCw hr.le
    linarith
  have hCr' : C * r ≤ cs * (Λ * r) := by
    have := mul_le_mul_of_nonneg_right hCs hr.le
    linarith
  have h0 := hV hz
  simp only [Set.mem_ofPred_eq] at h0
  have hz1 : G4.auxiliaryDistance (s := s) (basePoint (n := n) (m := m) '' (L.U : Set _)) w X
      (basePoint η) z < ENNReal.ofReal (cw * (Λ * r)) :=
    lt_of_lt_of_le h0 (ENNReal.ofReal_le_ofReal hCr)
  have hsub : rsBall {ξ : Fin (n + m) → ℝ | basePoint ξ ∈ Ω} w (triangularLift X L.P) η r ⊆
      {ξ | G4.auxiliaryDistance (s := s) (L.U : Set (Fin (n + m) → ℝ)) w
        (triangularLift X L.P) η ξ < ENNReal.ofReal (cs * (Λ * r))} := by
    intro ξ hξ
    have h1 := hU hξ
    simp only [Set.mem_ofPred_eq] at h1 ⊢
    exact lt_of_lt_of_le h1 (ENNReal.ofReal_le_ofReal hCr')
  rw [mul_div_assoc]
  exact (fiberVolume_mono hsub z).trans ((hS z hz1).2.trans (ENNReal.ofReal_le_ofReal hH))

/-- Lower fiber bound of the ordinary lifted ball at radius `r`, over the
original ball of radius `δf r`, from the starred fiber bound at the reduced scale `δ'`
and a real quotient comparison (BB pp. 521–522). -/
theorem fiberRescaling_lower (L : FixedLiftData w s Ω X x₀ m) {η : Fin (n + m) → ℝ}
    {r δf δ' C cw cs cl cf Cf cf' : ℝ} (hδ : C * (δf * r) ≤ cw * δ')
    (hV : rsBall Ω w X (basePoint η) (δf * r) ⊆
      {y | G4.auxiliaryDistance (s := s) (basePoint (n := n) (m := m) '' (L.U : Set _)) w X
        (basePoint η) y < ENNReal.ofReal (C * (δf * r))})
    (hL : {ξ | G4.auxiliaryDistance (s := s) (L.U : Set (Fin (n + m) → ℝ)) w
        (triangularLift X L.P) η ξ < ENNReal.ofReal (cl * δ')} ⊆
      rsBall {ξ : Fin (n + m) → ℝ | basePoint ξ ∈ Ω} w (triangularLift X L.P) η r)
    (hS : StarredFiberBoundsAt L η δ' cw cs cl cf Cf)
    (hH : cf' * fiberRescalingRatio Ω w X L.P η r ≤ cf * fiberRescalingRatio Ω w X L.P η δ')
    {z : Fin n → ℝ} (hz : z ∈ rsBall Ω w X (basePoint η) (δf * r)) :
    ENNReal.ofReal (cf' * (volume (rsBall {ξ : Fin (n + m) → ℝ | basePoint ξ ∈ Ω} w
        (triangularLift X L.P) η r)).toReal / (volume (rsBall Ω w X (basePoint η) r)).toReal) ≤
      fiberVolume (rsBall {ξ : Fin (n + m) → ℝ | basePoint ξ ∈ Ω} w
        (triangularLift X L.P) η r) z := by
  have h0 := hV hz
  simp only [Set.mem_ofPred_eq] at h0
  have hz1 : G4.auxiliaryDistance (s := s) (basePoint (n := n) (m := m) '' (L.U : Set _)) w X
      (basePoint η) z < ENNReal.ofReal (cw * δ') :=
    lt_of_lt_of_le h0 (ENNReal.ofReal_le_ofReal hδ)
  rw [mul_div_assoc]
  exact (ENNReal.ofReal_le_ofReal hH).trans ((hS z hz1).1.trans (fiberVolume_mono hL z))

end RothschildStein.L1
