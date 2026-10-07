-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.Generators
public import RothschildStein.G4.FrameCalculus
public import RothschildStein.S.Transposes

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Filter
open scoped Topology

namespace RothschildStein.G4

/-- Products of frame coefficients are smooth on the open
nondegenerate-frame domain (BB Definition 9.33, p. 425). -/
theorem generatorValue_contDiffOn {ι : Type*} {n : ℕ}
    {Ω : Set (Fin n → ℝ)}
    {Z : ι → (Fin n → ℝ) → (Fin n → ℝ)}
    (hZ : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (Z j) Ω)
    (B : Fin n → ι) (L : List (Fin n × ι)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (generatorValue Z B L)
      (Ω ∩ {x | frameDet Z B x ≠ 0}) := by
  induction L with
  | nil => exact contDiffOn_const
  | cons z L ih =>
    exact (frameCoefficient_contDiffOn hZ (hZ z.2) B z.1).mul ih

/-- Recursive Leibniz expression for the derivative of an actual
generator product; its empty-product derivative is zero. -/
def generatorDerivativeValue {ι : Type*} {n : ℕ}
    (Z : ι → (Fin n → ℝ) → (Fin n → ℝ)) (B : Fin n → ι)
    (T : (Fin n → ℝ) → (Fin n → ℝ)) :
    List (Fin n × ι) → (Fin n → ℝ) → ℝ
  | [], _ => 0
  | z :: L, x => fieldDerivative T (frameCoefficient Z B (Z z.2) z.1) x *
      generatorValue Z B L x + frameCoefficient Z B (Z z.2) z.1 x *
        generatorDerivativeValue Z B T L x

/-- The recursive Leibniz expression equals the actual derivative
on the original open frame domain (BB Proposition 9.36, pp. 427–428). -/
theorem fieldDerivative_generatorValue {ι : Type*} {n : ℕ}
    {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω)
    {Z : ι → (Fin n → ℝ) → (Fin n → ℝ)}
    (hZ : ∀ j, ContDiffOn ℝ (⊤ : ℕ∞) (Z j) Ω)
    (B : Fin n → ι) (T : (Fin n → ℝ) → (Fin n → ℝ))
    (L : List (Fin n × ι)) {x : Fin n → ℝ}
    (hx : x ∈ Ω) (hB : frameDet Z B x ≠ 0) :
    fieldDerivative T (generatorValue Z B L) x = generatorDerivativeValue Z B T L x := by
  have hnear : Ω ∩ {y | frameDet Z B y ≠ 0} ∈ 𝓝 x := by
    apply inter_mem (hΩ.mem_nhds hx)
    exact ((frameDet_contDiffOn hZ B).contDiffAt (hΩ.mem_nhds hx)).continuousAt.preimage_mem_nhds
      (isOpen_compl_singleton.mem_nhds hB)
  induction L with
  | nil =>
    change (fderiv ℝ (fun _ : Fin n → ℝ => (1 : ℝ)) x) (T x) = 0
    simp
  | cons z L ih =>
    have hc := ((frameCoefficient_contDiffOn hZ (hZ z.2) B z.1).contDiffAt hnear).differentiableAt
      (by simp)
    have hg := ((generatorValue_contDiffOn hZ B L).contDiffAt hnear).differentiableAt
      (by simp)
    change fieldDerivative T (fun y => frameCoefficient Z B (Z z.2) z.1 y *
      generatorValue Z B L y) x = _
    rw [S.fieldDerivative_mul T _ _ x hc hg, ih]
    rfl

end RothschildStein.G4
