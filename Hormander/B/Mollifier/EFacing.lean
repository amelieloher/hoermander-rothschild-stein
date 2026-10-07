-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.B.Mollifier.Weighted
public import Hormander.D.Defs

@[expose] public section

noncomputable section

open MeasureTheory
open scoped FourierTransform ENNReal

namespace Hormander.B

variable {N : ℕ}

/-- The Schwartz function attached to a smooth compactly supported cutoff relation. -/
def cutoffSchwartz {η η' : Carrier N → ℝ} (h : Hormander.D.cutoffPrecedes η η') :
    SchwartzMap (Carrier N) ℝ := h.2.1.toSchwartzMap h.1

theorem cutoffSchwartz_apply {η η' : Carrier N → ℝ} (h : Hormander.D.cutoffPrecedes η η')
    (x : Carrier N) : cutoffSchwartz h x = η x := rfl

/-- The outer cutoff of a cutoff relation, as a Schwartz function. -/
def cutoffSchwartzOuter {η η' : Carrier N → ℝ} (h : Hormander.D.cutoffPrecedes η η') :
    SchwartzMap (Carrier N) ℝ := h.2.2.2.1.toSchwartzMap h.2.2.1

theorem cutoffSchwartzOuter_apply {η η' : Carrier N → ℝ} (h : Hormander.D.cutoffPrecedes η η')
    (x : Carrier N) : cutoffSchwartzOuter h x = η' x := rfl

theorem cutoff_outer_eq_one {η η' : Carrier N → ℝ} (h : Hormander.D.cutoffPrecedes η η') :
    ∀ x ∈ tsupport (cutoffSchwartz h : Carrier N → ℝ), cutoffSchwartzOuter h x = 1 := by
  intro x hx
  rw [cutoffSchwartzOuter_apply]
  exact subset_of_mem_nhdsSet h.2.2.2.2 hx

/-- `[Λ^r, θ] X_j` and `[Λ^r, X_j]` have order `r`. -/
theorem eFacing_orders (X : RealSchwartzVectorField N) (θ : SchwartzMap (Carrier N) ℝ) (r : ℝ) :
    HasOrder r ((operatorComm (lambdaOperator r) (realMultiplierOperator θ)).comp
        (vectorFieldOperator X)) ∧
      HasOrder r (operatorComm (lambdaOperator r) (vectorFieldOperator X)) := by
  refine ⟨?_, (hasOrder_lambda_comm_vectorField X r).1⟩
  have h1 := fractionalCommutator_order r (complexifyRealSchwartz θ)
  have h2 := (isDiffOp_vectorFieldOperator X).hasOrder
  have := h1.comp h2
  convert this using 1 <;> first | rfl | (push_cast; ring)

/-- For `η₁ ≺ θ ≺ ρ_E ≺ η₂`, `T^r = θ Λ^r θ`:
`‖[S_δ ρ_E, X_j] T^r u‖₂ ≤ C ‖η₂ u‖_{H^r}`, uniformly in `δ > 0`. -/
theorem eFacing_mollifier_cutoff_bound (X : RealSchwartzVectorField N)
    {η₁ θ ρ η₂ : Carrier N → ℝ}
    (_h₁ : Hormander.D.cutoffPrecedes η₁ θ) (h₂ : Hormander.D.cutoffPrecedes θ ρ)
    (h₃ : Hormander.D.cutoffPrecedes ρ η₂) (r : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (δ : ℝ) (hδ : 0 < δ) (u : TestFunction N),
      sobolevNorm 0 (operatorComm ((mollOp N δ hδ).comp (realMultiplierOperator (cutoffSchwartz h₃)))
          (vectorFieldOperator X)
          (((realMultiplierOperator (cutoffSchwartz h₂)).comp (lambdaOperator r)).comp
            (realMultiplierOperator (cutoffSchwartz h₂)) u)) ≤
        C * sobolevNorm r (realMultiplierOperator (cutoffSchwartzOuter h₃) u) := by
  set zθ := cutoffSchwartz h₂
  set zρ := cutoffSchwartz h₃
  set zη := cutoffSchwartzOuter h₃
  have hρη := cutoff_outer_eq_one h₃
  -- η₂ = 1 on the support of θ
  have hθη : ∀ x ∈ tsupport (zθ : Carrier N → ℝ), zη x = 1 := by
    intro x hx
    apply hρη
    have hρ1 : ρ x = 1 := subset_of_mem_nhdsSet h₂.2.2.2.2 hx
    have : x ∈ Function.support ρ := by simp [Function.mem_support, hρ1]
    exact subset_tsupport _ this
  obtain ⟨Ce, hCe, hCe'⟩ := mollifier_cutoff_commutator_bound X zρ zη hρη 0
  set T := ((realMultiplierOperator zθ).comp (lambdaOperator r)).comp (realMultiplierOperator zθ)
  have hMθ : HasOrder 0 (realMultiplierOperator zθ) :=
    hasOrder_multiplierOperator_zero (complexifyRealSchwartz zθ)
  have hMη : HasOrder 0 (realMultiplierOperator zη) :=
    hasOrder_multiplierOperator_zero (complexifyRealSchwartz zη)
  have hT : HasOrder r ((realMultiplierOperator zη).comp T) := by
    have := hMη.comp ((hMθ.comp (hasOrder_lambdaOperator r)).comp hMθ)
    simpa [T, LinearMap.comp_assoc] using this
  have habs : (realMultiplierOperator zθ).comp (realMultiplierOperator zη) =
      realMultiplierOperator zθ :=
    multiplier_absorb_of_tsupport (complexifyRealSchwartz zθ) zη (by
      rw [tsupport_complexifyRealSchwartz]; exact hθη)
  have hTabs : T = T.comp (realMultiplierOperator zη) := by
    simp only [T, LinearMap.comp_assoc, habs]
  obtain ⟨CT, hCT, hCT'⟩ := norm0_le_of_order hT
  refine ⟨Ce * CT, by positivity, fun δ hδ u => ?_⟩
  have e : T u = T (realMultiplierOperator zη u) := LinearMap.congr_fun hTabs u
  have h1 := ((hCe' δ hδ (T u)).1).2
  have h2 : realMultiplierOperator zη (T u) = ((realMultiplierOperator zη).comp T)
      (realMultiplierOperator zη u) := by
    rw [e]; rfl
  rw [h2] at h1
  refine h1.trans ?_
  calc Ce * sobolevNorm 0 (((realMultiplierOperator zη).comp T) (realMultiplierOperator zη u))
      ≤ Ce * (CT * sobolevNorm r (realMultiplierOperator zη u)) :=
        mul_le_mul_of_nonneg_left (hCT' _) hCe
    _ = _ := by ring

end Hormander.B
