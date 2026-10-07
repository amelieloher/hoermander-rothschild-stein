-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.E.OneStepFinal.LzBound
public import Hormander.D.Cutoffs

@[expose] public section

noncomputable section

open MeasureTheory SchwartzMap

namespace Hormander.E
open Hormander.B

variable {N : ℕ}

theorem testToTempered_injective' {φ ψ : TestFunction N} (h : (φ : Tempered N) = ψ) : φ = ψ := by
  have : φ - ψ = 0 := by
    apply eq_zero_of_bilinearPairing_eq_zero
    intro u
    have h1 : (φ : Tempered N) u = (ψ : Tempered N) u := by rw [h]
    rw [testToTempered_apply, testToTempered_apply] at h1
    rw [bilinearPairing_comm, bilinearPairing_sub_right, h1, sub_self]
  exact sub_eq_zero.mp this

/-- A nested pair of smooth compactly supported functions has a Schwartz intermediate cutoff. -/
theorem exists_intermediate_schwartz {η : Carrier N → ℝ} {η' : SchwartzMap (Carrier N) ℝ}
    (h : Hormander.D.cutoffPrecedes η (η' : Carrier N → ℝ)) :
    ∃ χ : SchwartzMap (Carrier N) ℝ, Hormander.D.cutoffPrecedes η (χ : Carrier N → ℝ) ∧
      Hormander.D.cutoffPrecedes (χ : Carrier N → ℝ) (η' : Carrier N → ℝ) := by
  obtain ⟨χf, h1, h2, -⟩ := Hormander.D.exists_intermediate_cutoff h
  refine ⟨cutoffSchwartz h2, ?_, ?_⟩
  · have e : ⇑(cutoffSchwartz h2) = χf := funext (cutoffSchwartz_apply h2)
    rw [e]; exact h1
  · have e : ⇑(cutoffSchwartz h2) = χf := funext (cutoffSchwartz_apply h2)
    rw [e]; exact h2

/-- The five-fold chain `η₁ ≺ χ ≺ θ ≺ ρ ≺ η₂` of Schwartz cutoffs. -/
theorem exists_schwartz_chain {η₁ η₂ : SchwartzMap (Carrier N) ℝ}
    (h : Hormander.D.cutoffPrecedes (η₁ : Carrier N → ℝ) (η₂ : Carrier N → ℝ)) :
    ∃ χ θ ρ : SchwartzMap (Carrier N) ℝ,
      Hormander.D.cutoffPrecedes (η₁ : Carrier N → ℝ) (χ : Carrier N → ℝ) ∧
      Hormander.D.cutoffPrecedes (χ : Carrier N → ℝ) (θ : Carrier N → ℝ) ∧
      Hormander.D.cutoffPrecedes (θ : Carrier N → ℝ) (ρ : Carrier N → ℝ) ∧
      Hormander.D.cutoffPrecedes (ρ : Carrier N → ℝ) (η₂ : Carrier N → ℝ) := by
  obtain ⟨ρ, h1, h2⟩ := exists_intermediate_schwartz h
  obtain ⟨θ, h3, h4⟩ := exists_intermediate_schwartz h1
  obtain ⟨χ, h5, h6⟩ := exists_intermediate_schwartz h3
  exact ⟨χ, θ, ρ, h5, h6, h4, h2⟩

/-- The diffusion operator is local. -/
theorem diffusion_apply_eq_zero {k : ℕ} (Vs : Fin (k + 1) → RealSchwartzVectorField N)
    (cs : SchwartzMap (Carrier N) ℝ) (g : TestFunction N) (x : Carrier N)
    (hx : x ∉ tsupport (g : Carrier N → ℂ)) :
    Hormander.C.diffusionOperator Vs cs g x = 0 := by
  have hsub : ∀ i, tsupport (vectorFieldOperator (Vs i) g : Carrier N → ℂ) ⊆
      tsupport (g : Carrier N → ℂ) := fun i => tsupport_vectorField_subset _ _
  unfold Hormander.C.diffusionOperator
  simp only [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.comp_apply]
  have h1 : ∀ i : Fin k, vectorFieldOperator (Vs i.succ) (vectorFieldOperator (Vs i.succ) g) x = 0 :=
    fun i => vectorField_apply_eq_zero (Vs i.succ) _ x (fun h => hx (hsub _ h))
  have h2 : vectorFieldOperator (Vs 0) g x = 0 := vectorField_apply_eq_zero (Vs 0) g x hx
  have h3 : realMultiplierOperator cs g x = 0 := by
    rw [realMultiplierOperator_apply]
    have : g x = 0 := image_eq_zero_of_notMem_tsupport hx
    simp [this]
  rw [add_apply, add_apply, sum_apply]
  simp [h1, h2, h3]

end Hormander.E
