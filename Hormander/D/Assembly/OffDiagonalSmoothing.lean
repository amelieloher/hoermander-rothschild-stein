-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.D.Assembly.LocalizedGain
public import Hormander.B.OffDiagonal.Final.Commutator

/-!
# Off-diagonal smoothing

`Hormander.D.offDiagonalSmoothing N` proves `Hormander.D.OffDiagonalSmoothing N` via the iterated
commutator route of `Hormander.B.OffDiagonal.Final.Commutator`.
-/

@[expose] public section

noncomputable section

open Hormander.B

namespace Hormander.D

/-- The separated Bessel tail gains arbitrarily many Sobolev orders. -/
theorem offDiagonalSmoothing (N : ℕ) : OffDiagonalSmoothing N := by
  intro φ ψ σ τ r hψφ
  obtain ⟨η, h₁, h₂, -⟩ := exists_intermediate_cutoff hψφ
  set g : SchwartzMap (Carrier N) ℝ := cutoffSchwartzOuter h₁
  have hg : (g : Carrier N → ℝ) = η := rfl
  have hψ : ∀ x, ψ x ≠ 0 → g x = 1 := by
    intro x hx
    have hx' : x ∈ tsupport (ψ : Carrier N → ℝ) := subset_tsupport _ hx
    exact subset_of_mem_nhdsSet h₁.2.2.2.2 hx'
  have hφ : ∀ x, g x ≠ 0 → φ x = 1 := by
    intro x hx
    have hx' : x ∈ tsupport (η : Carrier N → ℝ) := subset_tsupport _ hx
    exact subset_of_mem_nhdsSet h₂.2.2.2.2 hx'
  obtain ⟨C, hC⟩ := offDiagonalTail_order_of_sandwich hψ hφ σ τ r
  exact ⟨C, fun v => by simpa [sub_eq_add_neg] using hC v⟩

end Hormander.D
