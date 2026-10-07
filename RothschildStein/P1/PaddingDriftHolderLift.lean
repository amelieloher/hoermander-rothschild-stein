-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.PaddingDriftTriangularAdapter
public import RothschildStein.P1.PaddingCylinderFiberSetting
public import RothschildStein.P1.PaddingDriftHolderAlphabet
public import RothschildStein.P1.PaddingHolderPullbackNorm

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace
open scoped ENNReal
namespace RothschildStein.P1

/-- Each intrinsic word derivative in the projected alphabet
lifts to the actual genuine diffusion-padded system. -/
theorem hasIntrinsicWordDeriv_paddingDrift_lift {q n d : ℕ}
    (Ω : Opens (Fin n → ℝ)) (J : Opens (Fin d → ℝ))
    (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (I : List (Fin (q + d + 1))) (f g : (Fin n → ℝ) → ℝ)
    (hg : hasIntrinsicWordDeriv (paddingDriftBaseAlphabet (d := d) X) Ω I f g) :
    hasIntrinsicWordDeriv (paddingVectorFields (d := d) X) (P2.cylinder Ω J) I
      (fun ξ => f (basePoint ξ)) (fun ξ => g (basePoint ξ)) := by
  let Y := paddingDriftBaseAlphabet (d := d) X
  let P := paddingDriftPolynomials q n d
  have hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (triangularLift Y P i)
      (P2.cylinder Ω J : Set (Fin (n + d) → ℝ)) := by
    change ∀ i, ContDiffOn ℝ (⊤ : ℕ∞)
      (triangularLift (paddingDriftBaseAlphabet (d := d) X)
        (paddingDriftPolynomials q n d) i) _
    rw [← paddingVectorFields_eq_triangularLift]
    exact contDiffOn_paddingVectorFields_projection _ _
      (padding_cylinder_subset_base Ω J) X hX
  have hgi := P2.hasIntrinsicWordDeriv_comp_basePoint (P2.cylinder Ω J) Ω
    (fun _ h => (P2.mem_cylinder.mp h).1) hXt I hg
  change hasIntrinsicWordDeriv
    (triangularLift (paddingDriftBaseAlphabet (d := d) X) (paddingDriftPolynomials q n d))
    (P2.cylinder Ω J) I (fun ξ => f (basePoint ξ)) (fun ξ => g (basePoint ξ)) at hgi
  rw [← paddingVectorFields_eq_triangularLift] at hgi
  exact hgi

/-- Intrinsic Hölder regularity of the forcing
lifts at every order to the full genuine diffusion-padded family.
Metric domains and output domains are independent. -/
theorem memHolderX_paddingDrift_lift {q n d k : ℕ}
    (ΩA : Opens (Fin n → ℝ)) (JA : Opens (Fin d → ℝ))
    (Ω : Opens (Fin n → ℝ)) (J : Opens (Fin d → ℝ))
    (w : Fin (q + 1) → ℕ+) (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (Ω : Set (Fin n → ℝ)))
    (α : ℝ) (hα : 0 ≤ α) (f : (Fin n → ℝ) → ℝ)
    (hf : memHolderX w X (controlDistance (ΩA : Set (Fin n → ℝ)) w X) Ω k α f) :
    memHolderX (paddingControlWeights (d := d) w)
      (paddingVectorFields (d := d) X)
      (controlDistance (P2.cylinder ΩA JA : Set (Fin (n + d) → ℝ))
        (paddingControlWeights (d := d) w) (paddingVectorFields (d := d) X))
      (P2.cylinder Ω J) k α (fun ξ => f (basePoint ξ)) := by
  have hbase := memHolderX_paddingDriftBaseAlphabet (d := d) Ω w X hX
    (controlDistance (ΩA : Set (Fin n → ℝ)) w X) α f hf
  refine ⟨(holderENorm_paddingDrift_pullback_le ΩA JA Ω J w X α hα f).trans_lt hf.1, ?_⟩
  intro I hI
  obtain ⟨g, hg, hgn⟩ := hbase.2 I hI
  have hgi := hasIntrinsicWordDeriv_paddingDrift_lift Ω J X hX I f g hg
  exact ⟨fun ξ => g (basePoint ξ), hgi,
    (holderENorm_paddingDrift_pullback_le ΩA JA Ω J w X α hα g).trans_lt hgn⟩

end RothschildStein.P1
