-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.L1.ModelData
public import RothschildStein.L1.DirectFreeness
public import RothschildStein.L1.FrameIndependence
public import RothschildStein.L1.FreeFrameWeight
public import RothschildStein.G4.FrameVolumeAdapters

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace
open scoped BigOperators
namespace RothschildStein.L1.ModelData
open G3

/-- The already chosen model words are retained short words;
this makes no new basis or lifting choice (BB pp. 514–515). -/
def shortFrame {k s N : ℕ} {w : Fin k → ℕ+} (M : ModelData k s N w)
    (j : Fin N) : G4.ShortWord w s :=
  ⟨M.B j, (G4.mem_shortWordFamily_iff w _).mpr
    ⟨(M.basis_weight j).1,(M.basis_weight j).2.1⟩⟩

/-- The model short-frame total weight is exactly the
homogeneous dimension (BB Def. 10.36, p. 515). -/
theorem shortFrame_weight_sum {k s N : ℕ} {w : Fin k → ℕ+}
    (M : ModelData k s N w) :
    (∑ j, (G4.shortWeight w (M.shortFrame j) : ℕ)) = M.G.homogeneousDimension := by
  unfold HomogeneousGroup.homogeneousDimension
  apply Finset.sum_congr rfl
  intro j _
  exact (M.basis_weight j).2.2.symm

/-- Formal independence of the fixed model words and actual
freeness imply a nonzero determinant in any smooth free system on the
same carrier (BB Prop. 10.35, pp. 514–515). -/
theorem shortFrame_det_ne_zero {k s N : ℕ} {w : Fin k → ℕ+}
    (M : ModelData k s N w) (U : Opens (Fin N → ℝ))
    (Z : Fin k → (Fin N → ℝ) → (Fin N → ℝ))
    (hZ : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Z i) U)
    {x : Fin N → ℝ} (hx : x ∈ U) (hFree : FreeAt w s Z x) :
    G4.frameDet (G4.shortField w Z) M.shortFrame x ≠ 0 := by
  have hf : LinearIndependent ℝ (fun j => (wordLieElement (M.B j) : formalSpan k s w)) :=
    LinearIndependent.of_comp (formalSpan k s w).subtype M.basis_independent
  have he := hf.map' (directPointEvaluation (s := s) (p := w) U Z hZ x)
    (LinearMap.ker_eq_bot.mpr ((freeAt_iff_directPointEvaluation_injective U Z hZ hx).mp hFree))
  have hval : (fun j => directPointEvaluation (s := s) (p := w) U Z hZ x
      (wordLieElement (M.B j))) = (fun j => G4.shortField w Z (M.shortFrame j) x) := by
    funext j
    exact directPointEvaluation_word U Z hZ (M.B j) (M.basis_weight j).2.1 hx
  apply (frameDet_ne_zero_iff_linearIndependent _ _ _).mpr
  simpa only [Function.comp_def,hval] using he

/-- Every actual nonzero short frame at a free point has the
chosen model's homogeneous dimension; no exponent-identification input
is required (BB Prop. 10.35 and Def. 10.36, pp. 514–515). -/
theorem frame_weight_sum_eq_homogeneousDimension {k s N : ℕ} {w : Fin k → ℕ+}
    (M : ModelData k s N w) (U : Opens (Fin N → ℝ))
    (Z : Fin k → (Fin N → ℝ) → (Fin N → ℝ))
    (hZ : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Z i) U)
    {x : Fin N → ℝ} (hx : x ∈ U) (hFree : FreeAt w s Z x)
    (B : Fin N → G4.ShortWord w s) (hB : G4.frameDet (G4.shortField w Z) B x ≠ 0) :
    (∑ j, (G4.shortWeight w (B j) : ℕ)) = M.G.homogeneousDimension := by
  have hw := short_frameWeight_eq_of_FreeAt Z x hFree B M.shortFrame hB
    (M.shortFrame_det_ne_zero U Z hZ hx hFree)
  rw [G4.frameWeight_eq_nat_sum,G4.frameWeight_eq_nat_sum] at hw
  have he : (∑ j, (G4.shortWeight w (B j) : ℕ)) =
      ∑ j, (G4.shortWeight w (M.shortFrame j) : ℕ) := by exact_mod_cast hw
  exact he.trans M.shortFrame_weight_sum

end RothschildStein.L1.ModelData
