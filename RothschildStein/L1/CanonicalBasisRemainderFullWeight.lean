-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.RadialRemainderWeightUpgrade
public import RothschildStein.L1.RadialRemainderSymmetryWeight
public import RothschildStein.L1.CanonicalBasisBracketRemainderWeight
public import RothschildStein.L1.CanonicalFrameFullWeight
public import RothschildStein.L1.ModelBasisFullWeight
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric TopologicalSpace
open scoped BigOperators
namespace RothschildStein.L1
open G3

/-- The actual canonical basis differs from the constructed free model
by fields of full strict weight one minus the basis word weight
(BB Theorem 10.28, pp. 506–509). -/
theorem canonical_basis_remainder_full_weight {a s : ℕ} {p : Fin a → ℕ+}
    (D : FreeModelData a s p) (Ω : Opens (Fin (freeDimension a s p) → ℝ))
    (X : Fin a → (Fin (freeDimension a s p) → ℝ) → (Fin (freeDimension a s p) → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    {x : Fin (freeDimension a s p) → ℝ}
    (C : CanonicalFrameChartData Ω (canonicalWordFrame D X) x)
    (η : Fin (freeDimension a s p) → ℝ) (hη : η ∈ ball x C.radius)
    (i : Fin (freeDimension a s p)) :
    fullFieldJetClass (ball 0 C.radius) D.weight (1 - (D.weight i : ℝ))
      (fun u => C.coordinateField η i u - canonicalWordFrame D D.fields i u) := by
  let U : Opens (Fin (freeDimension a s p) → ℝ) := ⟨ball 0 C.radius,isOpen_ball⟩
  let Z := C.coordinateField η
  let Y := canonicalWordFrame D D.fields
  let R := fun k u => Z k u - Y k u
  have h0 : (0 : Fin (freeDimension a s p) → ℝ) ∈ U := mem_ball_self C.radius_pos
  have hWX := fun k => G1.wordBracket_contDiffOn Ω.isOpen X hX (modelBasisWord D k)
  have hZ : ∀ k, fullFieldJetClass U D.weight (-(D.weight k : ℝ)) (Z k) :=
    canonical_frame_full_weight D Ω X hX C η hη
  have hY : ∀ k, fullFieldJetClass U D.weight (-(D.weight k : ℝ)) (Y k) :=
    model_basis_full_weight D U h0
  have hY0 : ∀ k, Y k 0 = Pi.single k 1 := fun k => modelBasisWord_origin D k
  have hZ0 : ∀ k, Z k 0 = Pi.single k 1 :=
    fun k => C.basis_values Ω.isOpen hWX η hη k
  have hradZ : ∀ u ∈ U, ∑ k, u k • Z k u = u :=
    fun u hu => C.radial_identity Ω.isOpen hWX η u hη hu
  have hradY : ∀ u ∈ U, ∑ k, u k • Y k u = u :=
    fun u _ => modelBasisWord_radial D u
  have hradR : ∀ u ∈ U, ∑ k, u k • R k u = 0 := by
    intro u hu
    dsimp only [R]
    simp only [smul_sub,Finset.sum_sub_distrib,hradZ u hu,hradY u hu,sub_self]
  have hR0 (k : Fin (freeDimension a s p)) : R k 0 = 0 := by
    change Z k 0 - Y k 0 = 0
    rw [hZ0,hY0,sub_self]
  have hall : ∀ q k, fieldJetClass U D.weight (1 - (D.weight k : ℝ)) q (R k) := by
    intro q
    induction q with
    | zero =>
      intro k
      exact (circleFieldJetClass_zero_order_of_zero U D.weight _ _
        ((hZ k 0).1.sub (hY k 0).1) (hR0 k)).1
    | succ q ih =>
      have hB (j l : Fin (freeDimension a s p)) :
          fieldJetClass U D.weight (1 - (D.weight l : ℝ) - D.weight j) q
            (fun u => VectorField.lieBracket ℝ (Z j) (Z l) u -
              VectorField.lieBracket ℝ (Y j) (Y l) u) := by
        have hh := canonical_basis_bracket_remainder_weight_of_basis_remainders
          D Ω X hX C η hη ih j l
        convert hh using 1; try rfl
        ring
      have hs := radial_remainder_symmetry_weight_of_bracket_difference U h0
        D.weight Z Y hZ hY hY0 hradZ hradY ih hB
      exact radial_remainder_weight_upgrade_of_symmetry U h0 D.weight R
        (fun k => (ih k).1) hradR hs
  intro q
  exact hall q i
end RothschildStein.L1
