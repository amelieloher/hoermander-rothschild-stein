-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Moser.MeanValueMatrixCutoffPair
public import HeatKernel.Moser.LogarithmicTentSpatialWeight
public import HeatKernel.Geometry.SmoothCutoff
public import HeatKernel.Bridge.WeakCutoffSupport
import Mathlib.Tactic
import all HeatKernel.Geometry.CarnotPoint
import all Mathlib.Basic.Real.Basic

/-! # Distance-tent weights on actual nonnegative weak-solution cutoff curves -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set MeasureTheory TopologicalSpace RothschildStein
namespace HeatKernel

/-- The squared distance tent of radius three halves has a compatible fixed test
and smooth localization plateau inside the radius-two solution ball. The same
weak gradient and actual dual time equation are retained. -/
theorem IsLocalWeakSolution.exists_logarithmic_tent_cutoff_pair {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (x : CarnotPoint G hq hqpos hspan) {r : ℝ} (hr : 0 < r)
    (coeff : ℝ → (Fin N → ℝ) → Fin q → Fin q → ℝ)
    (I : Opens ℝ) {u : ℝ → (Fin N → ℝ) → ℝ}
    (hu : IsLocalWeakSolution G hq hqpos hw hspan coeff I
      ⟨horizontalBall (G.horizontalFields hq) x (2 * r),
        isOpen_horizontalBall G hq hqpos hspan x (2 * r)⟩ u)
    (ha : ∀ i j, Measurable (fun z : ℝ × (Fin N → ℝ) => coeff z.1 z.2 i j))
    {lower upper : ℝ} (hlower : 0 ≤ lower)
    (hbound : ∀ᵐ z : ℝ × (Fin N → ℝ) ∂volume,
      (∀ i j, coeff z.1 z.2 i j = coeff z.1 z.2 j i) ∧ ∀ ξ : Fin q → ℝ,
        lower * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, coeff z.1 z.2 i j * ξ i * ξ j ∧
        ∑ i, ∑ j, coeff z.1 z.2 i j * ξ i * ξ j ≤ upper * ∑ i, ξ i ^ 2)
    (hu0 : ∀ᵐ z : ℝ × (Fin N → ℝ)
      ∂volume.restrict ((I : Set ℝ) ×ˢ horizontalBall (G.horizontalFields hq) x (2 * r)),
        0 ≤ u z.1 z.2)
    {A B : ℝ} (hJ : Icc A B ⊆ (I : Set ℝ)) :
    let U : Opens (Fin N → ℝ) := ⟨horizontalBall (G.horizontalFields hq) x (2 * r),
      isOpen_horizontalBall G hq hqpos hspan x (2 * r)⟩
    let η := fun y => max (1 - (horizontalL2Distance (G.horizontalFields hq) x y).toReal /
      (3 * r / 2)) 0
    ∃ (φ : (Fin N → ℝ) → ℝ) (d : energyGraph (N := N) ⊤ (G.horizontalFields hq))
      (W : WeakSolutionSpatialWeight U (G.horizontalFields hq))
      (w : zeroBoundaryGraph U (G.horizontalFields hq))
      (g : Fin q → ℝ → (Fin N → ℝ) → ℝ)
      (v : ℝ → zeroBoundaryGraph U (G.horizontalFields hq))
      (F : ℝ → (zeroBoundaryGraph U (G.horizontalFields hq) →L[ℝ] ℝ)),
      WeakSolutionEnergyInterface (G.horizontalFields hq) coeff I U u g ∧
      IsZeroBoundaryWeakCutoffEnergyTimePair U (G.horizontalFields hq) coeff (Icc A B)
        u g φ (fun i => fieldDerivative (G.horizontalFields hq i) φ) v F ∧
      (∀ᵐ t ∂volume.restrict (Icc A B), ∀ᵐ y ∂volume,
        0 ≤ (v t : GradientSpace (N := N) ⊤ q).fst y) ∧
      W.toFun = (fun y => η y ^ 2) ∧
      W.gradient = (fun i y => 2 * η y * (d : GradientSpace (N := N) ⊤ q).snd i y) ∧
      (w : GradientSpace (N := N) ⊤ q).fst =ᵐ[volume] W.toFun ∧
      (∀ i, (w : GradientSpace (N := N) ⊤ q).snd i =ᵐ[volume] W.gradient i) ∧
      (∀ᵐ y ∂volume, ∑ i, ((d : GradientSpace (N := N) ⊤ q).snd i y)^2 ≤
        ((3 * r / 2)^2)⁻¹) ∧
      (∀ᵐ y ∂volume, y ∉ horizontalBall (G.horizontalFields hq) x (3 * r / 2) →
        ∀ i, (d : GradientSpace (N := N) ⊤ q).snd i y = 0) ∧
      (∀ y, W.toFun y ≠ 0 ∨ (∃ i, W.gradient i y ≠ 0) →
        φ y = 1 ∧ ∀ i, fieldDerivative (G.horizontalFields hq i) φ y = 0) := by
  let U : Opens (Fin N → ℝ) := ⟨horizontalBall (G.horizontalFields hq) x (2 * r),
    isOpen_horizontalBall G hq hqpos hspan x (2 * r)⟩
  let η := fun y => max (1 - (horizontalL2Distance (G.horizontalFields hq) x y).toReal /
    (3 * r / 2)) 0
  have hrad : 0 < 3 * r / 2 := by positivity
  obtain ⟨d, W, w, _, hd, hW, hD, hwv, hwd, _, hzero⟩ :=
    exists_logarithmic_tent_spatial_weight G hq hqpos hspan hw x hrad
      (show 3 * r / 2 < 2 * r by linarith)
  have hc := isCompact_horizontal_closedBall G hq hqpos hspan hw x
    (show 0 ≤ 7 * r / 4 by positivity)
  obtain ⟨φ, hφ, hcompact, hs, hunit, hone⟩ := exists_smooth_cutoff hc U.isOpen (by
    intro y hy
    exact hy.trans_lt ((ENNReal.ofReal_lt_ofReal_iff (by positivity : 0 < 2 * r)).mpr
      (show 7 * r / 4 < 2 * r by linarith)))
  obtain ⟨g, v, F, hg, hp, hz⟩ := hu.exists_smooth_cutoff_energy_pair G hq hqpos hw hspan
    coeff I U U ha hlower hbound hu0 hJ hφ hunit hcompact hs hs
  refine ⟨φ, d, W, w, g, v, F, hg, hp, hz, hW, hD, hwv, hwd, hd, hzero, ?_⟩
  intro y hy
  have hηne : η y ≠ 0 := by
    intro hηzero
    rcases hy with hy | ⟨i, hi⟩
    · exact hy (by rw [hW]; simp only [η, hηzero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)])
    · exact hi (by rw [hD]; change 2 * η y * _ = 0; rw [hηzero]; ring)
  have hηpos : 0 < η y := lt_of_le_of_ne (le_max_right _ _) (Ne.symm hηne)
  have hdiv : (horizontalL2Distance (G.horizontalFields hq) x y).toReal / (3 * r / 2) < 1 := by
    dsimp only [η] at hηpos
    rcases lt_max_iff.mp hηpos with h | h
    · linarith
    · exact False.elim (lt_irrefl 0 h)
  have hdist : (horizontalL2Distance (G.horizontalFields hq) x y).toReal < 7 * r / 4 := by
    have H := (div_lt_one hrad).mp hdiv
    linarith
  have hyP : y ∈ horizontalBall (G.horizontalFields hq) x (7 * r / 4) := by
    change horizontalL2Distance (G.horizontalFields hq) x y < ENNReal.ofReal (7 * r / 4)
    rw [← ENNReal.toReal_lt_toReal
      (horizontalL2Distance_ne_top_of_bracketSpansOn hqpos _ (G.horizontalFields_contDiff hq) hspan x y)
      ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal (by positivity : 0 ≤ 7 * r / 4)]
    exact hdist
  have heq : EqOn φ (fun _ => (1 : ℝ)) (horizontalBall (G.horizontalFields hq) x (7 * r / 4)) := by
    intro z hz
    apply hone z
    exact le_of_lt (show horizontalL2Distance (G.horizontalFields hq) x z <
      ENNReal.ofReal (7 * r / 4) from hz)
  exact ⟨heq hyP, fun i => fieldDerivative_eq_zero_on_plateau (G.horizontalFields hq i)
    (isOpen_horizontalBall G hq hqpos hspan x (7 * r / 4)) heq hyP⟩

end HeatKernel
