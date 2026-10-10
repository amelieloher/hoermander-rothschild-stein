-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Kernel.JointKernelSections
public import HeatKernel.Kernel.ClassicalLocalWeakSolutions

/-! # Local weak equations for jointly smooth classical kernels

Joint smoothness and the section heat equations give the complete local
weak-solution predicate in either spatial variable on positive-time cylinders.
-/

@[expose] public section

noncomputable section

open TopologicalSpace RothschildStein

namespace HeatKernel

/-- A jointly smooth kernel satisfying the row heat equation has local weak-solution rows. -/
theorem isLocalWeakSolution_row_of_joint_smooth_kernel {n q : ℕ}
    (G : HomogeneousGroup n) (hq : q ≤ n) (hqpos : 0 < q)
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (hspan : bracketSpansOn Set.univ (G.horizontalFields hq))
    (p : ℝ → (Fin n → ℝ) → (Fin n → ℝ) → ℝ)
    (hp : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : ℝ × ((Fin n → ℝ) × (Fin n → ℝ)) => p z.1 z.2.1 z.2.2)
      (Set.Ioi 0 ×ˢ Set.univ))
    (hheat : ∀ t, 0 < t → ∀ x y, deriv (fun s => p s x y) t =
      sumSquares (G.horizontalFields hq) (fun z => p t x z) y)
    (I : Opens ℝ) (U : Opens (Fin n → ℝ)) (hI : ∀ t ∈ I, 0 < t) (x : Fin n → ℝ) :
    IsLocalWeakSolution G hq hqpos hw hspan
      (fun _ _ i j => if i = j then 1 else 0) I U (fun t y => p t x y) :=
  isLocalWeakSolution_of_smooth_classical_heat_equation G hq hqpos hw hspan I U hI
    (fun t y => p t x y) (contDiffOn_joint_kernel_row p hp x) (fun t ht y => hheat t ht x y)

/-- A jointly smooth kernel satisfying the column heat equation has local weak-solution columns. -/
theorem isLocalWeakSolution_column_of_joint_smooth_kernel {n q : ℕ}
    (G : HomogeneousGroup n) (hq : q ≤ n) (hqpos : 0 < q)
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (hspan : bracketSpansOn Set.univ (G.horizontalFields hq))
    (p : ℝ → (Fin n → ℝ) → (Fin n → ℝ) → ℝ)
    (hp : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : ℝ × ((Fin n → ℝ) × (Fin n → ℝ)) => p z.1 z.2.1 z.2.2)
      (Set.Ioi 0 ×ˢ Set.univ))
    (hheat : ∀ t, 0 < t → ∀ x y, deriv (fun s => p s x y) t =
      sumSquares (G.horizontalFields hq) (fun z => p t z y) x)
    (I : Opens ℝ) (U : Opens (Fin n → ℝ)) (hI : ∀ t ∈ I, 0 < t) (y : Fin n → ℝ) :
    IsLocalWeakSolution G hq hqpos hw hspan
      (fun _ _ i j => if i = j then 1 else 0) I U (fun t x => p t x y) :=
  isLocalWeakSolution_of_smooth_classical_heat_equation G hq hqpos hw hspan I U hI
    (fun t x => p t x y) (contDiffOn_joint_kernel_column p hp y) (fun t ht x => hheat t ht x y)

end HeatKernel
