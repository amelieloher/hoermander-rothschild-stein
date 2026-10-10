-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.Locality
public import Mathlib.Analysis.Calculus.FDeriv.Congr
import Mathlib.Tactic

/-! Weak derivatives away from cutoff supports and derivatives on constant plateaus. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
open Set MeasureTheory TopologicalSpace RothschildStein Filter
open scoped Topology
namespace HeatKernel

/-- A global weak derivative vanishes almost everywhere outside the closed
support of its function. -/
theorem hasWeakWordDeriv_ae_zero_outside_tsupport {N q : ℕ}
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ)) (I : List (Fin q))
    {f g : (Fin N → ℝ) → ℝ} (hg : hasWeakWordDeriv X ⊤ I f g) :
    ∀ᵐ x ∂volume, x ∉ tsupport f → g x = 0 := by
  let W : Opens (Fin N → ℝ) := ⟨(tsupport f)ᶜ, isClosed_tsupport f |>.isOpen_compl⟩
  have hfzero : f =ᵐ[volume.restrict (W : Set (Fin N → ℝ))] fun _ => 0 :=
    ae_restrict_of_forall_mem W.isOpen.measurableSet
      (fun x hx => image_eq_zero_of_notMem_tsupport hx)
  exact (ae_restrict_iff' W.isOpen.measurableSet).mp
    (S.hasWeakWordDeriv_locality X ⊤ W (subset_univ _) hg hfzero)

/-- A vector-field derivative is zero on any open plateau of a function. -/
theorem fieldDerivative_eq_zero_on_plateau {N : ℕ}
    (X : (Fin N → ℝ) → (Fin N → ℝ)) {ψ : (Fin N → ℝ) → ℝ}
    {P : Set (Fin N → ℝ)} (hP : IsOpen P) {c : ℝ}
    (hψ : EqOn ψ (fun _ => c) P) {x : Fin N → ℝ} (hx : x ∈ P) :
    fieldDerivative X ψ x = 0 := by
  have he : ψ =ᶠ[𝓝 x] fun _ => c :=
    Filter.eventually_of_mem (hP.mem_nhds hx) (fun y hy => hψ hy)
  change fderiv ℝ ψ x (X x) = 0
  rw [he.fderiv_eq]
  simp

end HeatKernel
