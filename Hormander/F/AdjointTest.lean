-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.Interface.HormanderAdjointTest
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.FDeriv.Congr
public import Mathlib.Topology.Algebra.Support

@[expose] public section

noncomputable section

open Filter Function Set Topology
open scoped BigOperators

namespace Hormander.F

/-- A smooth scalar test supported inside an open set makes a coefficient product globally
smooth, even when the coefficient is only smooth on that open set. -/
theorem localized_smul_smooth {N : ℕ} {Ω : Set ((Fin N → ℝ))} (hΩ : IsOpen Ω)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (φ : (Fin N → ℝ) → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hK : tsupport φ ⊆ Ω) (h : (Fin N → ℝ) → F)
    (hh : ContDiffOn ℝ (⊤ : ℕ∞) h Ω) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => φ x • h x) := by
  rw [← contDiffOn_univ]
  apply isOpen_univ.contDiffOn_iff.mpr
  intro x hx
  by_cases hxΩ : x ∈ Ω
  · exact hφ.contDiffAt.smul (hh.contDiffAt (hΩ.mem_nhds hxΩ))
  · have hxK : x ∉ tsupport φ := fun hxK => hxΩ (hK hxK)
    have hφzero : φ =ᶠ[𝓝 x] fun _ => 0 :=
      (notMem_tsupport_iff_eventuallyEq).mp hxK
    have hzero : (fun y => φ y • h y) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [hφzero] with y hy
      simp [hy]
    exact contDiffAt_const.congr_of_eventuallyEq hzero

/-- In the scalar case, the coefficient product is globally smooth under the same support
condition. -/
theorem localized_mul_smooth {N : ℕ} {Ω : Set ((Fin N → ℝ))} (hΩ : IsOpen Ω)
    (φ h : (Fin N → ℝ) → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hK : tsupport φ ⊆ Ω) (hh : ContDiffOn ℝ (⊤ : ℕ∞) h Ω) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => φ x * h x) := by
  simpa only [smul_eq_mul] using
    localized_smul_smooth hΩ φ hφ hK h hh

theorem localized_smul_zero_outside {N : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (φ : (Fin N → ℝ) → ℝ) (h : (Fin N → ℝ) → F) {x : (Fin N → ℝ)}
    (hx : x ∉ tsupport φ) : φ x • h x = 0 := by
  have hx' : x ∉ support φ := fun hx' => hx (subset_closure hx')
  have hφx : φ x = 0 := by
    simpa only [mem_support, not_not] using hx'
  simp [hφx]

/-- The support of a function that vanishes outside a closed set is contained in that set. -/
theorem tsupport_subset_of_zero_outside {N : ℕ} {f : (Fin N → ℝ) → ℝ} {K : Set ((Fin N → ℝ))}
    (hK : IsClosed K) (hf : ∀ x ∉ K, f x = 0) : tsupport f ⊆ K := by
  change closure (support f) ⊆ K
  refine closure_minimal ?_ hK
  intro x hx
  by_contra hxK
  exact (mem_support.mp hx) (hf x hxK)

/-- The finite-coordinate divergence of a globally smooth vector field is globally smooth. -/
theorem euclideanDivergence_smooth {N : ℕ} (V : (Fin N → ℝ) → (Fin N → ℝ))
    (hV : ContDiff ℝ (⊤ : ℕ∞) V) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun x => Hormander.Interface.euclideanDivergence V x) := by
  have hDf : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ V) :=
    (contDiff_infty_iff_fderiv.mp hV).2
  unfold Hormander.Interface.euclideanDivergence
  apply ContDiff.sum
  intro i hi
  let evalTerm : ((Fin N → ℝ) →L[ℝ] (Fin N → ℝ)) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj i).comp
      (ContinuousLinearMap.apply ℝ (Fin N → ℝ) (Hormander.Interface.basisVec i))
  have hterm : ContDiff ℝ (⊤ : ℕ∞) (fun x => evalTerm (fderiv ℝ V x)) :=
    evalTerm.contDiff.comp hDf
  simpa [evalTerm, Hormander.Interface.basisVec] using hterm

/-- A localized divergence remains smooth globally and is zero off the test support. -/
theorem localizedDivergence_smooth {N : ℕ} {Ω : Set ((Fin N → ℝ))}
    (hΩ : IsOpen Ω) (V : (Fin N → ℝ) → (Fin N → ℝ))
    (hV : ContDiffOn ℝ (⊤ : ℕ∞) V Ω)
    (φ : (Fin N → ℝ) → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hK : tsupport φ ⊆ Ω) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun x => Hormander.Interface.euclideanDivergence (fun y => φ y • V y) x) := by
  apply euclideanDivergence_smooth
  exact localized_smul_smooth hΩ φ hφ hK V hV

theorem localizedDivergence_zero_outside {N : ℕ}
    (V : (Fin N → ℝ) → (Fin N → ℝ)) (φ : (Fin N → ℝ) → ℝ) {x : (Fin N → ℝ)}
    (hx : x ∉ tsupport φ) :
    Hormander.Interface.euclideanDivergence (fun y => φ y • V y) x = 0 := by
  have hlocal : (fun y => φ y • V y) =ᶠ[𝓝 x] fun _ => (0 : (Fin N → ℝ)) := by
    filter_upwards [(notMem_tsupport_iff_eventuallyEq).mp hx] with y hy
    simp [hy]
  have hderiv := hlocal.fderiv_eq (𝕜 := ℝ)
  unfold Hormander.Interface.euclideanDivergence
  rw [hderiv]
  simp

/-- The first adjoint divergence term is globally smooth and supported in the test support. -/
theorem localizedDivergence_tsupport_subset {N : ℕ}
    (V : (Fin N → ℝ) → (Fin N → ℝ)) (φ : (Fin N → ℝ) → ℝ) :
    tsupport (fun x => Hormander.Interface.euclideanDivergence
      (fun y => φ y • V y) x) ⊆ tsupport φ := by
  apply tsupport_subset_of_zero_outside (isClosed_tsupport _)
  intro x hx
  exact localizedDivergence_zero_outside V φ hx

/-- Multiplying the localized divergence by a coefficient that is smooth on Ω again gives a
globally smooth field. -/
theorem localized_outerField_smooth {N : ℕ} {Ω : Set ((Fin N → ℝ))}
    (hΩ : IsOpen Ω) (V : (Fin N → ℝ) → (Fin N → ℝ))
    (hV : ContDiffOn ℝ (⊤ : ℕ∞) V Ω)
    (φ : (Fin N → ℝ) → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hK : tsupport φ ⊆ Ω) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x =>
      Hormander.Interface.euclideanDivergence (fun y => φ y • V y) x • V x) := by
  exact localized_smul_smooth hΩ
    (fun x => Hormander.Interface.euclideanDivergence (fun y => φ y • V y) x)
    (localizedDivergence_smooth hΩ V hV φ hφ hK)
    ((localizedDivergence_tsupport_subset V φ).trans hK) V hV

theorem localized_outerDivergence_smooth {N : ℕ} {Ω : Set ((Fin N → ℝ))}
    (hΩ : IsOpen Ω) (V : (Fin N → ℝ) → (Fin N → ℝ))
    (hV : ContDiffOn ℝ (⊤ : ℕ∞) V Ω)
    (φ : (Fin N → ℝ) → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hK : tsupport φ ⊆ Ω) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => Hormander.Interface.euclideanDivergence
      (fun y => Hormander.Interface.euclideanDivergence
        (fun z => φ z • V z) y • V y) x) := by
  apply euclideanDivergence_smooth
  exact localized_outerField_smooth hΩ V hV φ hφ hK

theorem localized_outerDivergence_zero_outside {N : ℕ}
    (V : (Fin N → ℝ) → (Fin N → ℝ)) (φ : (Fin N → ℝ) → ℝ)
    {x : (Fin N → ℝ)} (hx : x ∉ tsupport φ) :
    Hormander.Interface.euclideanDivergence
      (fun y => Hormander.Interface.euclideanDivergence
        (fun z => φ z • V z) y • V y) x = 0 := by
  have houter : (fun y =>
      Hormander.Interface.euclideanDivergence (fun z => φ z • V z) y • V y) =ᶠ[𝓝 x]
      fun _ => (0 : (Fin N → ℝ)) := by
    filter_upwards [(isClosed_tsupport φ).isOpen_compl.mem_nhds hx] with y hy
    have hinner := localizedDivergence_zero_outside V φ hy
    simp [hinner]
  have hderiv := houter.fderiv_eq (𝕜 := ℝ)
  rw [Hormander.Interface.euclideanDivergence]
  rw [hderiv]
  simp

/-- The adjoint test `hormanderAdjointTest` is globally smooth, supported in K, and vanishes away from K. -/
theorem hormanderAdjointTest_smooth {k N : ℕ} {Ω : Set ((Fin N → ℝ))}
    (hΩ : IsOpen Ω) (X : Fin (k + 1) → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω)
    (c : (Fin N → ℝ) → ℝ) (hc : ContDiffOn ℝ (⊤ : ℕ∞) c Ω)
    (φ : (Fin N → ℝ) → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hK : tsupport φ ⊆ Ω) :
    ContDiff ℝ (⊤ : ℕ∞) (Hormander.Interface.hormanderAdjointTest X c φ) := by
  unfold Hormander.Interface.hormanderAdjointTest
  have hfirst := localizedDivergence_smooth hΩ (X 0) (hX 0) φ hφ hK
  have hsum : ContDiff ℝ (⊤ : ℕ∞) (fun x => ∑ i : Fin k,
      Hormander.Interface.euclideanDivergence
        (fun y => Hormander.Interface.euclideanDivergence
          (fun z => φ z • X i.succ z) y • X i.succ y) x) := by
    apply ContDiff.sum
    intro i hi
    exact localized_outerDivergence_smooth hΩ (X i.succ) (hX i.succ) φ hφ hK
  have hlast : ContDiff ℝ (⊤ : ℕ∞) (fun x => c x * φ x) := by
    simpa only [mul_comm] using localized_mul_smooth hΩ φ c hφ hK hc
  exact hfirst.neg.add hsum |>.add hlast

theorem hormanderAdjointTest_zero_outside {k N : ℕ}
    (X : Fin (k + 1) → (Fin N → ℝ) → (Fin N → ℝ))
    (c φ : (Fin N → ℝ) → ℝ) {x : (Fin N → ℝ)}
    (hx : x ∉ tsupport φ) :
    Hormander.Interface.hormanderAdjointTest X c φ x = 0 := by
  have hfirst := localizedDivergence_zero_outside (X 0) φ hx
  have hsum : ∀ i : Fin k, Hormander.Interface.euclideanDivergence
      (fun y => Hormander.Interface.euclideanDivergence
        (fun z => φ z • X i.succ z) y • X i.succ y) x = 0 := by
    intro i
    exact localized_outerDivergence_zero_outside (X i.succ) φ hx
  have hlast : c x * φ x = 0 := by
    have hφx := localized_smul_zero_outside φ (fun _ : (Fin N → ℝ) => (1 : ℝ)) hx
    simpa using congrArg (fun t : ℝ => c x * t) hφx
  unfold Hormander.Interface.hormanderAdjointTest
  simp [hfirst, hsum, hlast]

theorem hormanderAdjointTest_tsupport_subset {k N : ℕ}
    (X : Fin (k + 1) → (Fin N → ℝ) → (Fin N → ℝ))
    (c φ : (Fin N → ℝ) → ℝ) :
    tsupport (Hormander.Interface.hormanderAdjointTest X c φ) ⊆ tsupport φ := by
  apply tsupport_subset_of_zero_outside (isClosed_tsupport _)
  intro x hx
  exact hormanderAdjointTest_zero_outside X c φ hx

end Hormander.F
