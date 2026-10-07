-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.Standing
public import RothschildStein.Definitions.sumSquaresWithDrift
public import RothschildStein.S.ClassicalWords
public import RothschildStein.Definitions.testMultiplierOn

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped Topology BigOperators
namespace RothschildStein.H1
variable {N q : ℕ} (G : HomogeneousGroup N)

/-- Multiplying the local punctured smooth kernel by a compact
interior cutoff gives a globally punctured smooth function (BB p. 265). -/
theorem contDiffOn_localizedKernel (Ω : Opens (Fin N → ℝ))
    {γ : (Fin N → ℝ) → ℝ}
    (hγ : ContDiffOn ℝ (⊤ : ℕ∞) γ ((Ω : Set (Fin N → ℝ)) ∩ {(0 : Fin N → ℝ)}ᶜ))
    (η : TestFunction Ω ℝ (⊤ : ℕ∞)) :
    ContDiffOn ℝ (⊤ : ℕ∞) (fun x => γ x * η x) {(0 : Fin N → ℝ)}ᶜ := by
  intro x hx
  apply ContDiffAt.contDiffWithinAt
  by_cases hxΩ : x ∈ (Ω : Set (Fin N → ℝ))
  · exact (hγ.contDiffAt ((Ω.isOpen.inter isOpen_compl_singleton).mem_nhds
      ⟨hxΩ, hx⟩)).mul η.contDiff.contDiffAt
  · have hxs : x ∉ tsupport (η : (Fin N → ℝ) → ℝ) := fun h => hxΩ (η.tsupport_subset h)
    have he : ∀ᶠ y in 𝓝 x, y ∉ tsupport (η : (Fin N → ℝ) → ℝ) :=
      isClosed_closure.isOpen_compl.mem_nhds hxs
    exact (contDiffAt_const : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun _ : Fin N → ℝ => (0 : ℝ)) x).congr_of_eventuallyEq
        (he.mono fun y hy => by simp only [image_eq_zero_of_notMem_tsupport hy, mul_zero])

/-- The classical standing operator is local even for a
function that is singular on its support (BB p. 265). -/
theorem tsupport_sumSquares_subset
    (X : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ)) (f : (Fin N → ℝ) → ℝ) :
    tsupport (sumSquaresWithDrift X f) ⊆ tsupport f := by
  apply closure_minimal _ isClosed_closure
  intro x hx
  by_contra hxf
  have hd (i : Fin (q + 1)) : fieldDerivative (X i) f x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hxf (S.tsupport_fieldDerivative_subset (X i) f h))
  have hdd (i : Fin (q + 1)) : fieldDerivative (X i) (fieldDerivative (X i) f) x = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => hxf
      ((S.tsupport_fieldDerivative_subset (X i) _).trans
        (S.tsupport_fieldDerivative_subset (X i) f) h))
  exact hx (by simp only [sumSquaresWithDrift, hd, hdd, Finset.sum_const_zero, add_zero])

/-- The localized error has compact support inherited from
the local kernel, independently of its value at zero (BB p. 265). -/
theorem hasCompactSupport_localizedError
    (X : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ))
    {Γ : (Fin N → ℝ) → ℝ} (hs : HasCompactSupport Γ) (η : (Fin N → ℝ) → ℝ) :
    HasCompactSupport (fun x => sumSquaresWithDrift X Γ x * (1 - η x)) := by
  have hp : HasCompactSupport (sumSquaresWithDrift X Γ) :=
    hs.of_isClosed_subset isClosed_closure (tsupport_sumSquares_subset X Γ)
  exact hp.mul_right

/-- Smoothness of the standing operator is local, so it
applies on the punctured domain of the kernel (BB p. 265). -/
theorem StandingHypotheses.contDiffOn_operator (H : StandingHypotheses G q)
    (U : Opens (Fin N → ℝ)) {f : (Fin N → ℝ) → ℝ}
    (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (U : Set (Fin N → ℝ))) :
    ContDiffOn ℝ (⊤ : ℕ∞) (sumSquaresWithDrift H.fields f) (U : Set (Fin N → ℝ)) := by
  have hd (i : Fin (q + 1)) : ContDiffOn ℝ (⊤ : ℕ∞)
      (fieldDerivative (H.fields i) f) (U : Set (Fin N → ℝ)) :=
    (hf.fderiv_of_isOpen U.isOpen (by simp)).clm_apply (H.fields_smooth G i).contDiffOn
  have hdd (i : Fin q) : ContDiffOn ℝ (⊤ : ℕ∞)
      (fieldDerivative (H.fields i.succ) (fieldDerivative (H.fields i.succ) f))
      (U : Set (Fin N → ℝ)) :=
    ((hd i.succ).fderiv_of_isOpen U.isOpen (by simp)).clm_apply (H.fields_smooth G i.succ).contDiffOn
  exact (hd 0).add (ContDiffOn.sum (fun i _ => hdd i))

/-- The error vanishes near the origin by the inner cutoff,
including the value chosen at the origin (BB p. 265). -/
theorem localizedError_eventually_zero
    (PΓ η : (Fin N → ℝ) → ℝ) (hη : η =ᶠ[𝓝 (0 : Fin N → ℝ)] 1) :
    (fun x => PΓ x * (1 - η x)) =ᶠ[𝓝 (0 : Fin N → ℝ)] 0 := by
  filter_upwards [hη] with x hx
  simp only [hx, Pi.one_apply, sub_self, mul_zero, Pi.zero_apply]

/-- A punctured smooth function multiplied by a factor that
vanishes near zero extends smoothly across the origin (BB p. 265). -/
theorem contDiff_localizedError
    {PΓ η : (Fin N → ℝ) → ℝ}
    (hP : ContDiffOn ℝ (⊤ : ℕ∞) PΓ {(0 : Fin N → ℝ)}ᶜ)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hz : η =ᶠ[𝓝 (0 : Fin N → ℝ)] 1) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => PΓ x * (1 - η x)) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x = 0
  · subst x
    exact (contDiffAt_const : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun _ : Fin N → ℝ => (0 : ℝ)) 0).congr_of_eventuallyEq
        (localizedError_eventually_zero PΓ η hz)
  · exact (hP.contDiffAt (isOpen_compl_singleton.mem_nhds hx)).mul
      (contDiffAt_const.sub hη.contDiffAt)

end RothschildStein.H1
