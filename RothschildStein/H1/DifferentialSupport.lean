-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.DifferentialLocality
public import RothschildStein.H1.DifferentialScalar
public import RothschildStein.H1.HomogeneousTransposeConstant
public import RothschildStein.S.WeakDeriv

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set Filter TopologicalSpace MeasureTheory
open scoped Topology
namespace RothschildStein.H1
variable {N : ℕ}

private theorem differentialTranspose_zero (P : SmoothDifferentialOperator N) :
    G2.differentialTranspose P (fun _ => (0 : ℝ)) = fun _ => 0 := by
  have h := differentialTranspose_const_mul P 0 (fun _ => (1 : ℝ))
  simpa only [zero_mul] using h

/-- Formal transposition does not enlarge support. -/
theorem tsupport_differentialTranspose_subset (P : SmoothDifferentialOperator N)
    (f : (Fin N → ℝ) → ℝ) : tsupport (G2.differentialTranspose P f) ⊆ tsupport f := by
  apply closure_minimal _ isClosed_closure
  intro x hx
  by_contra hxf
  have he : f =ᶠ[𝓝 x] fun _ => 0 := notMem_tsupport_iff_eventuallyEq.mp hxf
  exact hx (by rw [differentialTranspose_germ_eq P he, differentialTranspose_zero])

/-- A cutoff equal to one near the origin has transpose zero
there, for a homogeneous operator of positive degree. -/
theorem differentialTranspose_cutoff_eventually_zero (G : HomogeneousGroup N)
    (P : SmoothDifferentialOperator N) {k : ℝ} (hk : 0 < k) (hP : P.IsHomogeneous G k)
    {θ : (Fin N → ℝ) → ℝ} (he : θ =ᶠ[𝓝 (0 : Fin N → ℝ)] fun _ => 1) :
    G2.differentialTranspose P θ =ᶠ[𝓝 (0 : Fin N → ℝ)] fun _ => 0 := by
  filter_upwards [he.eventuallyEq_nhds] with x hx
  rw [differentialTranspose_germ_eq P hx, differentialTranspose_one_eq_zero G P hk hP]
  rfl

/-- Step 2: a cutoff transpose is a compact test away from
zero, so its pairing with a continuous punctured kernel is integrable. -/
theorem integrable_mul_differentialTranspose_cutoff (G : HomogeneousGroup N)
    (P : SmoothDifferentialOperator N) {k : ℝ} (hk : 0 < k) (hP : P.IsHomogeneous G k)
    {f θ : (Fin N → ℝ) → ℝ} (hf : ContinuousOn f {(0 : Fin N → ℝ)}ᶜ)
    (hθ : ContDiff ℝ (⊤ : ℕ∞) θ) (hs : HasCompactSupport θ)
    (he : θ =ᶠ[𝓝 (0 : Fin N → ℝ)] fun _ => 1) :
    Integrable (fun x => f x * G2.differentialTranspose P θ x) := by
  let U : Opens (Fin N → ℝ) := ⟨{0}ᶜ, isOpen_compl_singleton⟩
  have hzero : (0 : Fin N → ℝ) ∉ tsupport (G2.differentialTranspose P θ) :=
    notMem_tsupport_iff_eventuallyEq.mpr (differentialTranspose_cutoff_eventually_zero G P hk hP he)
  have hcomp : HasCompactSupport (G2.differentialTranspose P θ) :=
    hs.of_isClosed_subset isClosed_closure (tsupport_differentialTranspose_subset P θ)
  let ψ : TestFunction U ℝ (⊤ : ℕ∞) :=
    ⟨G2.differentialTranspose P θ, G2.differentialTranspose_preservesSmooth P θ hθ, hcomp,
      by intro x hx; change x ∈ ({0}ᶜ : Set (Fin N → ℝ));
         simp only [mem_compl_iff, mem_singleton_iff]; intro he; exact hzero (he ▸ hx)⟩
  exact S.integrable_mul_test U (hf.locallyIntegrableOn isOpen_compl_singleton.measurableSet) ψ

end RothschildStein.H1
