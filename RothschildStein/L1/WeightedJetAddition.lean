-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.WeightedJetDerivatives
public import RothschildStein.L1.WeightedJetLocality
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace Filter
open scoped Topology
namespace RothschildStein.L1

set_option backward.defeqAttrib.useBackward true in
/-- Actual ordered coordinate partials add on an open smooth domain. -/
theorem rsPartial_add_on {N : ℕ} (Ω : Opens (Fin N → ℝ))
    (f g : (Fin N → ℝ) → ℝ) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f Ω)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g Ω) (J : List (Fin N))
    {x : Fin N → ℝ} (hx : x ∈ Ω) :
    rsPartial J (fun u => f u + g u) x = rsPartial J f x + rsPartial J g x := by
  induction J generalizing x with
  | nil => rfl
  | cons j J ih =>
    have he : rsPartial J (fun u => f u + g u) =ᶠ[𝓝 x]
        (fun u => rsPartial J f u + rsPartial J g u) :=
      Filter.Eventually.mono (Ω.isOpen.mem_nhds hx) (fun u hu => ih hu)
    have hdf := ((rsPartial_contDiffOn Ω J f hf).contDiffAt
      (Ω.isOpen.mem_nhds hx)).differentiableAt (by simp)
    have hdg := ((rsPartial_contDiffOn Ω J g hg).contDiffAt
      (Ω.isOpen.mem_nhds hx)).differentiableAt (by simp)
    change fderiv ℝ (rsPartial J (fun u => f u + g u)) x (Pi.single j 1) = _
    rw [he.fderiv_eq, fderiv_fun_add hdf hdg, add_apply]
    rfl

/-- A weighted finite jet class is closed under addition. -/
theorem scalarJetClass_add {N p : ℕ} (Ω : Opens (Fin N → ℝ))
    (h0 : (0 : Fin N → ℝ) ∈ Ω) {ω : Fin N → ℕ} {a : ℝ}
    {f g : (Fin N → ℝ) → ℝ} (hf : scalarJetClass Ω ω a p f)
    (hg : scalarJetClass Ω ω a p g) :
    scalarJetClass Ω ω a p (fun u => f u + g u) := by
  refine ⟨hf.1.add hg.1, ?_⟩
  intro J hJ hw
  rw [rsPartial_add_on Ω f g hf.1 hg.1 J h0, hf.2 J hJ hw, hg.2 J hJ hw, zero_add]
/-- Every ordered coordinate derivative of the zero function is zero. -/
theorem rsPartial_zero {N : ℕ} (J : List (Fin N)) :
    rsPartial J (fun _ : Fin N → ℝ => (0 : ℝ)) = fun _ => 0 := by
  induction J with
  | nil => rfl
  | cons j J ih => simp only [rsPartial, ih, fderiv_const_apply, zero_apply]

/-- The zero function belongs to every weighted finite jet class. -/
theorem scalarJetClass_zero {N p : ℕ} (Ω : Set (Fin N → ℝ))
    (ω : Fin N → ℕ) (a : ℝ) : scalarJetClass Ω ω a p (fun _ => 0) := by
  refine ⟨contDiffOn_const, ?_⟩
  intro J _ _
  rw [rsPartial_zero]

/-- Finite sums preserve each weighted finite jet class. -/
theorem scalarJetClass_sum {N p : ℕ} {ι : Type*} (Ω : Opens (Fin N → ℝ))
    (h0 : (0 : Fin N → ℝ) ∈ Ω) (ω : Fin N → ℕ) (a : ℝ)
    (T : Finset ι) (F : ι → (Fin N → ℝ) → ℝ)
    (hF : ∀ i ∈ T, scalarJetClass Ω ω a p (F i)) :
    scalarJetClass Ω ω a p (fun u => ∑ i ∈ T, F i u) := by
  classical
  revert hF
  induction T using Finset.induction_on with
  | empty => intro _; simpa only [Finset.sum_empty] using scalarJetClass_zero Ω ω a
  | @insert i T hi ih =>
    intro hF
    simp only [Finset.sum_insert hi]
    exact scalarJetClass_add Ω h0 (hF i (by simp))
      (ih (fun j hj => hF j (by simp [hj])))

end RothschildStein.L1
