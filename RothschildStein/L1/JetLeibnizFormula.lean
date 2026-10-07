-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.L1.WeightedJetDerivatives
public import RothschildStein.L1.JetLeibnizPartitions
@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set TopologicalSpace Filter
open scoped Topology
namespace RothschildStein.L1

/-- Finite list sums of functions differentiable at a point remain differentiable. -/
theorem differentiableAt_list_sum {N : ℕ} {ι : Type*} (L : List ι)
    (F : ι → (Fin N → ℝ) → ℝ) (x : Fin N → ℝ)
    (hF : ∀ i ∈ L, DifferentiableAt ℝ (F i) x) :
    DifferentiableAt ℝ (fun y => (L.map (fun i => F i y)).sum) x := by
  revert hF
  induction L with
  | nil => intro _; exact differentiableAt_const _
  | cons i L ih =>
    intro hF
    simp only [List.map_cons, List.sum_cons]
    exact (hF i (by simp)).add (ih (fun j hj => hF j (by simp [hj])))

/-- The actual derivative of a finite list sum, retaining multiplicities. -/
theorem fderiv_list_sum_apply {N : ℕ} {ι : Type*} (L : List ι)
    (F : ι → (Fin N → ℝ) → ℝ) (x z : Fin N → ℝ)
    (hF : ∀ i ∈ L, DifferentiableAt ℝ (F i) x) :
    fderiv ℝ (fun y => (L.map (fun i => F i y)).sum) x z =
      (L.map (fun i => fderiv ℝ (F i) x z)).sum := by
  revert hF
  induction L with
  | nil => intro _; simp
  | cons i L ih =>
    intro hF
    have ht := differentiableAt_list_sum L F x (fun k hk => hF k (by simp [hk]))
    simp only [List.map_cons, List.sum_cons]
    rw [fderiv_fun_add (hF i (by simp)) ht, add_apply]
    rw [ih (fun j hj => hF j (by simp [hj]))]

/-- The exact finite ordered Leibniz formula
on an open smooth domain; it retains all multiplicities. -/
theorem rsPartial_mul_eq_leibniz {N : ℕ} (Ω : Opens (Fin N → ℝ))
    (f g : (Fin N → ℝ) → ℝ) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f Ω)
    (hg : ContDiffOn ℝ (⊤ : ℕ∞) g Ω) (J : List (Fin N)) :
    ∀ x ∈ Ω, rsPartial J (fun y => f y * g y) x =
      ((jetLeibnizPartitions J).map (fun q => rsPartial q.1 f x * rsPartial q.2 g x)).sum := by
  induction J with
  | nil => intro x hx; simp only [rsPartial, jetLeibnizPartitions, List.map_singleton, List.sum_singleton]
  | cons j J ih =>
    intro x hx
    have he : rsPartial J (fun y => f y * g y) =ᶠ[𝓝 x]
        (fun y => ((jetLeibnizPartitions J).map
          (fun q => rsPartial q.1 f y * rsPartial q.2 g y)).sum) :=
      Filter.Eventually.mono (Ω.isOpen.mem_nhds hx) (fun y hy => ih y hy)
    have hs (q : List (Fin N) × List (Fin N)) :
        DifferentiableAt ℝ (fun y => rsPartial q.1 f y * rsPartial q.2 g y) x := by
      have hdf := ((rsPartial_contDiffOn Ω q.1 f hf).contDiffAt
        (Ω.isOpen.mem_nhds hx)).differentiableAt (by simp)
      have hdg := ((rsPartial_contDiffOn Ω q.2 g hg).contDiffAt
        (Ω.isOpen.mem_nhds hx)).differentiableAt (by simp)
      exact hdf.mul hdg
    change fderiv ℝ (rsPartial J (fun y => f y * g y)) x (Pi.single j 1) = _
    rw [he.fderiv_eq, fderiv_list_sum_apply _ _ _ _ (fun q _ => hs q)]
    simp only [jetLeibnizPartitions, List.map_append, List.sum_append, List.map_map]
    rw [← List.sum_map_add]
    apply congrArg List.sum
    apply List.map_congr_left
    intro q hq
    have hdf := ((rsPartial_contDiffOn Ω q.1 f hf).contDiffAt
      (Ω.isOpen.mem_nhds hx)).differentiableAt (by simp)
    have hdg := ((rsPartial_contDiffOn Ω q.2 g hg).contDiffAt
      (Ω.isOpen.mem_nhds hx)).differentiableAt (by simp)
    rw [fderiv_fun_mul hdf hdg]
    simp only [add_apply, smul_apply, smul_eq_mul, Function.comp_apply, rsPartial]
    ring
end RothschildStein.L1
