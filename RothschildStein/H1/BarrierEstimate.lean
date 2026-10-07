-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.BarrierAlgebra
public import RothschildStein.H1.WeakComparison

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set
namespace RothschildStein.H1
variable {N q : ℕ}

private theorem closure_slab_subset (j : Fin N) {d : ℝ} {U : Set (Fin N → ℝ)}
    (hstrip : ∀ x ∈ U, -d < x j ∧ x j < d) :
    closure U ⊆ {x | -d ≤ x j ∧ x j ≤ d} := by
  apply closure_minimal
  · intro x hx
    exact ⟨(hstrip x hx).1.le, (hstrip x hx).2.le⟩
  · exact (isClosed_le continuous_const (continuous_apply j)).inter
      (isClosed_le (continuous_apply j) continuous_const)

/-- One-sided barrier estimate, with the exact exponential constant
(BB Prop 6.1, p. 249). -/
theorem le_barrier_estimate_of_barrier
    {X : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ)}
    (j : Fin N) {γ d : ℝ} (hγ : 0 ≤ γ)
    (hbar : ∀ z, sumSquaresWithDrift X (fun z => Real.exp (γ * z j)) z = Real.exp (γ * z j))
    {U : Set (Fin N → ℝ)} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hstrip : ∀ x ∈ U, -d < x j ∧ x j < d)
    {f : (Fin N → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) (hs : tsupport f ⊆ U)
    (hX : ∀ i : Fin q, DifferentiableOn ℝ (X i.succ) U)
    {M : ℝ} (hM : 0 ≤ M) (hP : ∀ z ∈ U, -M ≤ sumSquaresWithDrift X f z)
    (x : Fin N → ℝ) (hx : x ∈ closure U) :
    f x ≤ M * (Real.exp (2 * γ * d) - 1) := by
  let g := exponentialBarrier j γ d
  have hg : ContDiff ℝ 2 g := contDiff_exponentialBarrier j γ d
  let w : (Fin N → ℝ) → ℝ := f + fun z => -M * g z
  have hw : ContDiff ℝ 2 w := hf.add (contDiff_const.mul hg)
  have hPw : ∀ z ∈ U, 0 ≤ sumSquaresWithDrift X w z := by
    intro z hz
    have hzX := fun i => (hX i z hz).differentiableAt (hU.mem_nhds hz)
    change 0 ≤ sumSquaresWithDrift X (f + fun z => -M * g z) z
    rw [sumSquares_add_at hf.contDiffAt (contDiff_const.mul hg).contDiffAt hzX,
      congrFun (sumSquares_const_mul X (-M) g) z,
      sumSquares_exponentialBarrier_of_barrier j γ d hbar z hzX]
    have he : 1 ≤ Real.exp (γ * (z j + d)) := by
      simpa only [Real.exp_zero] using Real.exp_le_exp.mpr
        (mul_nonneg hγ (by linarith [(hstrip z hz).1]))
    nlinarith [hP z hz]
  have hboundary : ∀ z ∈ frontier U, w z ≤ 0 := by
    intro z hz
    have hzout : z ∉ U := by
      have H : z ∈ closure U ∧ z ∉ U := by
        simpa only [frontier, hU.interior_eq, Set.mem_sdiff] using hz
      exact H.2
    have hfz : f z = 0 := image_eq_zero_of_notMem_tsupport (fun ht => hzout (hs ht))
    have hg0 := (exponentialBarrier_bounds j hγ z
      (closure_slab_subset j hstrip (frontier_subset_closure hz))).1
    change f z + -M * g z ≤ 0
    rw [hfz, zero_add]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hM) hg0
  have hwx := weak_comparison_boundary_of_barrier j γ hbar hU hUb hw.contDiffOn
    hw.continuous.continuousOn hX hPw hboundary x hx
  have hgb := (exponentialBarrier_bounds j hγ x (closure_slab_subset j hstrip hx)).2
  change f x + -M * g x ≤ 0 at hwx
  calc
    f x ≤ M * g x := by linarith
    _ ≤ M * (Real.exp (2 * γ * d) - 1) := mul_le_mul_of_nonneg_left hgb hM

/-- The absolute barrier estimate for every compact C2 input,
valid for the operator and its drift-reversed transpose (BB Prop 6.1,
Prop 6.9, pp. 249, 256–257). -/
theorem abs_le_barrier_estimate_of_barrier
    {X : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ)}
    (j : Fin N) {γ d : ℝ} (hγ : 0 ≤ γ)
    (hbar : ∀ z, sumSquaresWithDrift X (fun z => Real.exp (γ * z j)) z = Real.exp (γ * z j))
    {U : Set (Fin N → ℝ)} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hstrip : ∀ x ∈ U, -d < x j ∧ x j < d)
    {f : (Fin N → ℝ) → ℝ} (hf : ContDiff ℝ 2 f) (hs : tsupport f ⊆ U)
    (hX : ∀ i : Fin q, DifferentiableOn ℝ (X i.succ) U)
    {M : ℝ} (hM : 0 ≤ M) (hP : ∀ z ∈ U, |sumSquaresWithDrift X f z| ≤ M)
    (x : Fin N → ℝ) (hx : x ∈ closure U) :
    |f x| ≤ M * (Real.exp (2 * γ * d) - 1) := by
  have hup := le_barrier_estimate_of_barrier j hγ hbar hU hUb hstrip hf hs hX hM
    (fun z hz => (abs_le.mp (hP z hz)).1) x hx
  have hneg : ∀ z ∈ U, -M ≤ sumSquaresWithDrift X (-f) z := by
    intro z hz
    have he : (fun z => -1 * f z) = -f := by funext z; simp only [neg_one_mul, Pi.neg_apply]
    have H := congrFun (sumSquares_const_mul X (-1) f) z
    rw [he, neg_one_mul] at H
    rw [H]
    linarith [(abs_le.mp (hP z hz)).2]
  have hfneg : ContDiff ℝ 2 (-f) := hf.neg
  have hsneg : tsupport (-f) ⊆ U := by rw [tsupport_neg]; exact hs
  have hlo := le_barrier_estimate_of_barrier j hγ hbar hU hUb hstrip hfneg
    hsneg hX hM hneg x hx
  change -f x ≤ _ at hlo
  exact abs_le.mpr ⟨by linarith, hup⟩

end RothschildStein.H1
