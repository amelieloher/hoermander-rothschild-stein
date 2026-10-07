-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.SmoothDependenceVariationalFlow
public import RothschildStein.G1.SmoothDependenceAssembly

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
open scoped ContDiff Topology

namespace RothschildStein.G1

universe u

/-- Finite-order joint regularity of a continuous local flow,
by the independently constructed variation and induction on the order
(BB Proposition 1.2, p. 3). -/
theorem flowRegularity_nat (n : ℕ) : FlowRegularity.{u} n := by
  induction n with
  | zero =>
    intro E _ _ _ _ Ω U τ hΩ hU hτ Z hZ Φ hc hinit hsol
    exact contDiffOn_zero.mpr hc
  | succ n ih =>
    intro E _ _ _ _ Ω U τ hΩ hU hτ Z hZ Φ hc hinit hsol
    have horder : (n : ℕ∞ω) + 1 = ((n + 1 : ℕ) : ℕ∞ω) := by simp
    have hZs : ContDiffOn ℝ ((n : ℕ∞ω) + 1) Z Ω := horder.symm ▸ hZ
    have hZ1 : ContDiffOn ℝ 1 Z Ω := hZs.of_le (by exact_mod_cast Nat.le_add_left 1 n)
    apply (hU.prod isOpen_Ioo).contDiffOn_iff.mpr
    intro p hp
    let T := (|p.2| + τ) / 2
    have habs : |p.2| < τ := abs_lt.mpr hp.2
    have hT : 0 < T := by dsimp [T]; linarith [abs_nonneg p.2]
    have hTτ : T < τ := by dsimp [T]; linarith
    have hpT : p.2 ∈ Ioo (-T) T := by
      apply abs_lt.mp
      dsimp [T]
      linarith
    have hclosed : Icc (-T) T ⊆ Ioo (-τ) τ := by
      intro t ht
      constructor <;> linarith [ht.1, ht.2]
    have hcc : ContinuousOn Φ (U ×ˢ Icc (-T) T) := hc.mono (prod_mono Subset.rfl hclosed)
    obtain ⟨r, hr, hrU, K, B, hB, hK, hLip⟩ := exists_local_flow_bounds hΩ hU hZ1 hT hcc
      (fun x hx t ht => (hsol x hx t (hclosed ht)).2) hinit
      (fun x hx t ht => (hsol x hx t (hclosed ht)).1) hp.1
    have hcb : ContinuousOn Φ (ball p.1 r ×ˢ Icc (-T) T) :=
      hcc.mono (prod_mono hrU Subset.rfl)
    obtain ⟨J, hcJ, hJ⟩ := exists_initial_variation_family hΩ isOpen_ball hZ1 hT hB hcb
      (fun x hx t ht => (hsol x (hrU hx) t (hclosed ht)).2)
      (fun x hx => hinit x (hrU hx))
      (fun x hx t ht => (hsol x (hrU hx) t (hclosed ht)).1) hLip hK
    have hco : ContinuousOn Φ (ball p.1 r ×ˢ Ioo (-T) T) :=
      hcb.mono (prod_mono Subset.rfl Ioo_subset_Icc_self)
    have hso : ∀ x ∈ ball p.1 r, ∀ t ∈ Ioo (-T) T,
        Φ (x, t) ∈ Ω ∧ HasDerivAt (fun v => Φ (x, v)) (Z (Φ (x, t))) t :=
      fun x hx t ht => hsol x (hrU hx) t (hclosed (Ioo_subset_Icc_self ht))
    have hΦn := ih hΩ isOpen_ball hT (hZs.of_le (by simp)) hco
      (fun x hx => hinit x (hrU hx)) hso
    have hJn := initial_variation_contDiffOn_of_lower_order ih hΩ isOpen_ball hZs hT hco
      (fun x hx => hinit x (hrU hx)) hso hcJ (fun x hx => (hJ x hx).1)
      (fun x hx t ht => ((hJ x hx).2 t (Ioo_subset_Icc_self ht)).2)
    have hfull := flow_contDiffOn_succ_of_first_variation
      (Φ := fun x t => Φ (x, t)) (isOpen_ball.prod isOpen_Ioo)
      (hZs.of_le (by simp)) hΦn (fun q hq => (hso q.1 hq.1 q.2 hq.2).1) hJn
      (fun q hq => ((hJ q.1 hq.1).2 q.2 (Ioo_subset_Icc_self hq.2)).1)
      (fun q hq => (hso q.1 hq.1 q.2 hq.2).2)
    exact (horder ▸ hfull).contDiffAt
      ((isOpen_ball.prod isOpen_Ioo).mem_nhds ⟨mem_ball_self hr, hpT⟩)

end RothschildStein.G1
