-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Form.PositivePart
public import Mathlib.Algebra.Order.Group.MinMax

/-! # Horizontal gradients vanish on the zero level -/

@[expose] public section

noncomputable section

open Set MeasureTheory TopologicalSpace

namespace HeatKernel

/-- Every horizontal derivative vanishes almost everywhere on the zero level of an
energy-domain function. -/
theorem energyGraph_gradient_zero_on_zero {N q : ℕ}
    (X : Fin q → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) (v : energyGraph (N := N) ⊤ X) (i : Fin q) :
    ∀ᵐ x ∂volume, (v : GradientSpace (N := N) ⊤ q).fst x = 0 →
      (v : GradientSpace (N := N) ⊤ q).snd i x = 0 := by
  let U : Opens (Fin N → ℝ) := ⊤
  obtain ⟨p, hpf, hpg⟩ := exists_energyGraph_positivePart X hX v
  obtain ⟨n, hnf, hng⟩ := exists_energyGraph_positivePart X hX (-v)
  simp only [Submodule.coe_neg, WithLp.neg_fst, WithLp.neg_snd, PiLp.neg_apply] at hnf hng
  have hneg : (-(v : GradientSpace U q).fst : SpatialL2 U) =ᵐ[volume]
      fun x => -(v : GradientSpace U q).fst x := by
    simpa only [U, Opens.coe_top, Measure.restrict_univ, Pi.neg_def] using
      Lp.coeFn_neg (v : GradientSpace U q).fst
  have hsub : ((p : GradientSpace U q).fst - (n : GradientSpace U q).fst : SpatialL2 U) =ᵐ[volume]
      fun x => (p : GradientSpace U q).fst x - (n : GradientSpace U q).fst x := by
    simpa only [U, Opens.coe_top, Measure.restrict_univ, Pi.sub_def] using
      Lp.coeFn_sub (p : GradientSpace U q).fst (n : GradientSpace U q).fst
  have heq : p - n = v := by
    apply energyGraph_fst_injective U X (fun j => (hX j).contDiffOn)
    change (p : GradientSpace U q).fst - (n : GradientSpace U q).fst = (v : GradientSpace U q).fst
    apply Lp.ext
    have H : ((p : GradientSpace U q).fst - (n : GradientSpace U q).fst : SpatialL2 U) =ᵐ[volume]
        (v : GradientSpace U q).fst := by
      filter_upwards [hsub, hpf, hnf, hneg] with x hx hpx hnx hnegx
      rw [hx, hpx, hnx, hnegx]
      exact max_zero_sub_max_neg_zero_eq_self _
    simpa only [U, Opens.coe_top, Measure.restrict_univ] using H
  have hgi : (p : GradientSpace U q).snd i - (n : GradientSpace U q).snd i =
      (v : GradientSpace U q).snd i :=
    congrArg (fun z : energyGraph U X => (z : GradientSpace U q).snd i) heq
  have hsubg : (v : GradientSpace U q).snd i =ᵐ[volume]
      fun x => (p : GradientSpace U q).snd i x - (n : GradientSpace U q).snd i x := by
    rw [← hgi]
    simpa only [U, Opens.coe_top, Measure.restrict_univ, Pi.sub_def] using
      Lp.coeFn_sub ((p : GradientSpace U q).snd i) ((n : GradientSpace U q).snd i)
  filter_upwards [hsubg, hpg i, hng i, hneg] with x hx hpx hnx hnegx
  intro hvx
  have hpz : (p : GradientSpace U q).snd i x = 0 := by simpa [hvx] using hpx
  have hnz : (n : GradientSpace U q).snd i x = 0 := by
    rw [hnegx, hvx, neg_zero] at hnx
    simpa only [lt_self_iff_false, ite_false] using hnx
  simpa only [hpz, hnz, sub_zero] using hx

end HeatKernel
