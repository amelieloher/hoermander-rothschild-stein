-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HeatKernel.Poincare.CarnotChainIntegral
public import HeatKernel.Poincare.CarnotWhitneyRadiusSum
public import HeatKernel.Poincare.CarnotSegment
public import HeatKernel.Poincare.CarnotWhitneyOverlap

/-! Oscillation bounds paid by every ball meeting a radial segment. -/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric MeasureTheory RothschildStein
open scoped NNReal ENNReal BigOperators Classical

namespace HeatKernel

/-- A simple path inside a finite radial meeting family bounds the oscillation by
the total nonnegative cost of that entire family. -/
theorem lintegral_abs_sub_rpow_le_radial_meeting_cost {N q : ℕ}
    (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (hw : ∀ k : Fin q, G.weight (Fin.castLE hq k) = 1)
    {x : CarnotPoint G hq hqpos hspan} {r κ p : ℝ}
    (C : Set (CarnotPoint G hq hqpos hspan)) (hr : 0 < r) (hκ : 80 < κ)
    (hCU : C ⊆ ball x r)
    (hcover : ball x r = ⋃ w ∈ C, ball w (5 * (infDist w (ball x r)ᶜ / κ)))
    (z z₀ : C) (hroot : x ∈ ball z₀.val (5 * (infDist z₀.val (ball x r)ᶜ / κ)))
    (a c : C → ℝ) (haeq : ∀ w, a w = infDist w.val (ball x r)ᶜ / κ)
    (h : C → ℝ≥0) (hp : 1 ≤ p) (u : (Fin N → ℝ) → ℝ)
    (hlocal : ∀ w, eLpNorm (fun y => u y - c w) (ENNReal.ofReal p)
      (volume.restrict (horizontalBall (G.horizontalFields hq) w.val (20 * a w))) ≤
      ENNReal.ofReal (((2 : ℝ) ^ G.homogeneousDimension) ^ (1 / p) * (3 * (20 * a w))) *
        volume (horizontalBall (G.horizontalFields hq) w.val (a w)) ^ (1 / p) * h w)
    (hedge : ∀ w v, (ball w.val (5 * a w) ∩ ball v.val (5 * a v)).Nonempty →
      |c w - c v| ≤ (60 * (((2 : ℝ) ^ G.homogeneousDimension) ^ (1 / p)) ^ 2) *
        (a w * (h w : ℝ) + a v * (h v : ℝ)))
    {γ : Icc (0 : ℝ) 1 → CarnotPoint G hq hqpos hspan}
    (hzero : γ ⟨0, by norm_num⟩ = z.val) (hone : γ ⟨1, by norm_num⟩ = x)
    (hγ : ∀ t v, dist (γ t) (γ v) = dist z.val x * dist t v)
    (s : Finset C) (hmem : ∀ w : C, w ∈ s ↔ (ball w.val (5 * a w) ∩ range γ).Nonempty)
    (hf : AEStronglyMeasurable (fun y => u y - c z₀)
      (volume.restrict (horizontalBall (G.horizontalFields hq) z.val (5 * a z)))) :
    (∫⁻ y in horizontalBall (G.horizontalFields hq) z.val (5 * a z),
      ENNReal.ofReal (|u y - c z₀| ^ p)) ≤
      ENNReal.ofReal ((3 * (60 * (((2 : ℝ) ^ G.homogeneousDimension) ^ (1 / p)) ^ 2)) ^ p) *
        ENNReal.ofReal ((5 : ℝ) ^ G.homogeneousDimension) *
        volume (horizontalBall (G.horizontalFields hq) z.val (a z)) *
        ENNReal.ofReal ((∑ w ∈ s, a w * (h w : ℝ)) ^ p) := by
  classical
  obtain ⟨y, hy⟩ := CarnotPoint.exists_dist_eq G hq hqpos hspan hw x hr
  have hcompl : (ball x r)ᶜ.Nonempty := by
    refine ⟨y, ?_⟩
    change ¬ dist y x < r
    rw [dist_comm, hy]
    exact lt_irrefl r
  have hκ0 : 0 < κ := by linarith
  have ha : ∀ w : C, 0 < a w := by
    intro w
    rw [haeq w]
    exact div_pos ((isOpen_ball.isClosed_compl.notMem_iff_infDist_pos hcompl).mp
      (by simpa using hCU w.property)) hκ0
  have heqa : a = fun w : C => infDist w.val (ball x r)ᶜ / κ := funext haeq
  subst a
  let I := boundaryBallsMeetingPath C (ball x r) κ γ
  obtain ⟨hzI, hrootI, path, hpath⟩ := exists_simple_boundaryBall_chain hκ0 hcompl hCU
    hcover z.property z₀.property hroot hzero hone hγ
  let f : I → C := fun w => ⟨w.val, w.property.1⟩
  have hfinj : Function.Injective f := fun _ _ heq =>
    Subtype.ext (congrArg (fun w : C => w.val) heq)
  let a := fun w : C => infDist w.val (ball x r)ᶜ / κ
  have hbound := lintegral_abs_sub_rpow_le_horizontal_chain_cost (ι := I)
    G hq hqpos hspan hw (fun w : I => w.val) (a ∘ f) (c ∘ f) (h ∘ f)
    (fun w => ha (f w)) hp u (fun w => hlocal (f w))
    (fun w v hv => hedge (f w) (f v) hv)
    (i := ⟨z.val, hzI⟩) (j := ⟨z₀.val, hrootI⟩) path hpath hf
  let t := path.support.toFinset.image f
  have hts : t ⊆ s := by
    intro w hw'
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.mp hw'
    apply (hmem (f v)).mpr
    exact v.property.2
  have hsum : (∑ w ∈ path.support.toFinset, a (f w) * (h (f w) : ℝ)) ≤
      ∑ w ∈ s, a w * (h w : ℝ) := by
    have heq : (∑ w ∈ t, a w * (h w : ℝ)) =
        ∑ w ∈ path.support.toFinset, a (f w) * (h (f w) : ℝ) :=
      Finset.sum_image (fun _ _ _ _ h' => hfinj h')
    rw [← heq]
    exact Finset.sum_le_sum_of_subset_of_nonneg hts (fun w _ _ => mul_nonneg (ha w).le (h w).2)
  have hpow := Real.rpow_le_rpow
    (Finset.sum_nonneg (fun w _ => mul_nonneg (ha (f w)).le (h (f w)).2)) hsum
    (le_trans zero_le_one hp)
  have hfin : @List.toFinset I (Classical.decEq I) path.support = path.support.toFinset := by
    ext v
    simp
  rw [hfin] at hbound
  exact hbound.trans (mul_le_mul_right (ENNReal.ofReal_le_ofReal hpow) _)

end HeatKernel
