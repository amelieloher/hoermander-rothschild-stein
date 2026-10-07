-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.HolderSpaces
public import Mathlib.Topology.Algebra.Order.LiminfLimsup

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set Filter
open scoped ENNReal NNReal Topology
namespace RothschildStein.H3
variable {X : Type*} [MetricSpace X]

/-- The shared Hölder seminorm is the supremum of its
pointwise quotients, with zero contribution on the diagonal. -/
theorem holderSemi_eq_iSup {a : ℝ≥0} (A : Set X) (f : X → ℝ) :
    H2.holderSemi a A f = ⨆ x : A, ⨆ y : A,
      ENNReal.ofReal |f x - f y| / ENNReal.ofReal (dist x y ^ (a : ℝ)) := by
  let S := ⨆ x : A, ⨆ y : A,
    ENNReal.ofReal |f x - f y| / ENNReal.ofReal (dist x y ^ (a : ℝ))
  have hquot : S ≤ H2.holderSemi a A f := by
    by_cases ht : H2.holderSemi a A f = ⊤
    · rw [ht]; exact le_top
    apply iSup_le; intro x; apply iSup_le; intro y
    have hb := H2.sub_le_holderSemi (lt_top_iff_ne_top.mpr ht) x.property y.property
    have hp : 0 ≤ dist x y ^ (a : ℝ) := Real.rpow_nonneg dist_nonneg _
    have he : ENNReal.ofReal |f x - f y| ≤
        H2.holderSemi a A f * ENNReal.ofReal (dist x y ^ (a : ℝ)) := by
      rw [← ENNReal.ofReal_toReal ht, ← ENNReal.ofReal_mul ENNReal.toReal_nonneg]
      exact ENNReal.ofReal_le_ofReal hb
    exact ENNReal.div_le_of_le_mul he
  apply le_antisymm ?_ hquot
  by_cases ht : S = ⊤
  · rw [ht]; exact le_top
  have hb : ∀ x ∈ A, ∀ y ∈ A, |f x - f y| ≤ S.toReal * dist x y ^ (a : ℝ) := by
    intro x hx y hy
    by_cases hxy : x = y
    · subst y; simp; positivity
    have hd : 0 < dist x y := dist_pos.mpr hxy
    have hp : 0 < dist x y ^ (a : ℝ) := Real.rpow_pos_of_pos hd _
    have hq : ENNReal.ofReal |f x - f y| /
        ENNReal.ofReal (dist x y ^ (a : ℝ)) ≤ S :=
      (le_iSup_of_le (⟨x, hx⟩ : A) (le_iSup_of_le (⟨y, hy⟩ : A) le_rfl))
    have he := (ENNReal.div_le_iff (by simpa using hp) (by simp)).mp hq
    have hr := ENNReal.toReal_mono (ENNReal.mul_ne_top ht (by simp)) he
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _),
      ENNReal.toReal_ofReal hp.le, Subtype.dist_eq] using hr
  have he := H2.holderSemi_le_of_bound ENNReal.toReal_nonneg hb
  simpa only [ENNReal.ofReal_toReal ht] using he

/-- The full bounded Hölder norm is lower semicontinuous
for pointwise convergence, including infinite norm values. -/
theorem boundedHolderNorm_le_liminf {a : ℝ≥0} {A : Set X}
    {u : ℕ → X → ℝ} {f : X → ℝ}
    (hu : ∀ x ∈ A, Tendsto (fun n => u n x) atTop (𝓝 (f x))) :
    H2.boundedHolderNorm a A f ≤
      liminf (fun n => H2.boundedHolderNorm a A (u n)) atTop := by
  classical
  by_cases hA : A.Nonempty
  · let : Nonempty A := hA.to_subtype
    unfold H2.boundedHolderNorm H2.holderSup
    rw [holderSemi_eq_iSup, ENNReal.iSup_add]
    apply iSup_le; intro z
    rw [ENNReal.add_iSup]; apply iSup_le; intro x
    rw [ENNReal.add_iSup]; apply iSup_le; intro y
    have hz : Tendsto (fun n => ENNReal.ofReal |u n z|) atTop
        (𝓝 (ENNReal.ofReal |f z|)) :=
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp ((hu z z.property).abs)
    have hq : Tendsto (fun n => ENNReal.ofReal |u n x - u n y| /
        ENNReal.ofReal (dist x y ^ (a : ℝ))) atTop
        (𝓝 (ENNReal.ofReal |f x - f y| /
          ENNReal.ofReal (dist x y ^ (a : ℝ)))) := by
      by_cases hxy : x = y
      · subst y; simp
      · exact ENNReal.Tendsto.div_const
          (ENNReal.continuous_ofReal.continuousAt.tendsto.comp
            (((hu x x.property).sub (hu y y.property)).abs))
          (Or.inr (by simpa using
            (Real.rpow_pos_of_pos (dist_pos.mpr hxy) (a : ℝ))))
    rw [← (hz.add hq).liminf_eq]
    exact liminf_le_liminf (Eventually.of_forall fun n => by
      apply add_le_add
      · exact le_iSup (fun z : A => ENNReal.ofReal |u n z|) z
      · rw [holderSemi_eq_iSup]
        exact le_iSup_of_le x (le_iSup_of_le y le_rfl))
  · have he : A = ∅ := not_nonempty_iff_eq_empty.mp hA
    subst A
    simp [H2.boundedHolderNorm, H2.holderSup, holderSemi_eq_iSup]

end RothschildStein.H3
