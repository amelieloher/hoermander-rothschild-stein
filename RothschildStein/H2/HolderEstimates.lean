-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H2.HolderSpaces
public import Mathlib.Topology.MetricSpace.Bounded

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set Metric
open scoped ENNReal NNReal

namespace RothschildStein.H2
variable {X : Type*} [MetricSpace X]

/-- The product seminorm has the usual two-term bound (BB p. 298). -/
theorem holderSemi_mul_le {δ : ℝ≥0} {A : Set X} {f g : X → ℝ}
    (hf : BoundedHolder δ A f) (hg : BoundedHolder δ A g) :
    holderSemi δ A (fun x => f x * g x) ≤
      holderSup A f * holderSemi δ A g + holderSup A g * holderSemi δ A f := by
  have hf' := hf.parts
  have hg' := hg.parts
  have hbound := holderSemi_le_of_bound (δ := δ) (A := A)
    (f := fun x => f x * g x)
    (H := (holderSup A f).toReal * (holderSemi δ A g).toReal +
      (holderSup A g).toReal * (holderSemi δ A f).toReal) (by positivity)
  have he := hbound (by
    intro x hx y hy
    have hid : f x * g x - f y * g y = f x * (g x - g y) + g y * (f x - f y) := by ring
    rw [hid]
    calc
      _ ≤ |f x * (g x - g y)| + |g y * (f x - f y)| := abs_add_le _ _
      _ ≤ (holderSup A f).toReal * ((holderSemi δ A g).toReal * dist x y ^ (δ : ℝ)) +
          (holderSup A g).toReal * ((holderSemi δ A f).toReal * dist x y ^ (δ : ℝ)) := by
        simp only [abs_mul]
        exact add_le_add
          (mul_le_mul (abs_le_holderSup hf'.1 hx) (sub_le_holderSemi hg'.2 hx hy)
            (abs_nonneg _) ENNReal.toReal_nonneg)
          (mul_le_mul (abs_le_holderSup hg'.1 hy) (sub_le_holderSemi hf'.2 hx hy)
            (abs_nonneg _) ENNReal.toReal_nonneg)
      _ = _ := by ring)
  simpa only [ENNReal.ofReal_add (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
    (mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg),
    ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal hf'.1.ne, ENNReal.ofReal_toReal hf'.2.ne,
    ENNReal.ofReal_toReal hg'.1.ne, ENNReal.ofReal_toReal hg'.2.ne] using he

omit [MetricSpace X] in
/-- The supremum term is submultiplicative. -/
theorem holderSup_mul_le {A : Set X} {f g : X → ℝ}
    (hf : holderSup A f < ⊤) (hg : holderSup A g < ⊤) :
    holderSup A (fun x => f x * g x) ≤ holderSup A f * holderSup A g := by
  have h := holderSup_le_of_bound (A := A) (f := fun x => f x * g x)
    (M := (holderSup A f).toReal * (holderSup A g).toReal) (by
      intro x hx
      rw [abs_mul]
      exact mul_le_mul (abs_le_holderSup hf hx) (abs_le_holderSup hg hx)
        (abs_nonneg _) ENNReal.toReal_nonneg)
  simpa only [ENNReal.ofReal_mul ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal hf.ne, ENNReal.ofReal_toReal hg.ne] using h

/-- The full bounded Hölder norm is submultiplicative. -/
theorem boundedHolderNorm_mul_le {δ : ℝ≥0} {A : Set X} {f g : X → ℝ}
    (hf : BoundedHolder δ A f) (hg : BoundedHolder δ A g) :
    boundedHolderNorm δ A (fun x => f x * g x) ≤
      boundedHolderNorm δ A f * boundedHolderNorm δ A g := by
  calc
    _ ≤ holderSup A f * holderSup A g +
        (holderSup A f * holderSemi δ A g + holderSup A g * holderSemi δ A f) :=
      add_le_add (holderSup_mul_le hf.parts.1 hg.parts.1) (holderSemi_mul_le hf hg)
    _ ≤ _ := by
      unfold boundedHolderNorm
      rw [add_mul, mul_add, mul_add]
      calc
        _ = (holderSup A f * holderSup A g + holderSup A f * holderSemi δ A g) +
          holderSemi δ A f * holderSup A g := by ac_rfl
        _ ≤ _ := add_le_add_right (le_add_right (le_rfl :
          holderSemi δ A f * holderSup A g ≤ holderSemi δ A f * holderSup A g)) _

/-- The bounded Hölder class is stable under multiplication. -/
theorem BoundedHolder.mul {δ : ℝ≥0} {A : Set X} {f g : X → ℝ}
    (hf : BoundedHolder δ A f) (hg : BoundedHolder δ A g) :
    BoundedHolder δ A (fun x => f x * g x) :=
  (boundedHolderNorm_mul_le hf hg).trans_lt (ENNReal.mul_lt_top hf hg)

/-- Decreasing the exponent on a set of diameter at most D.
This includes zero diameter without dividing by a power of D. -/
theorem holderSemi_le_diameter_bound {δ γ : ℝ≥0} {A : Set X} {f : X → ℝ}
    {D : ℝ≥0} (hd : ∀ x ∈ A, ∀ y ∈ A, dist x y ≤ D)
    (hδγ : δ ≤ γ) (hf : holderSemi γ A f < ⊤) :
    holderSemi δ A f ≤ (D : ℝ≥0∞) ^ ((γ : ℝ) - δ) * holderSemi γ A f := by
  have hm : MemHolder γ (fun x : A => f x) := eHolderNorm_lt_top.mp hf
  have hh : HolderWith (nnHolderNorm γ (fun x : A => f x) * D ^ ((γ : ℝ) - δ)) δ
      (fun x : A => f x) := hm.holderWith.of_le (by
        intro x y
        rw [edist_dist, ← ENNReal.ofReal_coe_nnreal]
        exact ENNReal.ofReal_le_ofReal (hd x x.property y y.property)) hδγ
  have he := hh.eHolderNorm_le
  simpa only [holderSemi, ENNReal.coe_mul,
    ENNReal.coe_rpow_of_nonneg _ (sub_nonneg.mpr (show (δ : ℝ) ≤ γ from hδγ)),
    hm.coe_nnHolderNorm_eq_eHolderNorm, mul_comm] using he

/-- The diameter formulation of the exponent comparison. -/
theorem holderSemi_le_diam {δ γ : ℝ≥0} {A : Set X} {f : X → ℝ}
    (hA : Bornology.IsBounded A) (hδγ : δ ≤ γ) (hf : holderSemi γ A f < ⊤) :
    holderSemi δ A f ≤ ENNReal.ofReal (diam A ^ ((γ : ℝ) - δ)) * holderSemi γ A f := by
  have he := holderSemi_le_diameter_bound (D := Real.toNNReal (diam A))
    (fun x hx y hy => (dist_le_diam_of_mem hA hx hy).trans (Real.le_coe_toNNReal _)) hδγ hf
  simpa only [← ENNReal.ofReal_coe_nnreal, Real.coe_toNNReal', max_eq_left diam_nonneg,
    ENNReal.ofReal_rpow_of_nonneg diam_nonneg
      (sub_nonneg.mpr (show (δ : ℝ) ≤ γ from hδγ))] using he

/-- The full norm comparison includes the supremum term. -/
theorem boundedHolderNorm_le_diam {δ γ : ℝ≥0} {A : Set X} {f : X → ℝ}
    (hA : Bornology.IsBounded A) (hδγ : δ ≤ γ) (hf : BoundedHolder γ A f) :
    boundedHolderNorm δ A f ≤
      ENNReal.ofReal (max 1 (diam A ^ ((γ : ℝ) - δ))) * boundedHolderNorm γ A f := by
  let C := ENNReal.ofReal (max 1 (diam A ^ ((γ : ℝ) - δ)))
  have h₁ : (1 : ℝ≥0∞) ≤ C := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (le_max_left 1 _)
  have h₂ : ENNReal.ofReal (diam A ^ ((γ : ℝ) - δ)) ≤ C :=
    ENNReal.ofReal_le_ofReal (le_max_right _ _)
  change holderSup A f + holderSemi δ A f ≤ C * (holderSup A f + holderSemi γ A f)
  rw [mul_add]
  exact add_le_add (by simpa only [one_mul] using mul_le_mul_left h₁ (holderSup A f))
    ((holderSemi_le_diam hA hδγ hf.parts.2).trans
      (mul_le_mul_left h₂ (holderSemi γ A f)))

/-- Lipschitz functions have the asserted Hölder bound on a bounded set. -/
theorem LipschitzWith.holderSemi_le_diam {L δ : ℝ≥0} {A : Set X} {f : X → ℝ}
    (hl : LipschitzWith L f) (hA : Bornology.IsBounded A) (hδ : δ ≤ 1) :
    holderSemi δ A f ≤ (L : ℝ≥0∞) * ENNReal.ofReal (diam A ^ (1 - (δ : ℝ))) := by
  have hh : HolderWith L 1 (fun x : A => f x) :=
    by simpa only [mul_one, Function.comp_def] using
      (hl.comp (LipschitzWith.subtype_val A)).holderWith
  have hs : holderSemi 1 A f ≤ L := hh.eHolderNorm_le
  have he := RothschildStein.H2.holderSemi_le_diam hA hδ (hs.trans_lt ENNReal.coe_lt_top)
  simpa only [NNReal.coe_one, mul_comm] using
    he.trans (mul_le_mul_right hs (ENNReal.ofReal (diam A ^ (1 - (δ : ℝ)))))

end RothschildStein.H2
