-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.ControlSeparation

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace RothschildStein.G1

/-- The control distance gives an extended metric on the domain
before connectivity is proved. This explicit structure supplies its own
intrinsic topology alongside the Euclidean subtype metric
(BB Prop 1.41, pp. 22–23). -/
@[instance_reducible]
def controlEMetricSpace {m n : ℕ} {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω)
    (w : Fin m → ℕ+) (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContinuousOn (X i) Ω) : EMetricSpace Ω :=
  { PseudoEMetricSpace.ofEDist (fun x y : Ω => controlDistance Ω w X x.val y.val)
      (fun x => controlDistance_self w X x.property)
      (fun x y => controlDistance_symm Ω w X x.val y.val)
      (fun x y z => controlDistance_triangle Ω w X x.val y.val z.val) with
    eq_of_edist_eq_zero := fun h => Subtype.ext ((controlDistance_eq_zero_iff hΩ w X hX
      (Subtype.property _)).mp h) }

/-- The extended metric structure uses exactly the control
distance (BB Def 1.38, p. 21). -/
theorem controlEMetricSpace_edist {m n : ℕ} {Ω : Set (Fin n → ℝ)} (hΩ : IsOpen Ω)
    (w : Fin m → ℕ+) (X : Fin m → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContinuousOn (X i) Ω) (x y : Ω) :
    @edist Ω (controlEMetricSpace hΩ w X hX).toPseudoEMetricSpace.toEDist x y =
      controlDistance Ω w X x.val y.val := rfl

end RothschildStein.G1
