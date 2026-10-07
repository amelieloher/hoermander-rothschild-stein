-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.Measure
public import RothschildStein.G2.DilationMeasure

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

@[expose] public section
noncomputable section
namespace RothschildStein.G2
open MeasureTheory
variable {N : ℕ}

/-- A separate carrier for the homogeneous group law. The raw coordinate
space retains its existing pointwise algebra (BB Definition 3.1, p. 94). -/
def Carrier (_G : HomogeneousGroup N) := Fin N → ℝ

instance carrierGroup (G : HomogeneousGroup N) : Group (Carrier G) where
  mul := G.mul
  one := (0 : Fin N → ℝ)
  inv := G.inv
  mul_assoc := mul_assoc G
  one_mul := zero_mul G
  mul_one := mul_zero G
  inv_mul_cancel := inv_mul G

instance carrierMeasurableSpace (G : HomogeneousGroup N) : MeasurableSpace (Carrier G) :=
  inferInstanceAs (MeasurableSpace (Fin N → ℝ))

instance carrierMeasureSpace (G : HomogeneousGroup N) : MeasureSpace (Carrier G) :=
  inferInstanceAs (MeasureSpace (Fin N → ℝ))

end RothschildStein.G2
