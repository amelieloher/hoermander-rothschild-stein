-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.L1.FiberParameterization

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace RothschildStein.L1

/-- The actual fiber of a chart image is the vertical
parameter image. Horizontal uniqueness identifies its parameter preimage
(BB pp. 520–521). -/
theorem fiber_chart_image_eq {E F : Type*} {U : Set (E × F)} {Q : Set F}
    (Φ : E × F → E × F) (θ : E × F → E) (y : E)
    (hinj : ∀ v, InjOn (fun u => (Φ (u, v)).1) {u | (u, v) ∈ U})
    (hmap : ∀ v ∈ Q, (θ (y, v), v) ∈ U)
    (hbase : ∀ v ∈ Q, (Φ (θ (y, v), v)).1 = y) :
    {z : F | (y, z) ∈ Φ '' (U ∩ Prod.snd ⁻¹' Q)} =
      (fun v => (Φ (θ (y, v), v)).2) '' Q := by
  ext z
  constructor
  · rintro ⟨⟨u, v⟩, ⟨hu, hv⟩, he⟩
    have hfirst : (Φ (u, v)).1 = y := congrArg Prod.fst he
    have hθ : θ (y, v) = u := hinj v (hmap v hv) hu
      ((hbase v hv).trans hfirst.symm)
    refine ⟨v, hv, ?_⟩
    change (Φ (θ (y, v), v)).2 = z
    rw [hθ]
    exact congrArg Prod.snd he
  · rintro ⟨v, hv, he⟩
    exact ⟨(θ (y, v), v), ⟨hmap v hv, hv⟩, Prod.ext (hbase v hv) he⟩

end RothschildStein.L1
