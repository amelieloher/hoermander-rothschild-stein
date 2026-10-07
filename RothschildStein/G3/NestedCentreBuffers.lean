-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.UniformBufferDomains
@[expose] public section
noncomputable section
open Set Metric
namespace RothschildStein.G3

theorem centreBuffer_self_mem {N : ℕ} {K : Set (Fin N → ℝ)}
    {r : ℝ} (hr : 0 < r) {x : Fin N → ℝ} (hx : x ∈ K) :
    x ∈ centreBuffer K r :=
  mem_centreBuffer_iff.mpr ⟨x,hx,by simpa using hr⟩

end RothschildStein.G3
