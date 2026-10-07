-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.FixedLayerRepresentation
public import RothschildStein.G3.CorrectionProductAlgebra
@[expose] public section
noncomputable section
open scoped BigOperators
namespace RothschildStein.G3

def quasiCorrectionSlotCount (a s : ℕ) (p : Fin a → ℕ+) (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range n, Fintype.card (LayerWord a s p (k+1))

end RothschildStein.G3
