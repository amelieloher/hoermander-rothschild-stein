-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.TransferCoverCore
public import RothschildStein.P2.TransferCoverHolderCover
public import RothschildStein.P2.TransferCoverSobolev
public import RothschildStein.P2.TransferCoverHolder

/-!
# Transfer and finite cover: from the lifted local estimates to the original domain

Entry point for the `TransferCover*` modules (BB pp. 585-587, Thms 11.42-11.43; BB pp. 600-602,
Thms 11.57-11.58).

* `TransferCoverCore`: the operator `L̃ = ∑ X̃_{J i}` as a family of words (`driftOpWords`,
  `noDriftOpWords`; `HasWeakOperatorValue`, `HasIntrinsicOperatorValue`), the open `ρ`-balls
  `rhoBallOpen` of the chart centre, the comparison `ν ∘ Θ ≍ d̃`
  (`exists_gauge_comparison`) and the Euclidean openness of small base balls
  (`exists_isOpen_base_ball`).
* `TransferCoverSobolev`: `LiftedBaseSobolevEstimate` (the lifted base Sobolev estimate) and
  `sobolev_transfer_cover_of_lifted` (the second display: the original-domain estimate on
  `Ω' ⋐ Ω'' ⋐ Ω`, via the lifted norm transfer and a finite cover of `closure Ω'` by base balls with a lifted chart
  at each point); drift and no-drift instances.
* `TransferCoverHolderCover`, `TransferCoverHolder`: `LiftedBaseHolderEstimate` (the lifted estimate
  and `holder_finite_cover_of_lifted` (the original-domain Hölder estimate, via
  the Hölder transfer and the Lebesgue-number argument `holderENorm_le_of_cover`); drift and no-drift instances.
-/
