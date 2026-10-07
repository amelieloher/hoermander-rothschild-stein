-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.A.Mollifier.WeakLimit
public import Hormander.E.OneStepFinal.EnergyLimit

/-!
# Mollifier converse for Sobolev regularity

The weak-limit converse for mollification shows that bounded Sobolev norms pass to the limit
when the mollified distributions converge on Schwartz tests.
-/

@[expose] public section

namespace Hormander.E

/-- BB Lemma 5.21(2): a tempered
distribution whose mollifications at all small scales lie in `H^s` with norm at most `C` lies
in `H^s` with norm at most `C`. -/
theorem _root_.Hormander.A.mollifierConverse (N : ℕ) : MollifierConverse N :=
  fun _s T _C _δ₀ hδ₀ h => (Hormander.A.mollifier_weak_limit_converse T hδ₀ h).1

end Hormander.E
