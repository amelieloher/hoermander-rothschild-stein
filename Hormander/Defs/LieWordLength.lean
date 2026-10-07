-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Hormander.Interface.LieWord

@[expose] public section

namespace Hormander

open Hormander.Interface

/-- The ordinary length of a Lie word: its number of generator leaves (the drift `X 0`
counts once, like every other generator). -/
def lieWordLength {k : ℕ} : LieWord k → ℕ
  | .generator _ => 1
  | .bracket p q => lieWordLength p + lieWordLength q

end Hormander
