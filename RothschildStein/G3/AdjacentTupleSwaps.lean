-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module
public import RothschildStein.G3.LeadingPairSchwarz
public import Mathlib.GroupTheory.Perm.Sign

@[expose] public section
noncomputable section
namespace RothschildStein.G3

theorem tuple_swap_leading {E : Type*} {n : ℕ} (u : Fin (n + 2) → E) :
    (fun j => u (Equiv.swap (0 : Fin (n + 2)) 1 j)) =
      Fin.cons (u 1) (Fin.cons (u 0) (Fin.tail (Fin.tail u))) := by
  ext j
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun k => ?_) j) j
  · simp
  · simp
  · have hk : k.succ.succ ≠ (1 : Fin (n + 2)) := by
      intro h; have hv := congrArg Fin.val h; simp at hv
    simp [Equiv.swap_apply_def, Fin.tail, hk]

theorem tuple_swap_succ {E : Type*} {n : ℕ} (u : Fin (n + 2) → E) (i : Fin n) :
    (fun j => u (Equiv.swap i.succ.castSucc i.succ.succ j)) =
      Fin.cons (u 0) (fun j => Fin.tail u (Equiv.swap i.castSucc i.succ j)) := by
  ext j
  refine Fin.cases ?_ (fun j => ?_) j
  · have ha : (0 : Fin (n + 2)) ≠ i.castSucc.succ := by
      intro h; have hv := congrArg Fin.val h; simp at hv
    have hb : (0 : Fin (n + 2)) ≠ i.succ.succ := by
      intro h; have hv := congrArg Fin.val h; simp at hv
    simp [Equiv.swap_apply_def, ha, hb]
  · simp only [Equiv.swap_apply_def, Fin.cons_succ, Fin.tail,
      Fin.castSucc_succ, Fin.succ_inj]
    split_ifs <;> rfl

end RothschildStein.G3
