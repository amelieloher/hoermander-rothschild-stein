-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.SuboptimalRadiusChain

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace RothschildStein.G4

/-- Convert the attained suboptimal interval chain to the exact
actual chart-transfer relation: both frames are suboptimal at the old
switching radius and the next switching radius is no larger. The final
requested frame has left endpoint exactly r (BB p. 454). -/
theorem exists_actual_suboptimal_transfer_chain {ι : Type*} [Fintype ι] {n : ℕ}
    (Z : ι → (Fin n → ℝ) → (Fin n → ℝ)) (w : ι → ℕ+)
    (x : Fin n → ℝ) {t r R : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hr : 0 < r) (hrR : r ≤ R)
    (hspan : ∃ B : Fin n → ι, frameDet Z B x ≠ 0)
    (B₀ Btarget : Fin n → ι)
    (hstart : IsSuboptimal Z w B₀ x t R) (htarget : IsSuboptimal Z w Btarget x t r) :
    let S := fun B : Fin n → ι => Icc r R ∩ {ρ : ℝ | IsSuboptimal Z w B x t ρ}
    ∃ l : List (Fin n → ι),
      l.IsChain (fun B C => IsSuboptimal Z w B x t (sInf (S B)) ∧
        IsSuboptimal Z w C x t (sInf (S B)) ∧ sInf (S C) ≤ sInf (S B)) ∧
      l.head? = some B₀ ∧ l.getLast? = some Btarget ∧
      (∀ C ∈ l, sInf (S C) ∈ Icc r R ∧ IsSuboptimal Z w C x t (sInf (S C))) ∧
      sInf (S Btarget) = r ∧
      (∀ ρ ∈ Icc (sInf (S B₀)) R, IsSuboptimal Z w B₀ x t ρ) ∧
      l.Nodup ∧ l.length ≤ Fintype.card ι ^ n := by
  intro S
  obtain ⟨l, hchain, hhead, hlast, hmembers, hfirst, hnodup, hlength⟩ :=
    exists_suboptimal_radius_chain Z w x ht ht1 hr hrR hspan B₀ Btarget hstart htarget
  have htargetS : r ∈ S Btarget := ⟨⟨le_rfl, hrR⟩, htarget⟩
  have hleft := closed_radius_interval_left_endpoint
    (isCompact_restricted_suboptimal_radii Z w Btarget x t r R).isClosed
    ⟨r, htargetS⟩ (show S Btarget ⊆ Icc r R from inter_subset_left)
  have htargetInf : sInf (S Btarget) = r :=
    le_antisymm (hleft.2.2 r htargetS) hleft.2.1
  refine ⟨l, ?_, hhead, hlast, hmembers, htargetInf, hfirst, hnodup, hlength⟩
  apply List.IsChain.imp_of_mem_imp _ hchain
  intro B C hB _hC hBC
  have hscale : sInf (S C) ≤ sInf (S B) := by
    by_cases hCt : C = Btarget
    · subst C
      rw [htargetInf]
      exact (hmembers B hB).1.1
    · exact (hBC.2.2 hCt).le
  exact ⟨hBC.1, hBC.2.1 _ ⟨hscale, le_rfl⟩, hscale⟩

end RothschildStein.G4
