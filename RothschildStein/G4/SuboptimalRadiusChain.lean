-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G4.RequestedIntervalChain
public import RothschildStein.G4.SuboptimalRadiusIntervals

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace RothschildStein.G4

/-- The actual frame intervals give a bounded nonrepeating
chain from the reference frame to the requested small-radius frame.
Switching radii decrease strictly except for the final target switch;
each intervening radius interval remains suboptimal
(BB (9.56)–(9.57), p. 454). -/
theorem exists_suboptimal_radius_chain {ι : Type*} [Fintype ι] {n : ℕ}
    (Z : ι → (Fin n → ℝ) → (Fin n → ℝ)) (w : ι → ℕ+)
    (x : Fin n → ℝ) {t r R : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hr : 0 < r) (hrR : r ≤ R)
    (hspan : ∃ B : Fin n → ι, frameDet Z B x ≠ 0)
    (B₀ Btarget : Fin n → ι)
    (hstart : IsSuboptimal Z w B₀ x t R) (htarget : IsSuboptimal Z w Btarget x t r) :
    let S := fun B : Fin n → ι => Icc r R ∩ {ρ : ℝ | IsSuboptimal Z w B x t ρ}
    ∃ l : List (Fin n → ι),
      l.IsChain (fun B C => IsSuboptimal Z w B x t (sInf (S B)) ∧
        (∀ ρ ∈ Icc (sInf (S C)) (sInf (S B)), IsSuboptimal Z w C x t ρ) ∧
        (C ≠ Btarget → sInf (S C) < sInf (S B))) ∧
      l.head? = some B₀ ∧ l.getLast? = some Btarget ∧
      (∀ C ∈ l, sInf (S C) ∈ Icc r R ∧ IsSuboptimal Z w C x t (sInf (S C))) ∧
      (∀ ρ ∈ Icc (sInf (S B₀)) R, IsSuboptimal Z w B₀ x t ρ) ∧
      l.Nodup ∧ l.length ≤ Fintype.card ι ^ n := by
  intro S
  have hS : ∀ B, IsClosed (S B) := fun B =>
    (isCompact_restricted_suboptimal_radii Z w B x t r R).isClosed
  have hbound : ∀ B, S B ⊆ Icc r R := fun _ => inter_subset_left
  have hcover : Icc r R ⊆ ⋃ B, S B := by
    intro ρ hρ
    obtain ⟨B, hB⟩ := exists_suboptimal_frame Z w ht1 (hr.trans_le hρ.1) hspan
    exact mem_iUnion.mpr ⟨B, hρ, hB⟩
  have hstartS : R ∈ S B₀ := ⟨⟨hrR, le_rfl⟩, hstart⟩
  have htargetS : r ∈ S Btarget := ⟨⟨le_rfl, hrR⟩, htarget⟩
  obtain ⟨l, hchain, hhead, hlast, hmembers, hnodup, hlength⟩ :=
    exists_requested_interval_overlap_chain S hS hbound hcover B₀ Btarget hstartS htargetS
  have hendpoint : ∀ C ∈ l, sInf (S C) ∈ S C := fun C hC =>
    (closed_radius_interval_left_endpoint (hS C) (hmembers C hC) (hbound C)).1
  have hbetween : ∀ C, sInf (S C) ∈ S C → ∀ a ∈ S C,
      ∀ ρ ∈ Icc (sInf (S C)) a, IsSuboptimal Z w C x t ρ := by
    intro C hleft a ha ρ hρ
    exact ((ordConnected_suboptimal_radii Z w C x ht).out
      ⟨hr.trans_le hleft.1.1, hleft.2⟩ ⟨hr.trans_le ha.1.1, ha.2⟩ hρ).2
  have hfirst : sInf (S B₀) ∈ S B₀ :=
    (closed_radius_interval_left_endpoint (hS B₀) ⟨R, hstartS⟩ (hbound B₀)).1
  refine ⟨l, ?_, hhead, hlast, ?_, hbetween B₀ hfirst R hstartS, hnodup, ?_⟩
  · exact List.IsChain.imp_of_mem_imp (fun B C hB hC hBC =>
      ⟨(hendpoint B hB).2, hbetween C (hendpoint C hC) (sInf (S B)) hBC.1, hBC.2⟩) hchain
  · intro C hC
    exact hendpoint C hC
  · simpa only [Fintype.card_fun, Fintype.card_fin] using hlength

end RothschildStein.G4
