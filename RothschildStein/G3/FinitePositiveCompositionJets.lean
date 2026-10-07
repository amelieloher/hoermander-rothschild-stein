-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.LinearReparametrizedJets

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set

namespace RothschildStein.G3

/-- Finite-order local composition uses only positive jets at the actual
intermediate point, with the numerical factorial budget. -/
theorem norm_local_finite_positive_composition_jet_le {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {n : ℕ} {S : Set F} {T : Set E} (hS : IsOpen S) (hT : IsOpen T)
    {f : F → G} {g : E → F}
    (hf : ContDiffOn ℝ n f S) (hg : ContDiffOn ℝ n g T)
    (hmap : MapsTo g T S) {x : E} (hx : x ∈ T) (hn : 1 ≤ n)
    {M D : ℝ} (hM : 0 ≤ M) (hD : 1 ≤ D)
    (hfjet : ∀ j, 1 ≤ j → j ≤ n → ‖iteratedFDeriv ℝ j f (g x)‖ ≤ M)
    (hgjet : ∀ j, 1 ≤ j → j ≤ n → ‖iteratedFDeriv ℝ j g x‖ ≤ D) :
    ‖iteratedFDeriv ℝ n (f ∘ g) x‖ ≤ n.factorial * M * D ^ n := by
  let H : F → G := fun y => f y - f (g x)
  have hH : ContDiffOn ℝ n H S := hf.sub contDiffOn_const
  have hHjet : ∀ j ≤ n, ‖iteratedFDerivWithin ℝ j H S (g x)‖ ≤ M := by
    intro j hj
    rw [iteratedFDerivWithin_of_isOpen _ hS (hmap hx)]
    cases j with
    | zero => simpa [H, norm_iteratedFDeriv_zero] using hM
    | succ j =>
      rw [show H = (fun y => f y - f (g x)) from rfl,
        fun_iteratedFDeriv_sub_apply
          ((hf.contDiffAt (hS.mem_nhds (hmap hx))).of_le (by exact_mod_cast hj)) contDiffAt_const,
        iteratedFDeriv_succ_const, Pi.zero_apply, sub_zero]
      exact hfjet (j + 1) (by omega) hj
  have hh := norm_iteratedFDerivWithin_comp_le hH hg (n := n) le_rfl
    hS.uniqueDiffOn hT.uniqueDiffOn hmap hx hHjet (fun j hj hjn => by
      rw [iteratedFDerivWithin_of_isOpen _ hT hx]
      exact (hgjet j hj hjn).trans (le_self_pow₀ hD (by omega)))
  rw [iteratedFDerivWithin_of_isOpen _ hT hx] at hh
  have heq : iteratedFDeriv ℝ n (H ∘ g) x = iteratedFDeriv ℝ n (f ∘ g) x := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [Nat.add_comm 1 k]
    change iteratedFDeriv ℝ (k + 1) (fun y => (f ∘ g) y - f (g x)) x = _
    rw [fun_iteratedFDeriv_sub_apply
      (((hf.comp hg hmap).contDiffAt (hT.mem_nhds hx)).of_le
        (by exact_mod_cast (show k + 1 ≤ 1 + k by omega))) contDiffAt_const,
      iteratedFDeriv_succ_const, Pi.zero_apply, sub_zero]
  rw [heq] at hh
  exact hh

end RothschildStein.G3
