-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H3.IntrinsicWordInputCongruence
public import RothschildStein.Definitions.holderXENorm

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter TopologicalSpace
open scoped Topology ENNReal BigOperators
namespace RothschildStein.H3

/-- Intrinsic first derivatives restrict to an open subdomain;
continuity of the chosen integral curve supplies its smaller-domain germ. -/
theorem intrinsic_derivative_restrict {N : ℕ}
    (U V : Opens (Fin N → ℝ)) (hVU : (V : Set (Fin N → ℝ)) ⊆ U)
    (X : (Fin N → ℝ) → (Fin N → ℝ)) {f g : (Fin N → ℝ) → ℝ}
    (hg : hasIntrinsicDeriv U X f g) : hasIntrinsicDeriv V X f g := by
  intro x hx
  obtain ⟨⟨γ, h0, hγ, _⟩, hall⟩ := hg x (hVU hx)
  refine ⟨⟨γ, h0, hγ, ?_⟩, ?_⟩
  · exact hγ.self_of_nhds.continuousAt.eventually_mem
      (V.isOpen.mem_nhds (by rw [h0]; exact hx))
  · intro γ' h0' hγ' hmem
    exact hall γ' h0' hγ' (hmem.mono (fun _ ht => hVU ht))

/-- Every iterated intrinsic word restricts, with the same representatives. -/
theorem intrinsic_word_restrict {N m : ℕ}
    (X : Fin m → (Fin N → ℝ) → (Fin N → ℝ))
    (U V : Opens (Fin N → ℝ)) (hVU : (V : Set (Fin N → ℝ)) ⊆ U)
    (I : List (Fin m)) {f g : (Fin N → ℝ) → ℝ}
    (hg : hasIntrinsicWordDeriv X U I f g) : hasIntrinsicWordDeriv X V I f g := by
  induction I generalizing g with
  | nil => exact hg.mono hVU
  | cons i I ih =>
    obtain ⟨h, hh, hd⟩ := hg
    exact ⟨h, ih hh, intrinsic_derivative_restrict U V hVU (X i) hd⟩

/-- The exact intrinsic infimum norm decreases on open subdomains. -/
theorem intrinsic_word_norm_restrict_le {N m : ℕ}
    (X : Fin m → (Fin N → ℝ) → (Fin N → ℝ))
    (d : (Fin N → ℝ) → (Fin N → ℝ) → ℝ≥0∞)
    (U V : Opens (Fin N → ℝ)) (hVU : (V : Set (Fin N → ℝ)) ⊆ U)
    (I : List (Fin m)) (α : ℝ) (f : (Fin N → ℝ) → ℝ) :
    intrinsicWordENorm X d V I α f ≤ intrinsicWordENorm X d U I α f := by
  unfold intrinsicWordENorm
  apply le_sInf
  rintro r ⟨g, hg, rfl⟩
  refine le_trans ?_ (S.holderENorm_mono d α U g hVU)
  exact sInf_le ⟨g, intrinsic_word_restrict X U V hVU I hg, rfl⟩

/-- The complete fixed weighted norm decreases on open subdomains. -/
theorem holderXENorm_restrict_le {N m : ℕ}
    (w : Fin m → ℕ+) (X : Fin m → (Fin N → ℝ) → (Fin N → ℝ))
    (d : (Fin N → ℝ) → (Fin N → ℝ) → ℝ≥0∞)
    (U V : Opens (Fin N → ℝ)) (hVU : (V : Set (Fin N → ℝ)) ⊆ U)
    (k : ℕ) (α : ℝ) (f : (Fin N → ℝ) → ℝ) :
    holderXENorm w X d V k α f ≤ holderXENorm w X d U k α f := by
  unfold holderXENorm
  exact Finset.sum_le_sum (fun I _ => intrinsic_word_norm_restrict_le X d U V hVU I α f)

/-- Fixed intrinsic Hölder membership restricts without choosing new jets. -/
theorem memHolderX_restrict_intrinsic {N m : ℕ}
    (w : Fin m → ℕ+) (X : Fin m → (Fin N → ℝ) → (Fin N → ℝ))
    (d : (Fin N → ℝ) → (Fin N → ℝ) → ℝ≥0∞)
    (U V : Opens (Fin N → ℝ)) (hVU : (V : Set (Fin N → ℝ)) ⊆ U)
    (k : ℕ) (α : ℝ) {f : (Fin N → ℝ) → ℝ}
    (hf : memHolderX w X d U k α f) : memHolderX w X d V k α f := by
  refine ⟨(S.holderENorm_mono d α U f hVU).trans_lt hf.1, ?_⟩
  intro I hI
  obtain ⟨g, hg, hn⟩ := hf.2 I hI
  exact ⟨g, intrinsic_word_restrict X U V hVU I hg,
    (S.holderENorm_mono d α U g hVU).trans_lt hn⟩

/-- On an open cutoff plateau, the complete local fixed norm
is bounded by the global localized norm, at every weighted order. -/
theorem cutoff_plateau_holderX_norm_le {N m : ℕ}
    (w : Fin m → ℕ+) (X : Fin m → (Fin N → ℝ) → (Fin N → ℝ))
    (d : (Fin N → ℝ) → (Fin N → ℝ) → ℝ≥0∞)
    (V : Opens (Fin N → ℝ)) (k : ℕ) (α : ℝ)
    (u φ : (Fin N → ℝ) → ℝ) (hφ : EqOn φ 1 (V : Set (Fin N → ℝ))) :
    holderXENorm w X d V k α u ≤
      holderXENorm w X d ⊤ k α (fun x => u x * φ x) := by
  have he : EqOn u (fun x => u x * φ x) (V : Set (Fin N → ℝ)) := by
    intro x hx
    simp only [hφ hx, Pi.one_apply, mul_one]
  have hn : holderXENorm w X d V k α u =
      holderXENorm w X d V k α (fun x => u x * φ x) := by
    unfold holderXENorm
    exact Finset.sum_congr rfl (fun I _ => intrinsic_word_norm_congr_input X d V I α he)
  exact hn.trans_le (holderXENorm_restrict_le w X d ⊤ V (subset_univ _) k α _)

end RothschildStein.H3
