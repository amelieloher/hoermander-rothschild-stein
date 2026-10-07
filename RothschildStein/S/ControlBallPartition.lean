-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.CompactSmoothPartition
public import RothschildStein.S.DistanceRealLaws
public import RothschildStein.S.TestWordHolderBounds

set_option autoImplicit false
set_option relaxedAutoImplicit false
@[expose] public section
noncomputable section
open Set TopologicalSpace
open scoped BigOperators ENNReal
namespace RothschildStein.S
variable {n m : ℕ}

/-- Compactly supported smooth cutoffs on doubled control balls sum to one on the smaller balls and have finite Hölder norm (BB (2.23), p. 85). -/
theorem exists_finite_control_ball_partition
    (Ω : Opens (Fin n → ℝ)) (G : DistanceGeometry Ω)
    (centers : Fin m → Ω) {r α κ : ℝ} (hr : 0 < r)
    (hα : 0 < α) (hα1 : α ≤ 1) (V : Set (Fin n → ℝ))
    (hcompact : IsCompact (closure V)) (hclosure : closure V ⊆ Ω)
    (hκ : DistanceComparison G.d V κ)
    (hballs : ∀ i,{z | z ∈ (Ω : Set (Fin n → ℝ)) ∧ G.d (centers i).val z < ENNReal.ofReal (2*r)} ⊆ V) :
    ∃ ζ : Fin m → (Fin n → ℝ) → ℝ,
      (∀ i,ContDiff ℝ (⊤ : ℕ∞) (ζ i) ∧ HasCompactSupport (ζ i) ∧
        tsupport (ζ i) ⊆ {z | z ∈ (Ω : Set (Fin n → ℝ)) ∧ G.d (centers i).val z < ENNReal.ofReal (2*r)} ∧
        holderENorm G.d α {z | z ∈ (Ω : Set (Fin n → ℝ)) ∧ G.d (centers i).val z < ENNReal.ofReal (2*r)} (ζ i) < ∞) ∧
      ∀ x ∈ ⋃ i,{z | z ∈ (Ω : Set (Fin n → ℝ)) ∧ G.d (centers i).val z < ENNReal.ofReal r},∑ i,ζ i x = 1 := by
  let B := fun i : Fin m => {z | z ∈ (Ω : Set (Fin n → ℝ)) ∧ G.d (centers i).val z < ENNReal.ofReal r}
  let D := fun i : Fin m => {z | z ∈ (Ω : Set (Fin n → ℝ)) ∧ G.d (centers i).val z < ENNReal.ofReal (2*r)}
  have hrad : ENNReal.ofReal r < ENNReal.ofReal (2*r) :=
    (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by linarith)
  have hBD : ∀ i,B i ⊆ D i := fun i z hz => ⟨hz.1,hz.2.trans hrad⟩
  have hBV : (⋃ i,B i) ⊆ V := by
    intro z hz
    obtain ⟨i,hi⟩ := mem_iUnion.mp hz
    exact hballs i (hBD i hi)
  have hcl : ∀ i,closure (B i) ⊆ D i := by
    intro i
    have hclV : closure (B i) ⊆ closure V := closure_mono ((hBD i).trans (hballs i))
    have ht := G.ambient_closure_ball_subset (centers i) (ENNReal.ofReal r) (hclV.trans hclosure)
    exact fun z hz => ⟨(ht hz).1,(ht hz).2.trans_lt hrad⟩
  let K : Compacts (Fin n → ℝ) := ⟨closure (⋃ i,B i),
    hcompact.of_isClosed_subset isClosed_closure (closure_mono hBV)⟩
  have hcover : (K : Set (Fin n → ℝ)) ⊆ ⋃ i,D i := by
    change closure (⋃ i,B i) ⊆ ⋃ i,D i
    rw [closure_iUnion_of_finite]
    exact iUnion_mono hcl
  obtain ⟨ζ,hζ,hsum⟩ := exists_compact_smooth_finite_partition K D
    (fun i => G.isOpen_ball (centers i) (ENNReal.ofReal (2*r))) hcover
  refine ⟨ζ,?_,fun x hx => hsum x (subset_closure hx)⟩
  intro i
  refine ⟨(hζ i).1,(hζ i).2.1,(hζ i).2.2,?_⟩
  have hc : DistanceComparison G.d (D i) κ := ⟨hκ.1,fun x hx y hy => hκ.2 x (hballs i hx) y (hballs i hy)⟩
  exact holderENorm_lt_top_of_smooth_compact_comparison G.d (D i) hc hα hα1 (hζ i).1 (hζ i).2.1

end RothschildStein.S
