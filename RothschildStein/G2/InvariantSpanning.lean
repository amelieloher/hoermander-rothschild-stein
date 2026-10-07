-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.PolynomialBasisInverse
public import RothschildStein.G2.InvariantBracket
public import Hormander.Interface.LieAlgebraSpansOn

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false

@[expose] public section
noncomputable section
namespace RothschildStein.G2
open scoped BigOperators
variable {N : ℕ} (G : HomogeneousGroup N)

/-- Invariant fields spanning at the identity span at every point
(BB pp. 124, 135; the triangular inverse supplies surjectivity explicitly). -/
theorem invariant_spanning_everywhere {ι : Type*}
    (V : ι → (Fin N → ℝ) → (Fin N → ℝ))
    (hV : ∀ i, IsLeftInvariantField G (V i))
    (hspan : Submodule.span ℝ (Set.range (fun i => V i 0)) = ⊤) (x : Fin N → ℝ) :
    Submodule.span ℝ (Set.range (fun i => V i x)) = ⊤ := by
  let S := Submodule.span ℝ (Set.range (fun i => V i x))
  have hd : ∀ v, leftField G v x ∈ S := by
    intro v
    have hv : v ∈ Submodule.span ℝ (Set.range (fun i => V i 0)) := by rw [hspan]; trivial
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨i, rfl⟩ := hv
      rw [← hV i |>.eq_leftField G]
      exact Submodule.subset_span ⟨i, rfl⟩
    | zero =>
      change fderiv ℝ (G.mul x) 0 0 ∈ S
      rw [map_zero]; exact S.zero_mem
    | add v w hv hw ihv ihw =>
      change fderiv ℝ (G.mul x) 0 (v + w) ∈ S
      rw [map_add]; exact S.add_mem ihv ihw
    | smul c v hv ih =>
      change fderiv ℝ (G.mul x) 0 (c • v) ∈ S
      rw [map_smul]; exact S.smul_mem c ih
  have hb : ∀ k, Hormander.Interface.basisVec k ∈ S := by
    intro k
    rw [coordinate_basis_expansion G k x]
    apply S.sum_mem
    intro i hi
    apply S.smul_mem
    rw [canonicalField_eq_leftField]
    exact hd _
  apply top_unique
  intro v _
  have he : v = ∑ k, v k • Hormander.Interface.basisVec k := by
    ext j
    simp [Hormander.Interface.basisVec, Pi.single_apply]
  rw [he]
  exact S.sum_mem fun k _ => S.smul_mem (v k) (hb k)

/-- Lie words in invariant generators remain invariant (BB Proposition 3.35, p. 114). -/
theorem lieWord_invariant {q : ℕ}
    (X : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, IsLeftInvariantField G (X i)) (w : Hormander.Interface.LieWord q) :
    IsLeftInvariantField G (Hormander.Interface.LieWord.eval X w) := by
  induction w with
  | generator i => exact hX i
  | bracket a b iha ihb => exact iha.lieBracket G ihb

/-- The origin bracket-span condition implies the exact all-points bracket-span condition
(BB pp. 124, 135). -/
theorem lieAlgebraSpansOn_of_origin {q : ℕ}
    (X : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, IsLeftInvariantField G (X i))
    (hspan : Submodule.span ℝ (Set.range (fun w : Hormander.Interface.LieWord q =>
      Hormander.Interface.LieWord.eval X w 0)) = ⊤) :
    Hormander.Interface.LieAlgebraSpansOn Set.univ X := by
  intro x _
  exact invariant_spanning_everywhere G _ (lieWord_invariant G X hX) hspan x

end RothschildStein.G2
