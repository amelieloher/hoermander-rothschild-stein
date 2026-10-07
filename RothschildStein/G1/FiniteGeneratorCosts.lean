-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.GeneratorArcs
public import RothschildStein.G1.WeightedTriangle

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
open scoped ENNReal

namespace RothschildStein.G1

/-- A finite generator path preserves domain membership, including
its reversed edges (BB Theorem 1.45, p. 34). -/
theorem FiniteGeneratorPath.mem_iff {m n : ℕ} {Ω : Set (Fin n → ℝ)}
    {X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)} {x y : Fin n → ℝ}
    (h : FiniteGeneratorPath Ω X x y) : x ∈ Ω ↔ y ∈ Ω := by
  change Relation.EqvGen (IsGeneratorArc Ω X) x y at h
  induction h with
  | rel x y h => exact ⟨fun _ => h.endpoints_mem.2, fun _ => h.endpoints_mem.1⟩
  | refl x => rfl
  | symm x y h ih => exact ih.symm
  | trans x y z hxy hyz ihxy ihyz => exact ihxy.trans ihyz

/-- Finitely many actual generator arcs have finite total
weighted control distance, using reversal and triangle inequalities
(BB Theorem 1.45, p. 34). -/
theorem FiniteGeneratorPath.controlDistance_ne_top {m n : ℕ} {Ω : Set (Fin n → ℝ)}
    {X : Fin m → (Fin n → ℝ) → (Fin n → ℝ)} (w : Fin m → ℕ+)
    {x y : Fin n → ℝ} (h : FiniteGeneratorPath Ω X x y) (hx : x ∈ Ω) :
    controlDistance Ω w X x y ≠ ∞ := by
  change Relation.EqvGen (IsGeneratorArc Ω X) x y at h
  induction h with
  | rel x y h => exact h.controlDistance_ne_top w
  | refl x => simpa only [controlDistance_self w X hx] using ENNReal.zero_ne_top
  | symm x y h ih =>
      rw [controlDistance_symm]
      exact ih ((FiniteGeneratorPath.mem_iff h).mpr hx)
  | trans x y z hxy hyz ihxy ihyz =>
      have hy : y ∈ Ω := (FiniteGeneratorPath.mem_iff hxy).mp hx
      exact ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨ihxy hx, ihyz hy⟩)
        (controlDistance_triangle Ω w X x y z)

end RothschildStein.G1
