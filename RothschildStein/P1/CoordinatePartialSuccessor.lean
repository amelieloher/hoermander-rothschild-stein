-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G2.CoordinateIntegration
public import RothschildStein.S.FieldGermExtension
public import RothschildStein.S.WordDerivativeGerms

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set TopologicalSpace
open scoped Topology BigOperators
namespace RothschildStein.P1

/-- The coordinate word contains
precisely α(j) occurrences of coordinate j. -/
theorem coordinateWord_count {N : ℕ} (α : Fin N → ℕ) (j : Fin N) :
    (G2.coordinateWord α).count j = α j := by
  classical
  rw [G2.coordinateWord, List.count_flatMap]
  simp only [Function.comp_def, List.count_replicate]
  have hs := (List.sum_toFinset (fun i : Fin N => if i == j then α i else 0)
    (List.nodup_finRange N)).symm
  rw [List.toFinset_finRange] at hs
  exact hs.trans (by simp)

/-- Adding one coordinate derivative gives
the precise successor multi-index, up to coordinate-word permutation. -/
theorem coordinateWord_successor_perm {N : ℕ} (α : Fin N → ℕ) (j : Fin N) :
    (j :: G2.coordinateWord α).Perm (G2.coordinateWord (α + Pi.single j 1)) := by
  classical
  apply List.perm_iff_count.mpr
  intro i
  rw [List.count_cons, coordinateWord_count, coordinateWord_count]
  by_cases h : i = j
  · subst i
    simp
  · simp [Pi.add_apply, h, Ne.symm h]

/-- The derivative of an actual smooth
multi-index partial is the successor multi-index partial, using the
existing commutation theorem for coordinate derivatives (BB p. 549). -/
theorem euclideanPartial_coordinate_successor {N : ℕ} (α : Fin N → ℕ) (j : Fin N)
    (f : (Fin N → ℝ) → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    (fun x => fderiv ℝ (euclideanPartial α f) x (Pi.single j 1)) =
      euclideanPartial (α + Pi.single j 1) f := by
  have h := congrArg (fun g : G2.SmoothScalar N => g.1)
    (G2.coordinateWord_perm (j :: G2.coordinateWord α)
      (G2.coordinateWord (α + Pi.single j 1)) (coordinateWord_successor_perm α j) ⟨f, hf⟩)
  rw [G2.coordinateWord_coe, G2.coordinateWord_coe] at h
  simp only [List.foldr_cons] at h
  exact h

/-- The same successor identity holds for a
function smooth only on an open domain, including a punctured pole.
The proof uses the existing smooth germ extension and word locality
(BB Lemma 11.18, p. 549). -/
theorem euclideanPartial_coordinate_successor_local {N : ℕ}
    (U : Opens (Fin N → ℝ)) (α : Fin N → ℕ) (j : Fin N)
    (f : (Fin N → ℝ) → ℝ) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f (U : Set (Fin N → ℝ)))
    (x : Fin N → ℝ) (hx : x ∈ U) :
    fderiv ℝ (euclideanPartial α f) x (Pi.single j 1) =
      euclideanPartial (α + Pi.single j 1) f x := by
  obtain ⟨g, hg, he⟩ := S.exists_global_scalar_germ_extension U
    ⟨{x}, isCompact_singleton⟩ (by
      intro y hy
      change y = x at hy
      subst y
      change x ∈ U
      exact hx) f hf
  have heq := he x (by simp)
  have hp : euclideanPartial α g =ᶠ[𝓝 x] euclideanPartial α f := by
    simpa only [G2.coordinate_word_partial] using
      S.wordDerivative_eventuallyEq G2.coordinateFields (G2.coordinateWord α) heq
  have hβ : euclideanPartial (α + Pi.single j 1) g x =
      euclideanPartial (α + Pi.single j 1) f x := by
    simpa only [G2.coordinate_word_partial] using
      (S.wordDerivative_eventuallyEq G2.coordinateFields
        (G2.coordinateWord (α + Pi.single j 1)) heq).eq_of_nhds
  calc
    _ = fderiv ℝ (euclideanPartial α g) x (Pi.single j 1) :=
      congrArg (fun L => L (Pi.single j 1)) (hp.fderiv_eq (𝕜 := ℝ)).symm
    _ = euclideanPartial (α + Pi.single j 1) g x :=
      congrFun (euclideanPartial_coordinate_successor α j g hg) x
    _ = _ := hβ

end RothschildStein.P1
