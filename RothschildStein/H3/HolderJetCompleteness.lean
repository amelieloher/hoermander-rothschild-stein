-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.S.HolderCompleteness
public import RothschildStein.S.HolderUniformConvergence
public import RothschildStein.S.HolderContinuity
public import RothschildStein.S.Sobolev
public import RothschildStein.H3.IntrinsicWordUniformLimit
public import RothschildStein.Definitions.memHolderX

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set Filter TopologicalSpace
open scoped Topology ENNReal
namespace RothschildStein.H3

/-- Compatible weighted intrinsic jets that are Cauchy in a
positive Hölder norm have one compatible uniform jet limit. A common
bound in a second positive exponent gives membership in that exponent.
This is the direct Cauchy step of BB Proposition 8.58, pp. 386–387. -/
theorem exists_holder_jet_limit_of_cauchy {N m : ℕ}
    (Ω U : Opens (Fin N → ℝ)) (D : S.DistanceGeometry Ω)
    (hU : (U : Set (Fin N → ℝ)) ⊆ Ω)
    (w : Fin m → ℕ+) (X : Fin m → (Fin N → ℝ) → (Fin N → ℝ)) (k : ℕ)
    {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (F : ℕ → List (Fin m) → (Fin N → ℝ) → ℝ)
    (hder : ∀ n I, wordWeight w I ≤ k → hasIntrinsicWordDeriv X U I (F n []) (F n I))
    (hfinite : ∀ n I, wordWeight w I ≤ k →
      holderENorm D.d β (U : Set (Fin N → ℝ)) (F n I) < ⊤)
    (hcauchy : ∀ I, wordWeight w I ≤ k →
      S.holderCauchySeq D.d β (U : Set (Fin N → ℝ)) (fun n => F n I))
    (C : List (Fin m) → ℝ≥0∞)
    (hC : ∀ I, wordWeight w I ≤ k → C I < ⊤)
    (hbound : ∀ n I, wordWeight w I ≤ k →
      holderENorm D.d α (U : Set (Fin N → ℝ)) (F n I) ≤ C I) :
    ∃ jet : List (Fin m) → (Fin N → ℝ) → ℝ,
      memHolderX w X D.d U k α (jet []) ∧
      ∀ I, wordWeight w I ≤ k →
        hasIntrinsicWordDeriv X U I (jet []) (jet I) ∧
        holderENorm D.d α (U : Set (Fin N → ℝ)) (jet I) ≤ C I + C I ∧
        Tendsto (fun n => holderENorm D.d β (U : Set (Fin N → ℝ))
          (fun x => F n I x - jet I x)) atTop (𝓝 0) ∧
        TendstoUniformlyOn (fun n => F n I) (jet I) atTop (U : Set (Fin N → ℝ)) ∧
        ∀ x ∈ (U : Set (Fin N → ℝ)), Tendsto (fun n => F n I x) atTop (𝓝 (jet I x)) := by
  classical
  have hsep : ∀ x ∈ (U : Set (Fin N → ℝ)), ∀ y ∈ U, D.d x y = 0 → x = y := by
    intro x hx y hy hd
    exact congrArg Subtype.val ((D.distance_eq_zero_iff ⟨x, hU hx⟩ ⟨y, hU hy⟩).mp hd)
  have hex : ∀ I : List (Fin m), ∃ g : (Fin N → ℝ) → ℝ,
      wordWeight w I ≤ k →
        holderENorm D.d β (U : Set (Fin N → ℝ)) g < ⊤ ∧
        Tendsto (fun n => holderENorm D.d β (U : Set (Fin N → ℝ))
          (fun x => F n I x - g x)) atTop (𝓝 0) ∧
        ∀ x ∈ (U : Set (Fin N → ℝ)), Tendsto (fun n => F n I x) atTop (𝓝 (g x)) := by
    intro I
    by_cases hI : wordWeight w I ≤ k
    · obtain ⟨g, hg⟩ := S.exists_holderENorm_limit_of_cauchy D.d hβ
        (U : Set (Fin N → ℝ)) hsep (fun n => F n I)
        (fun n => hfinite n I hI) (hcauchy I hI)
      exact ⟨g, fun _ => hg⟩
    · exact ⟨0, fun h => (hI h).elim⟩
  choose jet hjet using hex
  have hu (I : List (Fin m)) (hI : wordWeight w I ≤ k) :
      TendstoUniformlyOn (fun n => F n I) (jet I) atTop (U : Set (Fin N → ℝ)) :=
    S.tendstoUniformlyOn_of_holderENorm_error_tendsto D.d β
      (U : Set (Fin N → ℝ)) (fun n => F n I) (jet I) (hjet I hI).2.1
  have hc (n : ℕ) (I : List (Fin m)) (hI : wordWeight w I ≤ k) :
      ContinuousOn (F n I) (U : Set (Fin N → ℝ)) :=
    S.continuousOn_of_holderENorm_lt_top_on_subset Ω D hU hβ (hfinite n I hI)
  have hi (I : List (Fin m)) (hI : wordWeight w I ≤ k) :
      hasIntrinsicWordDeriv X U I (jet []) (jet I) :=
    hasIntrinsicWordDeriv_of_uniform_jet_limits U X I F jet
      (fun n J hJ => hder n J ((S.wordWeight_sublist_le w hJ).trans hI))
      (fun n J hJ => hc n J ((S.wordWeight_sublist_le w hJ).trans hI))
      (fun J hJ => hu J ((S.wordWeight_sublist_le w hJ).trans hI))
  have hb (I : List (Fin m)) (hI : wordWeight w I ≤ k) :
      holderENorm D.d α (U : Set (Fin N → ℝ)) (jet I) ≤ C I + C I :=
    S.holderENorm_limit_le_add_self D.d hα (U : Set (Fin N → ℝ)) hsep
      (fun n => F n I) (jet I) (hjet I hI).2.2 (C I) (hC I hI)
      (Eventually.of_forall (fun n => hbound n I hI))
  have hbn (I : List (Fin m)) (hI : wordWeight w I ≤ k) :
      holderENorm D.d α (U : Set (Fin N → ℝ)) (jet I) < ⊤ :=
    (hb I hI).trans_lt (ENNReal.add_lt_top.mpr ⟨hC I hI, hC I hI⟩)
  refine ⟨jet, ⟨hbn [] (by simp [wordWeight]), ?_⟩, ?_⟩
  · intro I hI
    have hIk := (S.mem_wordFamily_iff w k I).mp hI
    exact ⟨jet I, hi I hIk, hbn I hIk⟩
  · intro I hI
    exact ⟨hi I hI, hb I hI, (hjet I hI).2.1, hu I hI, (hjet I hI).2.2⟩

end RothschildStein.H3
