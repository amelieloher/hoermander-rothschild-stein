-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.H1.PremiseAssembly
public import RothschildStein.G1.RankEquivalence
public import RothschildStein.G2.ControlRankBridge
public import RothschildStein.Definitions.bracketSpansOn
public import RothschildStein.G2.QuasiBounds
public import RothschildStein.Provider.CanonicalFields
public import RothschildStein.Definitions.sumSquares
public import RothschildStein.Definitions.sumSquaresTranspose

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped BigOperators Topology
namespace RothschildStein.Provider
variable {N q : ℕ}

/-- The given gauge supplies the standing homogeneous norm. -/
def gaugeHomogeneousNorm (G : HomogeneousGroup N) (ν : (Fin N → ℝ) → ℝ)
    (hν : G.IsHomogeneousGauge ν) : G2.HomogeneousNorm G := by
  let hb := G2.gauge_norm_bounds_of_groupIdentities (fun _ ht x => G2.inv_dilate G ht x) hν
  exact ⟨ν, hν, Classical.choose hb, (Classical.choose_spec hb).1,
    (Classical.choose_spec hb).2.1, (Classical.choose_spec hb).2.2⟩

/-- Standard words commute with relabelling the generators. -/
theorem wordBracket_relabel {m k : ℕ}
    (X : Fin m → (Fin N → ℝ) → (Fin N → ℝ))
    (Z : Fin k → (Fin N → ℝ) → (Fin N → ℝ)) (f : Fin m → Fin k)
    (hf : ∀ i, Z (f i) = X i) (I : List (Fin m)) :
    wordBracket Z (I.map f) = wordBracket X I := by
  induction I with
  | nil => rfl
  | cons i I ih =>
    cases I with
    | nil => simpa only [List.map_cons, List.map_nil, wordBracket] using hf i
    | cons j I =>
      change VectorField.lieBracket ℝ (Z (f i)) (wordBracket Z ((j :: I).map f)) = _
      rw [hf, ih]
      rfl

/-- At the origin the binary Lie words `Hormander.Interface.LieWord` span the tangent space,
by comparison with right-nested words. -/
theorem lieWord_span_origin (X : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (X i)) (hs : bracketSpansOn univ X) :
    Submodule.span ℝ (range (fun w : Hormander.Interface.LieWord q =>
      Hormander.Interface.LieWord.eval X w 0)) = ⊤ := by
  have he := G1.binary_span_eq_word_span isOpen_univ X
    (fun i => (hX i).contDiffOn) (x := 0) (mem_univ _)
  have hset : range (fun w : Hormander.Interface.LieWord q =>
      Hormander.Interface.LieWord.eval X w 0) =
      {v | ∃ w : Hormander.Interface.LieWord q, v = Hormander.lieWordEval X w 0} := by
    ext v
    constructor
    · rintro ⟨w, rfl⟩; exact ⟨w, congrFun (G2.lieWordEval_eq_frozen X w) 0 |>.symm⟩
    · rintro ⟨w, rfl⟩; exact ⟨w, congrFun (G2.lieWordEval_eq_frozen X w) 0 |>.symm⟩
  rw [hset, he]
  exact hs 0 (mem_univ _)

/-- A drift system in H1's standing class. -/
def driftStandingHypotheses (G : HomogeneousGroup N) (hq : q + 1 ≤ N) (hqpos : 0 < q)
    (hw : ∀ i : Fin q, G.weight ⟨i.val, lt_of_lt_of_le (Nat.lt_succ_of_lt i.isLt) hq⟩ = 1)
    (hw0 : G.weight ⟨q, lt_of_lt_of_le (Nat.lt_succ_self q) hq⟩ = 2)
    (hspan : bracketSpansOn univ (G.driftFields hq))
    (ν : (Fin N → ℝ) → ℝ) (hν : G.IsHomogeneousGauge ν) : H1.StandingHypotheses G q where
  q_pos := hqpos
  norm := gaugeHomogeneousNorm G ν hν
  fields := G.driftFields hq
  invariant i := by
    cases i using Fin.cases with
    | zero => exact G2.leftField_invariant G _
    | succ i => exact G2.leftField_invariant G _
  homogeneous i := by
    cases i using Fin.cases with
    | zero => simpa only [HomogeneousGroup.driftFields, Fin.cases_zero, hw0,
        Nat.cast_ofNat, ite_true] using G2.canonicalField_homogeneous G ⟨q, by omega⟩
    | succ i => simpa only [HomogeneousGroup.driftFields, Fin.cases_succ, hw,
        Nat.cast_one, Fin.succ_ne_zero, ite_false] using
        G2.canonicalField_homogeneous G ⟨i.val, by omega⟩
  horizontal_nonzero := by
    let i : Fin q := ⟨0, hqpos⟩
    refine ⟨i, ?_⟩
    intro he
    have hz := congrFun (congrFun he 0) (⟨i.val, by omega⟩ : Fin N)
    simp [HomogeneousGroup.driftFields, G2.canonicalField_eq_leftField,
      G2.leftField_zero, Hormander.Interface.basisVec] at hz
  span_origin := lieWord_span_origin _ (HomogeneousGroup.driftFields_contDiff G hq) hspan

/-- A system without drift uses a zero generator at index zero. -/
def horizontalStandingHypotheses (G : HomogeneousGroup N) (hq : q ≤ N) (hqpos : 0 < q)
    (hw : ∀ i : Fin q, G.weight (Fin.castLE hq i) = 1)
    (hspan : bracketSpansOn univ (G.horizontalFields hq))
    (ν : (Fin N → ℝ) → ℝ) (hν : G.IsHomogeneousGauge ν) : H1.StandingHypotheses G q where
  q_pos := hqpos
  norm := gaugeHomogeneousNorm G ν hν
  fields := Fin.cases 0 (G.horizontalFields hq)
  invariant i := by
    cases i using Fin.cases with
    | zero => intro x y; simp
    | succ i => exact G2.leftField_invariant G _
  homogeneous i := by
    cases i using Fin.cases with
    | zero => intro t ht x; simp [G2.dilate_zero]
    | succ i => simpa only [Fin.cases_succ, HomogeneousGroup.horizontalFields, hw,
        Nat.cast_one, Fin.succ_ne_zero, ite_false] using
        G2.canonicalField_homogeneous G (Fin.castLE hq i)
  horizontal_nonzero := by
    let i : Fin q := ⟨0, hqpos⟩
    refine ⟨i, ?_⟩
    intro he
    have hz := congrFun (congrFun he 0) (Fin.castLE hq i)
    simp [HomogeneousGroup.horizontalFields, G2.canonicalField_eq_leftField,
      G2.leftField_zero, Hormander.Interface.basisVec] at hz
  span_origin := by
    apply lieWord_span_origin
    · intro i
      cases i using Fin.cases with
      | zero => exact contDiff_const
      | succ i => exact HomogeneousGroup.horizontalFields_contDiff G hq i
    · intro x hx
      apply top_unique
      rw [← hspan x hx]
      apply Submodule.span_le.mpr
      rintro v ⟨I, hI, rfl⟩
      apply Submodule.subset_span
      refine ⟨I.map Fin.succ, by simpa using hI, ?_⟩
      exact (congrFun (wordBracket_relabel (G.horizontalFields hq)
        (Fin.cases 0 (G.horizontalFields hq)) Fin.succ (fun _ => rfl) I) x).symm

/-- Existence (BB Thm 6.18) and uniqueness (BB Thm 6.18 and Rem 6.17, p. 264) of the homogeneous
fundamental solution, as hypotheses. The norm and canonical-field comparisons are proved
independently of these inputs. -/
structure FundamentalSolutionInputs (G : HomogeneousGroup N) : Prop where
  existence : ∀ {q : ℕ} (H : H1.StandingHypotheses G q),
    2 < (G.homogeneousDimension : ℝ) → Nonempty (H1.FundamentalKernel G H)
  uniqueness : ∀ {q : ℕ} (H : H1.StandingHypotheses G q)
    (K : H1.FundamentalKernel G H), H1.DistributionalKernelUniqueness K
  uniqueness_atInfinity : ∀ {q : ℕ} (H : H1.StandingHypotheses G q)
    (K : H1.FundamentalKernel G H), H1.DistributionalKernelUniquenessAtInfinity K

/-- From existence and uniqueness, the fundamental kernel and its reflection both have the
properties `H1.FundamentalKernelProperties` of BB Thm 11.5. -/
theorem FundamentalSolutionInputs.kernel_pair {G : HomogeneousGroup N} (U : FundamentalSolutionInputs G)
    (H : H1.StandingHypotheses G q) (hQ : 2 < (G.homogeneousDimension : ℝ)) :
    ∃ K : H1.FundamentalKernel G H, H1.FundamentalKernelProperties K ∧
      H1.FundamentalKernelProperties (K.reflection hQ) := by
  obtain ⟨K⟩ := U.existence H hQ
  exact ⟨K, H1.assemble_kernel_of_uniqueness K hQ (U.uniqueness H K) (U.uniqueness_atInfinity H K),
    H1.assemble_kernel_of_uniqueness (K.reflection hQ) hQ
      (U.uniqueness _ _) (U.uniqueness_atInfinity _ _)⟩

end RothschildStein.Provider
