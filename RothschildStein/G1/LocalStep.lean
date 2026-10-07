-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.G1.BracketAlgebra
public import RothschildStein.Definitions.bracketSpansOn
public import RothschildStein.Definitions.bracketStepOn
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Topology.Instances.Matrix
public import Mathlib.Topology.Separation.Regular
public import Mathlib.Topology.Order.Compact

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set Metric
open scoped Topology

namespace RothschildStein.G1

/-- Coefficient matrix of a selected standard-word frame (BB Def 1.22, p. 12). -/
def wordFrame {m N : ℕ} (X : Fin m → (Fin N → ℝ) → (Fin N → ℝ))
    (I : Fin N → List (Fin m)) (x : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℝ :=
  fun j i => wordBracket X (I i) x j

/-- A frame determinant is nonzero exactly when its columns are independent
(BB Def 1.22, p. 12). -/
theorem wordFrame_det_ne_zero_iff {m N : ℕ}
    (X : Fin m → (Fin N → ℝ) → (Fin N → ℝ)) (I : Fin N → List (Fin m))
    (x : Fin N → ℝ) :
    (wordFrame X I x).det ≠ 0 ↔ LinearIndependent ℝ (fun i => wordBracket X (I i) x) := by
  rw [← isUnit_iff_ne_zero, ← Matrix.isUnit_iff_isUnit_det,
    ← Matrix.linearIndependent_cols_iff_isUnit]
  rfl

/-- Full rank provides a basis consisting of actual standard words, with any
prescribed word restriction retained (BB Def 1.22, p. 12). -/
theorem exists_wordFrame_of_span {m N : ℕ}
    (X : Fin m → (Fin N → ℝ) → (Fin N → ℝ)) (A : Set (List (Fin m)))
    (x : Fin N → ℝ)
    (hspan : Submodule.span ℝ {v | ∃ I ∈ A, v = wordBracket X I x} = ⊤) :
    ∃ I : Fin N → List (Fin m), (∀ i, I i ∈ A) ∧ (wordFrame X I x).det ≠ 0 := by
  classical
  have heq : Module.finrank ℝ (Submodule.span ℝ {v | ∃ I ∈ A, v = wordBracket X I x}) = N := by
    rw [hspan]
    simp
  have h := Submodule.exists_fun_fin_finrank_span_eq ℝ {v | ∃ I ∈ A, v = wordBracket X I x}
  rw [heq] at h
  obtain ⟨v, hv, _, hli⟩ := h
  choose I hI heval using hv
  refine ⟨I, hI, (wordFrame_det_ne_zero_iff X I x).mpr ?_⟩
  have hveq : v = fun i => wordBracket X (I i) x := funext heval
  rwa [← hveq]

/-- Selected frame determinants are continuous on the original open domain
(BB Prop 1.25, p. 13). -/
theorem wordFrame_det_continuousOn {m N : ℕ} {Ω : Set (Fin N → ℝ)} (hΩ : IsOpen Ω)
    (X : Fin m → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω) (I : Fin N → List (Fin m)) :
    ContinuousOn (fun x => (wordFrame X I x).det) Ω := by
  rw [continuousOn_iff_continuous_domRestrict]
  apply Continuous.matrix_det
  apply continuous_pi
  intro j
  apply continuous_pi
  intro i
  exact (continuous_apply j).comp
    ((wordBracket_contDiffOn hΩ X hX (I i)).continuousOn.domRestrict)

/-- Nonvanishing of a chosen frame gives an open patch; the basis may change
from patch to patch (BB Prop 1.25, p. 13). -/
theorem isOpen_wordFrame_patch {m N : ℕ} {Ω : Set (Fin N → ℝ)} (hΩ : IsOpen Ω)
    (X : Fin m → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω) (I : Fin N → List (Fin m)) :
    IsOpen (Ω ∩ {x | (wordFrame X I x).det ≠ 0}) := by
  exact (wordFrame_det_continuousOn hΩ X hX I).isOpen_inter_preimage hΩ
    (isClosed_singleton.isOpen_compl)

/-- A nonzero frame with bounded word weights certifies the fixed weighted
step predicate (BB Def 1.24, p. 13). -/
theorem bracketStepOn_of_wordFrame {m N : ℕ} (w : Fin m → ℕ+)
    (X : Fin m → (Fin N → ℝ) → (Fin N → ℝ)) (s : ℕ)
    (I : Fin N → List (Fin m)) (hI : ∀ i, I i ≠ [] ∧ wordWeight w (I i) ≤ s)
    (x : Fin N → ℝ) (hdet : (wordFrame X I x).det ≠ 0) :
    bracketStepOn {x} w X s := by
  have hli := (wordFrame_det_ne_zero_iff X I x).mp hdet
  have htop := hli.span_eq_top_of_card_eq_finrank' (by simp)
  intro y hy
  have hyx : y = x := Set.mem_singleton_iff.mp hy
  subst y
  apply top_unique
  rw [← htop]
  apply Submodule.span_mono
  rintro v ⟨i, rfl⟩
  exact ⟨I i, (hI i).1, (hI i).2, rfl⟩

/-- Compact sets have a bounded open buffer with one uniform weighted step
on its entire compact closure (BB Prop 1.25, p. 13). -/
theorem exists_uniform_step_buffer {m N : ℕ} {Ω K : Set (Fin N → ℝ)}
    (hΩ : IsOpen Ω) (hK : IsCompact K) (hKΩ : K ⊆ Ω)
    (w : Fin m → ℕ+) (X : Fin m → (Fin N → ℝ) → (Fin N → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) Ω) (hrank : bracketSpansOn Ω X) :
    ∃ V : Set (Fin N → ℝ), IsOpen V ∧ K ⊆ V ∧ closure V ⊆ Ω ∧
      IsCompact (closure V) ∧ Bornology.IsBounded V ∧
      ∃ s : ℕ, 1 ≤ s ∧ bracketStepOn (closure V) w X s := by
  classical
  let A := {I : Fin N → List (Fin m) // ∀ i, I i ≠ []}
  let patch : A → Set (Fin N → ℝ) := fun I => Ω ∩ {x | (wordFrame X I.val x).det ≠ 0}
  have hpatch : ∀ I, IsOpen (patch I) := fun I => isOpen_wordFrame_patch hΩ X hX I.val
  have hcover : K ⊆ ⋃ I, patch I := by
    intro x hx
    obtain ⟨I, hI, hd⟩ := exists_wordFrame_of_span X {I | I ≠ []} x (hrank x (hKΩ hx))
    exact Set.mem_iUnion.mpr ⟨⟨I, hI⟩, hKΩ hx, hd⟩
  obtain ⟨T, hT⟩ := hK.elim_finite_subcover patch hpatch hcover
  let U := ⋃ I ∈ T, patch I
  have hU : IsOpen U := isOpen_biUnion fun I _ => hpatch I
  have hKU : K ⊆ U := hT
  have hUΩ : U ⊆ Ω := by
    intro x hx
    rcases Set.mem_iUnion.mp hx with ⟨I, hx⟩
    rcases Set.mem_iUnion.mp hx with ⟨_, hx⟩
    exact hx.1
  obtain ⟨V, hV, hKV, hVU, hVc⟩ := exists_open_between_and_isCompact_closure hK hU hKU
  let s := T.sup (fun I => Finset.univ.sup (fun i : Fin N => wordWeight w (I.val i))) + 1
  refine ⟨V, hV, hKV, hVU.trans hUΩ, hVc,
    hVc.isBounded.subset subset_closure, s, by omega, ?_⟩
  intro x hx
  obtain ⟨I, hxI⟩ := Set.mem_iUnion.mp (hVU hx)
  obtain ⟨hIT, hxI⟩ := Set.mem_iUnion.mp hxI
  have hweights : ∀ i, I.val i ≠ [] ∧ wordWeight w (I.val i) ≤ s := by
    intro i
    refine ⟨I.property i, ?_⟩
    have h₁ := Finset.le_sup (s := Finset.univ) (f := fun j : Fin N => wordWeight w (I.val j))
      (Finset.mem_univ i)
    have h₂ := Finset.le_sup (s := T)
      (f := fun I => Finset.univ.sup (fun i : Fin N => wordWeight w (I.val i))) hIT
    exact (h₁.trans h₂).trans (Nat.le_succ _)
  exact bracketStepOn_of_wordFrame w X s I.val hweights x hxI.2 x (by simp)

end RothschildStein.G1
