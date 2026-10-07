-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.ParametrixStatements
public import RothschildStein.P1.KernelListSums

/-!
# Parametrix error types: closure of the pole-tracked type classes

`IsTypeKernelOn F star lam` (a type-`lam` kernel *modeled on* a pole, `ParametrixStatements`) is closed
under `0`, sums, real multiples, negation, finite sums, lowering the type, equality off the diagonal, and
contains every kernel regular at every budget (a decomposition with an empty principal list). These are
the pole-tracked versions of the closure lemmas of `TypeClosure` and `KernelListSums`; the proofs are the
same constructions with the observation that none of them creates a principal term with a new pole.

`KernelFrame.withPole F star` is the frame with both poles replaced by `F.pole star`. Since the principal
terms of a decomposition only see the frame through `F.G, F.V, F.Θ` and the selected pole, a decomposition
for `F.withPole star` is a decomposition for `F` all of whose principal terms are modeled on `star`
(`IsTypeKernelOn.of_withPole`). This turns every result of the form `IsTypeKernel` proved for an arbitrary
frame (the type calculus of the chart) into a pole-tracked one for the pole `star` of the original frame.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
namespace RothschildStein.P1

variable {N : ℕ} {F : KernelFrame N} {star : Bool} {lam : ℕ}

namespace IsTypeKernelOn

/-- The zero kernel is modeled on every pole at every type. -/
theorem zero : IsTypeKernelOn F star lam (fun _ _ => 0) :=
  fun _ => ⟨TypeDecomposition.zero, by simp [TypeDecomposition.zero]⟩

/-- Kernels of type `lam` modeled on a pole are closed under sums. -/
theorem add {k₁ k₂ : (Fin N → ℝ) → (Fin N → ℝ) → ℝ} (h₁ : IsTypeKernelOn F star lam k₁)
    (h₂ : IsTypeKernelOn F star lam k₂) :
    IsTypeKernelOn F star lam (fun ξ η => k₁ ξ η + k₂ ξ η) := by
  intro m
  obtain ⟨d₁, hd₁⟩ := h₁ m
  obtain ⟨d₂, hd₂⟩ := h₂ m
  refine ⟨d₁.add d₂, ?_⟩
  intro t ht
  rcases List.mem_append.1 ht with h | h
  · exact hd₁ t h
  · exact hd₂ t h

/-- Kernels of type `lam` modeled on a pole are closed under real multiples. -/
theorem smul {k : (Fin N → ℝ) → (Fin N → ℝ) → ℝ} (c : ℝ) (h : IsTypeKernelOn F star lam k) :
    IsTypeKernelOn F star lam (fun ξ η => c * k ξ η) := by
  intro m
  obtain ⟨d, hd⟩ := h m
  refine ⟨d.smul c, ?_⟩
  intro t ht
  obtain ⟨t', ht', rfl⟩ := List.mem_map.1 ht
  exact hd t' ht'

/-- Kernels of type `lam` modeled on a pole are closed under negation. -/
theorem neg {k : (Fin N → ℝ) → (Fin N → ℝ) → ℝ} (h : IsTypeKernelOn F star lam k) :
    IsTypeKernelOn F star lam (fun ξ η => -k ξ η) := by
  simpa using h.smul (-1)

/-- Kernels of type `lam` modeled on a pole are closed under finite sums. -/
theorem sum {ι : Type*} (s : Finset ι) {k : ι → (Fin N → ℝ) → (Fin N → ℝ) → ℝ}
    (h : ∀ i ∈ s, IsTypeKernelOn F star lam (k i)) :
    IsTypeKernelOn F star lam (fun ξ η => ∑ i ∈ s, k i ξ η) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero : IsTypeKernelOn F star lam (fun _ _ => 0))
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- A kernel of type `lam'` modeled on a pole has every lower type `lam ≤ lam'`, still modeled
on that pole. -/
theorem mono {lam' : ℕ} (hl : lam ≤ lam') {k : (Fin N → ℝ) → (Fin N → ℝ) → ℝ}
    (h : IsTypeKernelOn F star lam' k) : IsTypeKernelOn F star lam k := by
  intro m
  obtain ⟨d, hd⟩ := h m
  exact ⟨d.mono hl, hd⟩

/-- A type decomposition modeled on a pole transfers along equality off the diagonal. -/
theorem congr_off_diagonal {r q : (Fin N → ℝ) → (Fin N → ℝ) → ℝ}
    (hr : IsTypeKernelOn F star lam r) (he : ∀ ξ η, ξ ≠ η → r ξ η = q ξ η) :
    IsTypeKernelOn F star lam q := by
  intro budget
  obtain ⟨d, hd⟩ := hr budget
  refine ⟨{ d with eq_off_diagonal := ?_ }, hd⟩
  intro ξ η hne
  rw [← he ξ η hne]
  exact d.eq_off_diagonal ξ η hne

/-- A pointwise equal kernel has the same type, modeled on the same pole. -/
theorem congr_all {r q : (Fin N → ℝ) → (Fin N → ℝ) → ℝ} (hr : IsTypeKernelOn F star lam r)
    (he : ∀ ξ η, r ξ η = q ξ η) : IsTypeKernelOn F star lam q :=
  hr.congr_off_diagonal fun ξ η _ => he ξ η

end IsTypeKernelOn

/-! ### Forcing a pole -/

/-- The frame with both poles replaced by the pole `F.pole star`. -/
def KernelFrame.withPole (F : KernelFrame N) (star : Bool) : KernelFrame N :=
  { F with Γ := F.pole star, Γs := F.pole star }

/-- Both poles of `F.withPole star` are `F.pole star`. -/
theorem KernelFrame.withPole_pole (F : KernelFrame N) (star b : Bool) :
    (F.withPole star).pole b = F.pole star := by
  cases b <;> rfl

/-- A principal term for the one-pole frame is a principal term of `F` modeled on `star`. -/
def PrincipalTerm.ofWithPole {F : KernelFrame N} {star : Bool} (t : PrincipalTerm (F.withPole star)) :
    PrincipalTerm F where
  a := t.a
  b := t.b
  D := t.D
  indices := t.indices
  indices_eq := t.indices_eq
  coefficient_smooth := t.coefficient_smooth
  degree := t.degree
  homogeneous := t.homogeneous
  star := star

/-- The kernel of `PrincipalTerm.ofWithPole` is the kernel of the original term. -/
theorem PrincipalTerm.ofWithPole_kernel {F : KernelFrame N} {star : Bool}
    (t : PrincipalTerm (F.withPole star)) (ξ η : Fin N → ℝ) :
    t.ofWithPole.kernel ξ η = t.kernel ξ η := by
  simp only [PrincipalTerm.kernel, PrincipalTerm.ofWithPole, KernelFrame.withPole_pole]
  rfl

/-- A decomposition for the one-pole frame `F.withPole star` is a decomposition for `F` all of
whose principal terms are modeled on `star`: every type-`lam` kernel for `F.withPole star` is a type-`lam`
kernel for `F` modeled on `star`. -/
theorem IsTypeKernelOn.of_withPole {k : (Fin N → ℝ) → (Fin N → ℝ) → ℝ}
    (h : IsTypeKernel (F.withPole star) lam k) : IsTypeKernelOn F star lam k := by
  intro m
  obtain ⟨d⟩ := h m
  refine ⟨{
    principal := d.principal.map PrincipalTerm.ofWithPole
    principal_degree := ?_
    regular := d.regular
    regular_isRegular := d.regular_isRegular
    eq_off_diagonal := ?_ }, ?_⟩
  · intro t ht
    obtain ⟨t', ht', rfl⟩ := List.mem_map.1 ht
    exact d.principal_degree t' ht'
  · intro ξ η hne
    have e := d.eq_off_diagonal ξ η hne
    rw [e, List.map_map]
    refine congrArg (· + d.regular ξ η) (congrArg List.sum (List.map_congr_left ?_))
    intro t _
    exact (PrincipalTerm.ofWithPole_kernel t ξ η).symm
  · intro t ht
    obtain ⟨t', _, rfl⟩ := List.mem_map.1 ht
    rfl

end RothschildStein.P1
