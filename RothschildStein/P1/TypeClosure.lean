-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.TypeCalculusStatements

/-!
# Closure of types under sums and higher type

`IsRegularKernel`, `IsTypeKernel` and `TypeOperator` are closed under `0`, `+`, negation, real
multiples and finite sums; a kernel of type `lam'` has every lower type `lam ≤ lam'`, so adding
higher type to a type-`lam` kernel keeps type `lam` (BB p. 543, Def 11.7: finite sums and
adding higher type preserve lower type).

Operators at positive type act by the absolute integral `∫ k(ξ, η) g(η) dη`, so their action is
additive in the operator and linear in the input on bounded compactly supported continuous inputs
(`IsTestInput`, which contains every test function and every word derivative of one) as soon as
the rows of positive-type kernels are integrable (`TypeKernelIntegrable`). At type 0 the action is a
principal value, and linearity is not asserted for arbitrary inputs.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped Topology
namespace RothschildStein.P1

variable {N : ℕ} {F : KernelFrame N}

/-! ### Regular remainders -/

namespace IsRegularKernel

variable {m : ℕ}

/-- The zero kernel is a regular remainder of every budget. -/
theorem zero : IsRegularKernel F m (fun _ _ => 0) := by
  refine ⟨contDiff_const, ?_, ?_⟩
  · exact HasCompactSupport.zero
  · intro z hz
    exfalso
    have : tsupport (fun z : (Fin N → ℝ) × (Fin N → ℝ) => (0 : ℝ)) = ∅ := tsupport_zero
    exact (this ▸ hz : z ∈ (∅ : Set _))

/-- Regular remainders are closed under sums. -/
theorem add {r s : (Fin N → ℝ) → (Fin N → ℝ) → ℝ} (hr : IsRegularKernel F m r)
    (hs : IsRegularKernel F m s) : IsRegularKernel F m (fun ξ η => r ξ η + s ξ η) :=
  ⟨hr.1.add hs.1, hr.2.1.add hs.2.1,
    (tsupport_add _ _).trans (union_subset hr.2.2 hs.2.2)⟩

/-- Regular remainders are closed under real multiples. -/
theorem smul {r : (Fin N → ℝ) → (Fin N → ℝ) → ℝ} (c : ℝ) (hr : IsRegularKernel F m r) :
    IsRegularKernel F m (fun ξ η => c * r ξ η) :=
  ⟨hr.1.const_smul c, hr.2.1.smul_left (f := fun _ => c),
    (tsupport_smul_subset_right (fun _ => c) _).trans hr.2.2⟩

/-- Regular remainders are closed under finite sums. -/
theorem sum {ι : Type*} (s : Finset ι) {r : ι → (Fin N → ℝ) → (Fin N → ℝ) → ℝ}
    (hr : ∀ i ∈ s, IsRegularKernel F m (r i)) :
    IsRegularKernel F m (fun ξ η => ∑ i ∈ s, r i ξ η) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero : IsRegularKernel F m (fun _ _ => 0))
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hr a (Finset.mem_insert_self a s)).add
      (ih fun i hi => hr i (Finset.mem_insert_of_mem hi))

end IsRegularKernel

/-! ### Principal terms and decompositions -/

namespace PrincipalTerm

variable {F : KernelFrame N}

/-- The real multiple of a principal term (scales the output cutoff `a`). -/
def smul (c : ℝ) (t : PrincipalTerm F) : PrincipalTerm F :=
  { t with a := c • t.a }

/-- The kernel of a real multiple of a principal term. -/
theorem kernel_smul (c : ℝ) (t : PrincipalTerm F) (ξ η : Fin N → ℝ) :
    (t.smul c).kernel ξ η = c * t.kernel ξ η := by
  simp only [kernel, smul]
  change c * t.a ξ * _ * _ = _
  ring

end PrincipalTerm

namespace TypeDecomposition

variable {F : KernelFrame N} {lam m : ℕ}

/-- The empty decomposition of the zero kernel. -/
def zero : TypeDecomposition F lam m (fun _ _ => 0) where
  principal := []
  principal_degree := by simp
  regular := fun _ _ => 0
  regular_isRegular := IsRegularKernel.zero
  eq_off_diagonal := by simp

/-- Concatenating the principal terms and adding the remainders decomposes a sum. -/
def add {k₁ k₂ : (Fin N → ℝ) → (Fin N → ℝ) → ℝ} (d₁ : TypeDecomposition F lam m k₁)
    (d₂ : TypeDecomposition F lam m k₂) :
    TypeDecomposition F lam m (fun ξ η => k₁ ξ η + k₂ ξ η) where
  principal := d₁.principal ++ d₂.principal
  principal_degree := by
    intro t ht
    rcases List.mem_append.1 ht with h | h
    · exact d₁.principal_degree t h
    · exact d₂.principal_degree t h
  regular := fun ξ η => d₁.regular ξ η + d₂.regular ξ η
  regular_isRegular := d₁.regular_isRegular.add d₂.regular_isRegular
  eq_off_diagonal := by
    intro ξ η h
    have e₁ := d₁.eq_off_diagonal ξ η h
    have e₂ := d₂.eq_off_diagonal ξ η h
    simp only [List.map_append, List.sum_append]
    linarith

/-- Scaling every principal term and the remainder decomposes a real multiple. -/
def smul (c : ℝ) {k : (Fin N → ℝ) → (Fin N → ℝ) → ℝ} (d : TypeDecomposition F lam m k) :
    TypeDecomposition F lam m (fun ξ η => c * k ξ η) where
  principal := d.principal.map (PrincipalTerm.smul c)
  principal_degree := by
    intro t ht
    obtain ⟨t', ht', rfl⟩ := List.mem_map.1 ht
    exact d.principal_degree t' ht'
  regular := fun ξ η => c * d.regular ξ η
  regular_isRegular := d.regular_isRegular.smul c
  eq_off_diagonal := by
    intro ξ η h
    have e := d.eq_off_diagonal ξ η h
    have hs : ((d.principal.map (PrincipalTerm.smul c)).map fun t => t.kernel ξ η).sum =
        c * (d.principal.map fun t => t.kernel ξ η).sum := by
      rw [List.map_map, ← List.sum_map_mul_left]
      congr 1
      apply List.map_congr_left
      intro t _
      exact PrincipalTerm.kernel_smul c t ξ η
    show c * k ξ η = _
    rw [hs, e]
    ring

/-- Lowering the type only weakens the degree bound of the principal terms. -/
def mono {lam' : ℕ} (h : lam ≤ lam') {k : (Fin N → ℝ) → (Fin N → ℝ) → ℝ}
    (d : TypeDecomposition F lam' m k) : TypeDecomposition F lam m k where
  principal := d.principal
  principal_degree := fun t ht => (d.principal_degree t ht).trans (by omega)
  regular := d.regular
  regular_isRegular := d.regular_isRegular
  eq_off_diagonal := d.eq_off_diagonal

end TypeDecomposition

/-! ### Type kernels -/

namespace IsTypeKernel

variable {F : KernelFrame N} {lam : ℕ}

/-- The zero kernel has every type. -/
theorem zero : IsTypeKernel F lam (fun _ _ => 0) := fun _ => ⟨TypeDecomposition.zero⟩

/-- Type-`lam` kernels are closed under sums. -/
theorem add {k₁ k₂ : (Fin N → ℝ) → (Fin N → ℝ) → ℝ} (h₁ : IsTypeKernel F lam k₁)
    (h₂ : IsTypeKernel F lam k₂) : IsTypeKernel F lam (fun ξ η => k₁ ξ η + k₂ ξ η) :=
  fun m => (h₁ m).elim fun d₁ => (h₂ m).elim fun d₂ => ⟨d₁.add d₂⟩

/-- Type-`lam` kernels are closed under real multiples. -/
theorem smul {k : (Fin N → ℝ) → (Fin N → ℝ) → ℝ} (c : ℝ) (h : IsTypeKernel F lam k) :
    IsTypeKernel F lam (fun ξ η => c * k ξ η) :=
  fun m => (h m).elim fun d => ⟨d.smul c⟩

/-- Type-`lam` kernels are closed under negation. -/
theorem neg {k : (Fin N → ℝ) → (Fin N → ℝ) → ℝ} (h : IsTypeKernel F lam k) :
    IsTypeKernel F lam (fun ξ η => -k ξ η) := by
  simpa using h.smul (-1)

/-- Type-`lam` kernels are closed under finite sums. -/
theorem sum {ι : Type*} (s : Finset ι) {k : ι → (Fin N → ℝ) → (Fin N → ℝ) → ℝ}
    (h : ∀ i ∈ s, IsTypeKernel F lam (k i)) :
    IsTypeKernel F lam (fun ξ η => ∑ i ∈ s, k i ξ η) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero : IsTypeKernel F lam (fun _ _ => 0))
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-- A kernel of type `lam'` has every lower type `lam ≤ lam'`. -/
theorem mono {lam' : ℕ} (hl : lam ≤ lam') {k : (Fin N → ℝ) → (Fin N → ℝ) → ℝ}
    (h : IsTypeKernel F lam' k) : IsTypeKernel F lam k :=
  fun m => (h m).elim fun d => ⟨d.mono hl⟩

end IsTypeKernel

/-! ### Type operators -/

namespace TypeOperator

variable {F : KernelFrame N} {lam : ℕ}

/-- The zero operator of type `lam`. -/
def zero (F : KernelFrame N) (lam : ℕ) : TypeOperator F lam where
  kernel := fun _ _ => 0
  isType := IsTypeKernel.zero
  mult := 0
  mult_eq_zero := fun _ => rfl

/-- The sum of two operators of type `lam` (kernels and multipliers add). -/
def add (T S : TypeOperator F lam) : TypeOperator F lam where
  kernel := fun ξ η => T.kernel ξ η + S.kernel ξ η
  isType := T.isType.add S.isType
  mult := T.mult + S.mult
  mult_eq_zero := fun h => by
    funext x
    have h₁ := congrFun (T.mult_eq_zero h) x
    have h₂ := congrFun (S.mult_eq_zero h) x
    change T.mult x + S.mult x = 0
    rw [h₁, h₂]
    simp

/-- A real multiple of an operator of type `lam`. -/
def smul (c : ℝ) (T : TypeOperator F lam) : TypeOperator F lam where
  kernel := fun ξ η => c * T.kernel ξ η
  isType := T.isType.smul c
  mult := c • T.mult
  mult_eq_zero := fun h => by
    funext x
    have h₁ := congrFun (T.mult_eq_zero h) x
    change c * T.mult x = 0
    rw [h₁]
    simp

/-- The negative of an operator of type `lam`. -/
def neg (T : TypeOperator F lam) : TypeOperator F lam := T.smul (-1)

/-- Transport of a type operator along an equality of types. -/
def ofEq {lam' : ℕ} (h : lam = lam') (T : TypeOperator F lam) : TypeOperator F lam' := by
  subst h
  exact T

/-- A type-`lam'` operator has every lower type `lam ≤ lam'` (same kernel and
multiplier; the multiplier vanishes when `lam' ≠ 0`). -/
def mono {lam' : ℕ} (h : lam ≤ lam') (T : TypeOperator F lam') : TypeOperator F lam where
  kernel := T.kernel
  isType := T.isType.mono h
  mult := T.mult
  mult_eq_zero := fun hl => T.mult_eq_zero (by omega)

/-- The kernel of the zero operator. -/
@[simp] theorem kernel_zero : (zero F lam).kernel = fun _ _ => 0 := rfl

/-- The kernel of a sum of operators. -/
@[simp] theorem kernel_add (T S : TypeOperator F lam) :
    (T.add S).kernel = fun ξ η => T.kernel ξ η + S.kernel ξ η := rfl

/-- The kernel of a real multiple of an operator. -/
@[simp] theorem kernel_smul (c : ℝ) (T : TypeOperator F lam) :
    (T.smul c).kernel = fun ξ η => c * T.kernel ξ η := rfl

/-- The kernel of the negative of an operator. -/
@[simp] theorem kernel_neg (T : TypeOperator F lam) :
    T.neg.kernel = fun ξ η => -1 * T.kernel ξ η := rfl

/-- Lowering the type does not change the kernel. -/
@[simp] theorem kernel_mono {lam' : ℕ} (h : lam ≤ lam') (T : TypeOperator F lam') :
    (T.mono h).kernel = T.kernel := rfl

/-- Transport along an equality of types does not change the action. -/
theorem apply_ofEq {lam' : ℕ} (h : lam = lam') (T : TypeOperator F lam)
    (f : (Fin N → ℝ) → ℝ) (ξ : Fin N → ℝ) : (T.ofEq h).apply f ξ = T.apply f ξ := by
  subst h
  rfl

/-- At positive type the action is the absolute integral. -/
theorem apply_of_ne_zero (T : TypeOperator F lam) (h : lam ≠ 0) (f : (Fin N → ℝ) → ℝ)
    (ξ : Fin N → ℝ) : T.apply f ξ = ∫ η, T.kernel ξ η * f η := by
  simp [apply, h]

/-- Lowering the type of a positive-type operator to another positive type does not change
the action. -/
theorem apply_mono_of_ne_zero {lam' : ℕ} (hl : lam ≤ lam') (T : TypeOperator F lam')
    (h : lam ≠ 0) (f : (Fin N → ℝ) → ℝ) (ξ : Fin N → ℝ) :
    (T.mono hl).apply f ξ = T.apply f ξ := by
  rw [apply_of_ne_zero _ h, apply_of_ne_zero _ (by omega)]
  rfl

end TypeOperator

/-! ### Linearity of the positive-type action -/

/-- Inputs on which positive-type operators act linearly: continuous with compact support
(so bounded). Contains every test function (`isTestInput_testFunction`), every word derivative of
a test function (`isTestInput_wordDerivative`), and is closed under linear combinations. -/
def IsTestInput (g : (Fin N → ℝ) → ℝ) : Prop := Continuous g ∧ HasCompactSupport g

namespace IsTestInput

/-- Test functions are test inputs. -/
theorem of_testFunction (φ : TestFunction F.V ℝ (⊤ : ℕ∞)) :
    IsTestInput (φ : (Fin N → ℝ) → ℝ) :=
  ⟨φ.continuous, φ.hasCompactSupport⟩

/-- The zero function is a test input. -/
theorem zero : IsTestInput (fun _ : Fin N → ℝ => (0 : ℝ)) :=
  ⟨continuous_const, HasCompactSupport.zero⟩

/-- Test inputs are closed under sums. -/
theorem add {g h : (Fin N → ℝ) → ℝ} (hg : IsTestInput g) (hh : IsTestInput h) :
    IsTestInput (fun η => g η + h η) :=
  ⟨hg.1.add hh.1, hg.2.add hh.2⟩

/-- Test inputs are closed under real multiples. -/
theorem smul {g : (Fin N → ℝ) → ℝ} (c : ℝ) (hg : IsTestInput g) :
    IsTestInput (fun η => c * g η) :=
  ⟨continuous_const.mul hg.1, hg.2.smul_left (f := fun _ => c)⟩

/-- Test inputs are closed under finite sums. -/
theorem sum {ι : Type*} (s : Finset ι) {g : ι → (Fin N → ℝ) → ℝ}
    (hg : ∀ i ∈ s, IsTestInput (g i)) : IsTestInput (fun η => ∑ i ∈ s, g i η) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zero : IsTestInput (fun _ : Fin N → ℝ => (0 : ℝ)))
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hg a (Finset.mem_insert_self a s)).add
      (ih fun i hi => hg i (Finset.mem_insert_of_mem hi))

/-- Test inputs are closed under signed list sums. -/
theorem listSum {ι : Type*} (l : List ι) {c : ι → ℝ} {g : ι → (Fin N → ℝ) → ℝ}
    (hg : ∀ a ∈ l, IsTestInput (g a)) :
    IsTestInput (fun η => (l.map fun a => c a * g a η).sum) := by
  induction l with
  | nil => simpa using (zero : IsTestInput (fun _ : Fin N → ℝ => (0 : ℝ)))
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    exact ((hg a List.mem_cons_self).smul (c a)).add
      (ih fun b hb => hg b (List.mem_cons_of_mem a hb))

end IsTestInput

namespace TypeOperator

variable {F : KernelFrame N} {lam : ℕ}

/-- A positive-type kernel against a test input is integrable in the second variable, from
row integrability (`TypeKernelIntegrable`) and boundedness. -/
theorem integrable_kernel_mul (hRowInt : TypeKernelIntegrable F) (hlam : lam ≠ 0) (T : TypeOperator F lam)
    {g : (Fin N → ℝ) → ℝ} (hg : IsTestInput g) (ξ : Fin N → ℝ) :
    Integrable (fun η => T.kernel ξ η * g η) := by
  have hk := (hRowInt lam (Nat.one_le_iff_ne_zero.2 hlam) T.kernel T.isType ξ).1
  obtain ⟨C, hC⟩ := hg.1.bounded_above_of_compact_support hg.2
  exact hk.mul_bdd hg.1.aestronglyMeasurable (Filter.Eventually.of_forall hC)

/-- At positive type, `apply` is additive in the operator. -/
theorem apply_add (hRowInt : TypeKernelIntegrable F) (hlam : lam ≠ 0) (T S : TypeOperator F lam)
    {g : (Fin N → ℝ) → ℝ} (hg : IsTestInput g) (ξ : Fin N → ℝ) :
    (T.add S).apply g ξ = T.apply g ξ + S.apply g ξ := by
  rw [apply_of_ne_zero _ hlam, apply_of_ne_zero _ hlam, apply_of_ne_zero _ hlam]
  simp only [kernel_add, add_mul]
  exact integral_add (integrable_kernel_mul hRowInt hlam T hg ξ) (integrable_kernel_mul hRowInt hlam S hg ξ)

/-- At positive type, `apply` commutes with real multiples of the operator. -/
theorem apply_smul (hlam : lam ≠ 0) (c : ℝ) (T : TypeOperator F lam) (g : (Fin N → ℝ) → ℝ)
    (ξ : Fin N → ℝ) : (T.smul c).apply g ξ = c * T.apply g ξ := by
  rw [apply_of_ne_zero _ hlam, apply_of_ne_zero _ hlam]
  simp only [kernel_smul, mul_assoc]
  exact integral_const_mul c _

/-- At positive type, `apply` of the negative operator. -/
theorem apply_neg (hlam : lam ≠ 0) (T : TypeOperator F lam) (g : (Fin N → ℝ) → ℝ)
    (ξ : Fin N → ℝ) : T.neg.apply g ξ = -T.apply g ξ := by
  rw [neg, apply_smul hlam]
  ring

/-- At positive type, `apply` of the zero operator. -/
theorem apply_zero (hlam : lam ≠ 0) (g : (Fin N → ℝ) → ℝ) (ξ : Fin N → ℝ) :
    (zero F lam).apply g ξ = 0 := by
  rw [apply_of_ne_zero _ hlam]
  simp

/-- At positive type, `apply` is additive in the input. -/
theorem apply_add_input (hRowInt : TypeKernelIntegrable F) (hlam : lam ≠ 0) (T : TypeOperator F lam)
    {g h : (Fin N → ℝ) → ℝ} (hg : IsTestInput g) (hh : IsTestInput h) (ξ : Fin N → ℝ) :
    T.apply (fun η => g η + h η) ξ = T.apply g ξ + T.apply h ξ := by
  rw [apply_of_ne_zero _ hlam, apply_of_ne_zero _ hlam, apply_of_ne_zero _ hlam]
  simp only [mul_add]
  exact integral_add (integrable_kernel_mul hRowInt hlam T hg ξ) (integrable_kernel_mul hRowInt hlam T hh ξ)

/-- At positive type, `apply` commutes with real multiples of the input. -/
theorem apply_smul_input (hlam : lam ≠ 0) (T : TypeOperator F lam) (c : ℝ)
    (g : (Fin N → ℝ) → ℝ) (ξ : Fin N → ℝ) :
    T.apply (fun η => c * g η) ξ = c * T.apply g ξ := by
  rw [apply_of_ne_zero _ hlam, apply_of_ne_zero _ hlam]
  rw [← integral_const_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall fun η => by ring)

/-- At positive type, `apply` of the zero input. -/
theorem apply_zero_input (hlam : lam ≠ 0) (T : TypeOperator F lam) (ξ : Fin N → ℝ) :
    T.apply (fun _ => (0 : ℝ)) ξ = 0 := by
  rw [apply_of_ne_zero _ hlam]
  simp

/-- At positive type, `apply` is additive over finite sums of inputs. -/
theorem apply_sum_input (hRowInt : TypeKernelIntegrable F) (hlam : lam ≠ 0) (T : TypeOperator F lam)
    {ι : Type*} (s : Finset ι) {g : ι → (Fin N → ℝ) → ℝ} (hg : ∀ i ∈ s, IsTestInput (g i))
    (ξ : Fin N → ℝ) :
    T.apply (fun η => ∑ i ∈ s, g i η) ξ = ∑ i ∈ s, T.apply (g i) ξ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using apply_zero_input hlam T ξ
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    rw [apply_add_input hRowInt hlam T (hg a (Finset.mem_insert_self a s))
      (IsTestInput.sum s fun i hi => hg i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => hg i (Finset.mem_insert_of_mem hi)]

/-- At positive type, `apply` of a signed list sum of test inputs (the shape of a bracket
expansion `∑ ± X_σ f`, where duplicated terms are kept). -/
theorem apply_listSum_input (hRowInt : TypeKernelIntegrable F) (hlam : lam ≠ 0) (T : TypeOperator F lam)
    {ι : Type*} (l : List ι) (c : ι → ℝ) {g : ι → (Fin N → ℝ) → ℝ}
    (hg : ∀ a ∈ l, IsTestInput (g a)) (ξ : Fin N → ℝ) :
    T.apply (fun η => (l.map fun a => c a * g a η).sum) ξ =
      (l.map fun a => c a * T.apply (g a) ξ).sum := by
  induction l with
  | nil => simpa using apply_zero_input hlam T ξ
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons]
    have hl : ∀ b ∈ l, IsTestInput (g b) := fun b hb => hg b (List.mem_cons_of_mem a hb)
    rw [apply_add_input hRowInt hlam T ((hg a List.mem_cons_self).smul (c a))
      (IsTestInput.listSum l hl), apply_smul_input hlam T (c a) (g a), ih hl]

end TypeOperator

end RothschildStein.P1
