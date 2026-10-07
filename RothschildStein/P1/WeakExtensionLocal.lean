-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.WeakExtensionJet
public import RothschildStein.P1.WeakExtensionParametrix

/-!
# Hölder and noncompact inputs: locality and cutoffs

Smooth noncompact inputs can be cut off to a compact subset of `V` without changing any identity of the
finite operator family (cut off equal to one near every input support of the finite family). This file collects the tools:

* locality of classical word derivatives, `L̃ = ∑ᵢ X̃ᵢ²` and the lifted `L̃ = X̃₀ + ∑ᵢ X̃ᵢ²`
  (`wordDerivative_eqOn`, `sumSquares_eqOn`, `sumSquaresWithDrift_eqOn`): derivatives of functions that
  agree on an open set agree there, in particular the derivatives of a cutoff equal to one vanish near
  its plateau;
* `exists_test_eq_on_nhds`: for `u` smooth on `V` and a compact `K₀ ⊆ V` there is a test function `v`
  equal to `u` on an open neighbourhood of `K₀`;
* `TypeOperator.SeesOnly`: the compact input supports of `WeakExtensionSupport` for finite families, and
  the invariance of `T f` and of the coefficients `MultEndpoint` under changing `f` off the support.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped ENNReal Topology
namespace RothschildStein.P1

section Locality

variable {N k : ℕ} (Xt : Fin k → (Fin N → ℝ) → (Fin N → ℝ))

/-- Classical word derivatives are local: equality near a point
persists after every ordered field derivative. -/
theorem wordDerivative_eventuallyEq_of_eventuallyEq (J : List (Fin k)) {f g : (Fin N → ℝ) → ℝ}
    {x : Fin N → ℝ} (h : f =ᶠ[𝓝 x] g) :
    wordDerivative Xt J f =ᶠ[𝓝 x] wordDerivative Xt J g := by
  induction J with
  | nil => exact h
  | cons i J ih =>
    have hd := ih.fderiv (𝕜 := ℝ)
    filter_upwards [hd] with z hz
    exact congrArg (fun L : (Fin N → ℝ) →L[ℝ] ℝ => L (Xt i z)) hz

/-- The word derivatives of functions which agree on an open set
agree there. -/
theorem wordDerivative_eqOn (J : List (Fin k)) {f g : (Fin N → ℝ) → ℝ} {W : Set (Fin N → ℝ)}
    (hW : IsOpen W) (h : EqOn f g W) : EqOn (wordDerivative Xt J f) (wordDerivative Xt J g) W :=
  fun _ hx => (wordDerivative_eventuallyEq_of_eventuallyEq Xt J
    (Filter.eventuallyEq_of_mem (hW.mem_nhds hx) h)).eq_of_nhds

/-- `L̃ = ∑ᵢ X̃ᵢ²` is local. -/
theorem sumSquares_eqOn {f g : (Fin N → ℝ) → ℝ} {W : Set (Fin N → ℝ)} (hW : IsOpen W)
    (h : EqOn f g W) : EqOn (sumSquares Xt f) (sumSquares Xt g) W := fun x hx => by
  have hi := fun i : Fin k => wordDerivative_eqOn Xt [i, i] hW h hx
  exact Finset.sum_congr rfl fun i _ => hi i

end Locality

section LocalityDrift

variable {N q : ℕ} (Xt : Fin (q + 1) → (Fin N → ℝ) → (Fin N → ℝ))

/-- `L̃ = X̃₀ + ∑ᵢ X̃ᵢ²` is local. -/
theorem sumSquaresWithDrift_eqOn {f g : (Fin N → ℝ) → ℝ} {W : Set (Fin N → ℝ)} (hW : IsOpen W)
    (h : EqOn f g W) : EqOn (sumSquaresWithDrift Xt f) (sumSquaresWithDrift Xt g) W :=
  fun x hx => by
    have h0 := wordDerivative_eqOn Xt [0] hW h hx
    have hi := fun i : Fin q => wordDerivative_eqOn Xt [i.succ, i.succ] hW h hx
    change fieldDerivative (Xt 0) f x +
        ∑ i : Fin q, fieldDerivative (Xt i.succ) (fieldDerivative (Xt i.succ) f) x =
      fieldDerivative (Xt 0) g x +
        ∑ i : Fin q, fieldDerivative (Xt i.succ) (fieldDerivative (Xt i.succ) g) x
    exact congrArg₂ (· + ·) h0 (Finset.sum_congr rfl fun i _ => hi i)

end LocalityDrift

section Cutoff

variable {N : ℕ}

/-- **Cutoff equal to one near a compact set.** If `u` is smooth on
`V` and `K₀ ⊆ V` is compact, there is a test function `v ∈ C_c^∞(V)` which equals `u` on an open
neighbourhood `W` of `K₀` (`v = χ u` with `χ ∈ C_c^∞(V)`, `χ = 1` on `W`). -/
theorem exists_test_eq_on_nhds (V : Opens (Fin N → ℝ)) {K₀ : Set (Fin N → ℝ)} (hK : IsCompact K₀)
    (hKV : K₀ ⊆ V) {u : (Fin N → ℝ) → ℝ} (hu : ContDiffOn ℝ (⊤ : ℕ∞) u (V : Set (Fin N → ℝ))) :
    ∃ (v : TestFunction V ℝ (⊤ : ℕ∞)) (W : Set (Fin N → ℝ)),
      IsOpen W ∧ K₀ ⊆ W ∧ W ⊆ V ∧ ∀ x ∈ W, v x = u x := by
  obtain ⟨W₁, hW₁, hKW₁, hcl₁, hc₁⟩ := exists_open_between_and_isCompact_closure hK V.isOpen hKV
  obtain ⟨W₂, hW₂, hcl₂₁, hcl₂, hc₂⟩ :=
    exists_open_between_and_isCompact_closure hc₁ V.isOpen hcl₁
  obtain ⟨χ, hχ, -, hs, hone⟩ := exists_contDiff_support_eq_eq_one_iff (n := (⊤ : ℕ∞)) hW₂
    (isClosed_closure (s := W₁)) hcl₂₁
  have ht : tsupport χ = closure W₂ := by rw [tsupport, hs]
  have hχc : HasCompactSupport χ := by
    rw [HasCompactSupport, ht]
    exact hc₂
  have hχV : tsupport χ ⊆ V := by
    rw [ht]
    exact hcl₂
  refine ⟨⟨fun x => χ x * u x, ?_, hχc.mul_right, tsupport_mul_subset_left.trans hχV⟩, W₁, hW₁,
    hKW₁, subset_closure.trans hcl₁, fun x hx => ?_⟩
  · refine contDiff_iff_contDiffAt.mpr fun x => ?_
    by_cases hx : x ∈ (V : Set (Fin N → ℝ))
    · exact hχ.contDiffAt.mul (hu.contDiffAt (V.isOpen.mem_nhds hx))
    · have hxs : x ∉ tsupport χ := fun h => hx (hχV h)
      have he : ∀ᶠ y in 𝓝 x, y ∉ tsupport χ := (isClosed_tsupport χ).isOpen_compl.mem_nhds hxs
      exact (contDiffAt_const : ContDiffAt ℝ (⊤ : ℕ∞) (fun _ : Fin N → ℝ => (0 : ℝ)) x).congr_of_eventuallyEq
        (he.mono fun y hy => by simp [image_eq_zero_of_notMem_tsupport hy])
  · show χ x * u x = u x
    rw [(hone x).1 (subset_closure hx), one_mul]

end Cutoff

section SeesOnly

variable {N : ℕ} {F : KernelFrame N} {lam : ℕ}

/-- A type operator **sees only `K`** when its kernel vanishes off the
diagonal for inputs outside `K` and its multiplier vanishes off `K` (the compact input support of
`TypeOperator.exists_inputSupport`). -/
def TypeOperator.SeesOnly (T : TypeOperator F lam) (K : Set (Fin N → ℝ)) : Prop :=
  (∀ ξ η, ξ ≠ η → η ∉ K → T.kernel ξ η = 0) ∧
    ∀ ξ, ξ ∉ K → (T.mult : (Fin N → ℝ) → ℝ) ξ = 0

theorem TypeOperator.SeesOnly.mono {T : TypeOperator F lam} {K K' : Set (Fin N → ℝ)}
    (h : T.SeesOnly K) (hK : K ⊆ K') : T.SeesOnly K' :=
  ⟨fun ξ η hne hη => h.1 ξ η hne fun hm => hη (hK hm),
    fun ξ hξ => h.2 ξ fun hm => hξ (hK hm)⟩

/-- Every type operator sees only a compact subset of `V`. -/
theorem TypeOperator.exists_seesOnly (T : TypeOperator F lam) :
    ∃ K : Set (Fin N → ℝ), IsCompact K ∧ K ⊆ (F.V : Set (Fin N → ℝ)) ∧ T.SeesOnly K := by
  obtain ⟨K, hK, hKV, hk, hm⟩ := T.exists_inputSupport
  exact ⟨K, hK, hKV, hk, hm⟩

/-- A finite family of type operators sees only one compact
subset of `V`. -/
theorem TypeOperator.exists_seesOnly_finset {ι : Type*} (s : Finset ι) (T : ι → TypeOperator F lam) :
    ∃ K : Set (Fin N → ℝ), IsCompact K ∧ K ⊆ (F.V : Set (Fin N → ℝ)) ∧
      ∀ i ∈ s, (T i).SeesOnly K := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨∅, isCompact_empty, empty_subset _, by simp⟩
  | insert a s ha ih =>
    obtain ⟨K, hK, hKV, h⟩ := ih
    obtain ⟨K', hK', hK'V, h'⟩ := (T a).exists_seesOnly
    refine ⟨K ∪ K', hK.union hK', union_subset hKV hK'V, fun i hi => ?_⟩
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact h'.mono subset_union_right
    · exact (h i hi).mono subset_union_left

/-- **Locality of the action**: if `T` sees only `K` then `T f = T g`
whenever `f = g` on `K` (positive dimension). -/
theorem TypeOperator.SeesOnly.apply_congr [NullSingletonClass (volume : Measure (Fin N → ℝ))]
    {T : TypeOperator F lam} {K : Set (Fin N → ℝ)} (h : T.SeesOnly K)
    {f g : (Fin N → ℝ) → ℝ} (hfg : EqOn f g K) : T.apply f = T.apply g :=
  T.apply_congr_of_eqOn h.1 h.2 hfg

variable {k : ℕ} {Xt : Fin k → (Fin N → ℝ) → (Fin N → ℝ)}

end SeesOnly

end RothschildStein.P1
