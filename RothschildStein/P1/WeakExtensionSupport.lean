-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.WeakExtensionAct

/-!
# Hölder and noncompact inputs: type operators see their input only on a compact subset of `V`

Every type-`λ` operator `T` of a kernel frame has a compact *input support* `K ⊆ V`: by the type decomposition its kernel
is, off the diagonal, a finite sum of principal terms `a(ξ) b(η) …` with `b ∈ C_c^∞(V)` plus a regular
remainder with compact support in `V × V`, and its multiplier is in `C_c^∞(V)`. Hence

* `TypeOperator.exists_inputSupport`: `k(ξ, η) = 0` for `η ∉ K`, `η ≠ ξ`, and `μ = 0` off `K`;
* `TypeOperator.apply_congr_of_eqOn`: `T f = T g` as soon as `f = g` on `K` (the diagonal is a null set
  in positive dimension), in particular `T f = T g` when `f = g` on `V`.

This is the locality which makes the representation identities insensitive to a cutoff equal to one near
every input support of the finite operator family.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped ENNReal Topology
namespace RothschildStein.P1

namespace TypeOperator

variable {N : ℕ} {F : KernelFrame N} {lam : ℕ}

/-- **The compact input support of a type operator**: there is a
compact `K ⊆ V` with `T.kernel ξ η = 0` for `η ∉ K`, `η ≠ ξ` (the finitely many cutoffs `b` of the
principal terms and the projection of the support of the regular remainder of a decomposition of
budget `0`), and `T.mult = 0` off `K`. -/
theorem exists_inputSupport (T : TypeOperator F lam) :
    ∃ K : Set (Fin N → ℝ), IsCompact K ∧ K ⊆ (F.V : Set (Fin N → ℝ)) ∧
      (∀ ξ η, ξ ≠ η → η ∉ K → T.kernel ξ η = 0) ∧
      ∀ ξ, ξ ∉ K → (T.mult : (Fin N → ℝ) → ℝ) ξ = 0 := by
  classical
  obtain ⟨d⟩ := T.isType 0
  let Kp : Set (Fin N → ℝ) :=
    ⋃ t ∈ d.principal.toFinset, tsupport (t.b : (Fin N → ℝ) → ℝ)
  let Kr : Set (Fin N → ℝ) :=
    Prod.snd '' tsupport (fun z : (Fin N → ℝ) × (Fin N → ℝ) => d.regular z.1 z.2)
  let Km : Set (Fin N → ℝ) := tsupport (T.mult : (Fin N → ℝ) → ℝ)
  have hKp : IsCompact Kp :=
    d.principal.toFinset.isCompact_biUnion fun t _ => t.b.hasCompactSupport
  have hKr : IsCompact Kr := d.regular_isRegular.2.1.image continuous_snd
  have hKm : IsCompact Km := T.mult.hasCompactSupport
  refine ⟨Kp ∪ Kr ∪ Km, (hKp.union hKr).union hKm, ?_, ?_, ?_⟩
  · refine union_subset (union_subset ?_ ?_) T.mult.tsupport_subset
    · refine iUnion₂_subset fun t _ => t.b.tsupport_subset
    · rintro _ ⟨z, hz, rfl⟩
      exact (d.regular_isRegular.2.2 hz).2
  · intro ξ η hξη hη
    rw [d.eq_off_diagonal ξ η hξη]
    have h1 : (d.principal.map fun t => t.kernel ξ η).sum = 0 := by
      refine List.sum_eq_zero fun x hx => ?_
      obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hx
      have hb : (t.b : (Fin N → ℝ) → ℝ) η = 0 := by
        refine image_eq_zero_of_notMem_tsupport fun hmem => hη ?_
        exact Or.inl (Or.inl (mem_biUnion (List.mem_toFinset.2 ht) hmem))
      simp [PrincipalTerm.kernel, hb]
    have h2 : d.regular ξ η = 0 := by
      have : (ξ, η) ∉ tsupport (fun z : (Fin N → ℝ) × (Fin N → ℝ) => d.regular z.1 z.2) :=
        fun hmem => hη (Or.inl (Or.inr ⟨(ξ, η), hmem, rfl⟩))
      exact image_eq_zero_of_notMem_tsupport
        (f := fun z : (Fin N → ℝ) × (Fin N → ℝ) => d.regular z.1 z.2) this
    rw [h1, h2, add_zero]
  · intro ξ hξ
    exact image_eq_zero_of_notMem_tsupport fun hmem => hξ (Or.inr hmem)

/-- **Locality of the action**: if the kernel of `T` vanishes
off the diagonal for inputs outside `K` and the multiplier vanishes off `K`, then `T f = T g` whenever
`f = g` on `K` (in positive dimension, where the diagonal is a null set). -/
theorem apply_congr_of_eqOn [NullSingletonClass (volume : Measure (Fin N → ℝ))] (T : TypeOperator F lam)
    {K : Set (Fin N → ℝ)} (hk : ∀ ξ η, ξ ≠ η → η ∉ K → T.kernel ξ η = 0)
    (hm : ∀ ξ, ξ ∉ K → (T.mult : (Fin N → ℝ) → ℝ) ξ = 0) {f g : (Fin N → ℝ) → ℝ}
    (h : EqOn f g K) : T.apply f = T.apply g := by
  have hae : ∀ ξ, ∀ᵐ η ∂(volume : Measure (Fin N → ℝ)),
      T.kernel ξ η * f η = T.kernel ξ η * g η := fun ξ => by
    filter_upwards [(Set.countable_singleton ξ).ae_notMem (volume : Measure (Fin N → ℝ))] with η hη
    have hne : ξ ≠ η := fun e => hη (by simp [e])
    by_cases hηK : η ∈ K
    · rw [h hηK]
    · rw [hk ξ η hne hηK, zero_mul, zero_mul]
  funext ξ
  have hmul : (T.mult : (Fin N → ℝ) → ℝ) ξ * f ξ = (T.mult : (Fin N → ℝ) → ℝ) ξ * g ξ := by
    by_cases hξ : ξ ∈ K
    · rw [h hξ]
    · rw [hm ξ hξ, zero_mul, zero_mul]
  unfold TypeOperator.apply
  by_cases hlam : lam = 0
  · simp only [hlam, ite_true]
    rw [hmul]
    congr 2
    funext ε
    unfold TypeOperator.truncated
    exact integral_congr_ae (ae_restrict_of_ae (hae ξ))
  · simp only [hlam, ite_false]
    exact integral_congr_ae (hae ξ)

/-- A type operator only sees its input on `V`: `T f = T g` when
`f = g` on `V`. -/
theorem apply_congr_of_eqOn_V [NullSingletonClass (volume : Measure (Fin N → ℝ))] (T : TypeOperator F lam)
    {f g : (Fin N → ℝ) → ℝ} (h : EqOn f g (F.V : Set (Fin N → ℝ))) : T.apply f = T.apply g := by
  obtain ⟨K, -, hKV, hk, hm⟩ := T.exists_inputSupport
  exact T.apply_congr_of_eqOn hk hm (h.mono hKV)

end TypeOperator

namespace LiftedChart

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {F : KernelFrame (n + m)}
  {q : ℕ} {H : H1.StandingHypotheses C.G q} {K : H1.FundamentalKernel C.G H}
  {hQ : 2 < (C.G.homogeneousDimension : ℝ)}

/-- The ambient dimension of a standard frame is positive (`2 < Q`). -/
theorem IsStandardFrame.dim_pos (_hF : C.IsStandardFrame F H K hQ) : 0 < n + m := by
  by_contra h
  have h0 : n + m = 0 := by omega
  have : IsEmpty (Fin (n + m)) := ⟨fun i => absurd i.2 (by omega)⟩
  have hd : C.G.homogeneousDimension = 0 := by
    unfold HomogeneousGroup.homogeneousDimension
    exact Finset.sum_of_isEmpty _
  rw [hd] at hQ
  norm_num at hQ

/-- The Lebesgue measure on the ambient space of a standard frame has no atoms. -/
theorem IsStandardFrame.noAtoms (hF : C.IsStandardFrame F H K hQ) :
    NullSingletonClass (volume : Measure (Fin (n + m) → ℝ)) := by
  have : Nonempty (Fin (n + m)) := ⟨⟨0, hF.dim_pos⟩⟩
  infer_instance

end LiftedChart

end RothschildStein.P1
