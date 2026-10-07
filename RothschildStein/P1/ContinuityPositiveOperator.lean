-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.ContinuityPositiveShell

/-!
# Positive-type continuity: the integral operator of a patch kernel

A *patch kernel* is a kernel `κ` supported (off the diagonal) in `V × V`, on a patch `V ⊆ S` with `S`
compact in the chart domain `U`, with the kernel bounds of exponent one on `S` and a measurable cut
to `S × S`. The positive-type operator `T f(ξ) = ∫ κ(ξ, η) f(η) dη` then satisfies, with constants
depending only on the kernel data:

* `PatchKernel.exists_lp_bound`: `‖T f‖_{L^p(V)} ≤ Λ ‖f‖_{L^p(V)}` for every `1 ≤ p < ∞` (Schur
  bound; the output is in `L^p`, and the integral converges absolutely almost everywhere);
* `PatchKernel.exists_sup_bound` and `PatchKernel.exists_holder_bound`: `L^∞ → C^α` for `0 < α < 1`
  in `holderENorm` with the lifted control distance `d̃`
  (`PatchKernel.exists_holderENorm_bound`), and `‖T f‖_{C^α(V)} ≤ C ‖f‖_{C^α(V)}`
  (`PatchKernel.exists_holderENorm_bound_of_holderENorm`).

Closure under sums and under changes at the diagonal is also proved, so that a type decomposition
(finitely many principal terms plus a regular remainder) can be assembled.
(BB pp. 566–576, Thm. 11.29; BB p. 544, Prop. 11.10.)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace RothschildStein.P1
namespace LiftedChart

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  (C : LiftedChart w s Ω hΩ X x₀ m)

/-- A **patch kernel**: on a compact patch `S ⊆ U` with a measurable `V ⊆ S`, the kernel
`κ` has the kernel bounds of exponent one, a measurable cut to `S × S`, and vanishes off the
diagonal outside `V × V` (the cutoffs of the type calculus are supported in `V`). -/
structure PatchKernel (S V : Set (Fin (n + m) → ℝ))
    (κ : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ) : Prop where
  isCompact : IsCompact S
  subset_U : S ⊆ C.U
  subset : V ⊆ S
  measurableSet : MeasurableSet V
  bounds : C.HasKernelBounds S 1 κ
  measurable : Measurable (Function.uncurry (sliceKernel S κ))
  support : ∀ ξ η, ξ ≠ η → (ξ ∉ V ∨ η ∉ V) → κ ξ η = 0

variable {C} {S V : Set (Fin (n + m) → ℝ)}
  {κ κ' : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ}

/-- The zero kernel is a patch kernel. -/
theorem PatchKernel.zero (hS : IsCompact S) (hSU : S ⊆ C.U) (hVS : V ⊆ S)
    (hV : MeasurableSet V) : C.PatchKernel S V (fun _ _ => 0) :=
  ⟨hS, hSU, hVS, hV, HasKernelBounds.zero, by
    have : Function.uncurry (sliceKernel S (fun _ _ => (0 : ℝ))) = fun _ => 0 := by
      funext z
      show sliceKernel S (fun _ _ => (0 : ℝ)) z.1 z.2 = 0
      unfold sliceKernel
      simp [Set.indicator]
    rw [this]
    exact measurable_const, fun _ _ _ _ => rfl⟩

/-- Patch kernels are stable under sums. -/
theorem PatchKernel.add (h₁ : C.PatchKernel S V κ) (h₂ : C.PatchKernel S V κ') :
    C.PatchKernel S V (fun ξ η => κ ξ η + κ' ξ η) := by
  refine ⟨h₁.isCompact, h₁.subset_U, h₁.subset, h₁.measurableSet, h₁.bounds.add h₂.bounds, ?_,
    fun ξ η hne hout => ?_⟩
  · have : Function.uncurry (sliceKernel S (fun ξ η => κ ξ η + κ' ξ η)) =
        Function.uncurry (sliceKernel S κ) + Function.uncurry (sliceKernel S κ') := by
      funext ⟨a, b⟩
      show sliceKernel S (fun ξ η => κ ξ η + κ' ξ η) a b = sliceKernel S κ a b + sliceKernel S κ' a b
      unfold sliceKernel
      exact congrFun (Set.indicator_add ((S ×ˢ S) \ Set.diagonal (Fin (n + m) → ℝ))
        (fun z : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => κ z.1 z.2)
        (fun z : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => κ' z.1 z.2)) (a, b)
    rw [this]
    exact h₁.measurable.add h₂.measurable
  · show κ ξ η + κ' ξ η = 0
    rw [h₁.support ξ η hne hout, h₂.support ξ η hne hout, add_zero]

/-- A finite list of patch kernels sums to a patch kernel. -/
theorem PatchKernel.list_sum {ι : Type*} (hS : IsCompact S) (hSU : S ⊆ C.U) (hVS : V ⊆ S)
    (hV : MeasurableSet V) (l : List ι) {κι : ι → (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ}
    (h : ∀ i ∈ l, C.PatchKernel S V (κι i)) :
    C.PatchKernel S V (fun ξ η => (l.map (fun i => κι i ξ η)).sum) := by
  induction l with
  | nil => simpa using PatchKernel.zero hS hSU hVS hV
  | cons a l ih =>
    have h1 := h a (List.mem_cons_self ..)
    have h2 := ih (fun i hi => h i (List.mem_cons_of_mem _ hi))
    simpa only [List.map_cons, List.sum_cons] using h1.add h2

/-- A patch kernel stays a patch kernel when changed on the diagonal. -/
theorem PatchKernel.congr_off_diagonal (h : C.PatchKernel S V κ)
    (he : ∀ ξ η, ξ ≠ η → κ ξ η = κ' ξ η) : C.PatchKernel S V κ' := by
  refine ⟨h.isCompact, h.subset_U, h.subset, h.measurableSet,
    h.bounds.congr_off_diagonal h.subset_U he, ?_, fun ξ η hne hout => ?_⟩
  · have : Function.uncurry (sliceKernel S κ') = Function.uncurry (sliceKernel S κ) := by
      funext ⟨a, b⟩
      show sliceKernel S κ' a b = sliceKernel S κ a b
      by_cases hab : a ∈ S ∧ b ∈ S ∧ a ≠ b
      · rw [sliceKernel_of_mem hab.1 hab.2.1 hab.2.2, sliceKernel_of_mem hab.1 hab.2.1 hab.2.2,
          he a b hab.2.2]
      · have hn : a ∉ S ∨ b ∉ S ∨ a = b := by
          by_contra hcon
          exact hab ⟨by_contra fun h => hcon (Or.inl h),
            by_contra fun h => hcon (Or.inr (Or.inl h)), fun h => hcon (Or.inr (Or.inr h))⟩
        rw [sliceKernel_of_not_mem hn, sliceKernel_of_not_mem hn]
    rw [this]
    exact h.measurable
  · rw [← he ξ η hne]
    exact h.support ξ η hne hout

/-- The diagonal point `ξ` is null: almost every `η` differs from `ξ`. -/
theorem ae_ne (C : LiftedChart w s Ω hΩ X x₀ m) (ξ : Fin (n + m) → ℝ) :
    ∀ᵐ η ∂(volume : Measure (Fin (n + m) → ℝ)), η ≠ ξ := by
  have : Nonempty (Fin (n + m)) := ⟨⟨0, C.G.dimension_pos⟩⟩
  have := measure_eq_zero_iff_ae_notMem.mp (measure_singleton (μ := volume) ξ)
  filter_upwards [this] with η hη
  simpa using hη

/-- For a patch kernel the row `η ↦ κ(ξ, η) f(η)` is almost everywhere the integrand of the
cut kernel over the compact patch `S` against `1_V f` (the diagonal is null and the kernel vanishes
off `V × V`). -/
theorem PatchKernel.ae_eq (h : C.PatchKernel S V κ) (f : (Fin (n + m) → ℝ) → ℝ)
    (ξ : Fin (n + m) → ℝ) :
    (fun η => κ ξ η * f η) =ᵐ[volume]
      S.indicator (fun η => sliceKernel S κ ξ η * V.indicator f η) := by
  filter_upwards [C.ae_ne ξ] with η hηξ
  show κ ξ η * f η = S.indicator (fun η => sliceKernel S κ ξ η * V.indicator f η) η
  by_cases hηV : η ∈ V
  · have hηS := h.subset hηV
    simp only [Set.indicator_of_mem hηS, Set.indicator_of_mem hηV]
    by_cases hξS : ξ ∈ S
    · rw [sliceKernel_of_mem hξS hηS hηξ.symm]
    · have hξV : ξ ∉ V := fun hv => hξS (h.subset hv)
      simp [h.support ξ η hηξ.symm (Or.inl hξV), sliceKernel_of_not_mem (Or.inl hξS)]
  · rw [h.support ξ η hηξ.symm (Or.inr hηV)]
    by_cases hηS : η ∈ S
    · simp [Set.indicator_of_mem hηS, Set.indicator_of_notMem hηV]
    · simp [Set.indicator_of_notMem hηS]

/-- The integral operator of a patch kernel is the integral over the compact patch `S` of the
cut kernel against `1_V f`. -/
theorem PatchKernel.integral_eq (h : C.PatchKernel S V κ) (f : (Fin (n + m) → ℝ) → ℝ)
    (ξ : Fin (n + m) → ℝ) :
    ∫ η, κ ξ η * f η =
      ∫ η, sliceKernel S κ ξ η * V.indicator f η ∂(volume.restrict S) := by
  rw [← integral_indicator h.isCompact.measurableSet]
  exact integral_congr_ae (h.ae_eq f ξ)

/-- The operator of a patch kernel vanishes outside the patch `V`. -/
theorem PatchKernel.integral_eq_zero_of_not_mem (h : C.PatchKernel S V κ)
    (f : (Fin (n + m) → ℝ) → ℝ) {ξ : Fin (n + m) → ℝ} (hξ : ξ ∉ V) : ∫ η, κ ξ η * f η = 0 := by
  rw [← integral_zero (Fin (n + m) → ℝ) ℝ (μ := volume)]
  refine integral_congr_ae ?_
  filter_upwards [C.ae_ne ξ] with η hηξ
  show κ ξ η * f η = 0
  rw [h.support ξ η hηξ.symm (Or.inl hξ), zero_mul]

section Bounds

variable (h : C.PatchKernel S V κ)
include h

/-- **The `L^∞` bound** (BB p. 544, Prop 11.10): `|T f| ≤ Cs sup_V |f|`
everywhere, with `Cs` depending only on the kernel data. -/
theorem PatchKernel.exists_sup_bound :
    ∃ Cs : ℝ, 0 < Cs ∧ ∀ (f : (Fin (n + m) → ℝ) → ℝ) (M : ℝ), 0 ≤ M → (∀ y ∈ V, |f y| ≤ M) →
      ∀ x, |∫ η, κ x η * f η| ≤ Cs * M := by
  obtain ⟨ρ, Cv, hS⟩ := C.exists_shellData_patch h.isCompact h.subset_U
  obtain ⟨A, B, hK⟩ := C.exists_sliceBounds_of_hasKernelBounds h.subset_U h.bounds h.measurable
  have hA := hK.A_nonneg
  have hC := hS.Cv_nonneg
  have hρ := hS.ρ_pos
  have hpos : 0 < A * (Cv * 2 ^ (C.G.homogeneousDimension - 1 + 1)) * (2 * ρ) + 1 := by positivity
  refine ⟨A * (Cv * 2 ^ (C.G.homogeneousDimension - 1 + 1)) * (2 * ρ) + 1, hpos,
    fun f M hM0 hM x => ?_⟩
  rw [h.integral_eq f x]
  by_cases hx : x ∈ S
  · have hM' : ∀ y ∈ S, |V.indicator f y| ≤ M := by
      intro y _
      by_cases hy : y ∈ V
      · rw [Set.indicator_of_mem hy]
        exact hM y hy
      · rw [Set.indicator_of_notMem hy, abs_zero]
        exact hM0
    refine (hK.abs_integral_le hS hM0 hM' hx).trans ?_
    have e : A * M * (Cv * 2 ^ (C.G.homogeneousDimension - 1 + 1)) * (2 * ρ) =
        (A * (Cv * 2 ^ (C.G.homogeneousDimension - 1 + 1)) * (2 * ρ)) * M := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) hM0
  · have : (fun y => sliceKernel S κ x y * V.indicator f y) = fun _ => 0 := by
      funext y
      rw [sliceKernel_of_not_mem (Or.inl hx), zero_mul]
    rw [this]
    simp only [integral_zero, abs_zero]
    positivity

/-- **Absolute convergence**: for `f` measurable and bounded on `V`, every row
`η ↦ κ(ξ, η) f(η)` is Lebesgue integrable, so the Bochner integral of the operator is the absolutely
convergent integral that represents a positive-type operator. -/
theorem PatchKernel.integrable_row {f : (Fin (n + m) → ℝ) → ℝ}
    (hf : AEStronglyMeasurable f (volume.restrict V)) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ y ∈ V, |f y| ≤ M) (ξ : Fin (n + m) → ℝ) :
    Integrable (fun η => κ ξ η * f η) := by
  obtain ⟨ρ, Cv, hS⟩ := C.exists_shellData_patch h.isCompact h.subset_U
  obtain ⟨A, B, hK⟩ := C.exists_sliceBounds_of_hasKernelBounds h.subset_U h.bounds h.measurable
  refine Integrable.congr ?_ (h.ae_eq f ξ).symm
  rw [integrable_indicator_iff h.isCompact.measurableSet]
  by_cases hξ : ξ ∈ S
  · have hg : AEStronglyMeasurable (V.indicator f) (volume.restrict S) := by
      refine (aestronglyMeasurable_indicator_iff h.measurableSet).mpr ?_
      rw [Measure.restrict_restrict h.measurableSet, inter_eq_left.mpr h.subset]
      exact hf
    have hM' : ∀ z ∈ S, |V.indicator f z| ≤ M := by
      intro z _
      by_cases hz : z ∈ V
      · rw [Set.indicator_of_mem hz]
        exact hM z hz
      · rw [Set.indicator_of_notMem hz, abs_zero]
        exact hM0
    exact hK.integrable_row hS hg hM0 hM' hξ
  · have : (fun y => sliceKernel S κ ξ y * V.indicator f y) = fun _ => 0 := by
      funext y
      rw [sliceKernel_of_not_mem (Or.inl hξ), zero_mul]
    rw [this]
    exact integrable_zero _ _ _

/-- **The `L^∞ → C^α` bound** (BB pp. 305–309, Thm 7.14 with `β = 1`, `ν = ℓ ≥ 1`; here
by the direct dyadic argument from the kernel difference bound): for `0 < α < 1` and `f` measurable
with `|f| ≤ M` on `V`, `|T f(x) - T f(y)| ≤ Ch M d̃(x, y)^α` for `x, y ∈ S`. -/
theorem PatchKernel.exists_holder_bound {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ Ch : ℝ, 0 < Ch ∧ ∀ (f : (Fin (n + m) → ℝ) → ℝ),
      AEStronglyMeasurable f (volume.restrict V) → ∀ M : ℝ, 0 ≤ M → (∀ y ∈ V, |f y| ≤ M) →
        ∀ x ∈ S, ∀ y ∈ S,
          |(∫ η, κ x η * f η) - ∫ η, κ y η * f η| ≤ Ch * M * (C.dl x y).toReal ^ α := by
  obtain ⟨ρ, Cv, hS⟩ := C.exists_shellData_patch h.isCompact h.subset_U
  obtain ⟨A, B, hK⟩ := C.exists_sliceBounds_of_hasKernelBounds h.subset_U h.bounds h.measurable
  have hA := hK.A_nonneg
  have hB := hK.B_nonneg
  have hC := hS.Cv_nonneg
  have hρ := hS.ρ_pos
  have hα' : 0 < 1 - α := by linarith
  have hCα : 0 ≤ holderConst A B Cv (C.G.homogeneousDimension - 1) α := by
    unfold holderConst
    positivity
  have hρα : 0 < ρ ^ (1 - α) := Real.rpow_pos_of_pos hρ _
  refine ⟨holderConst A B Cv (C.G.homogeneousDimension - 1) α * ρ ^ (1 - α) + 1, by positivity,
    fun f hf M hM0 hM x hx y hy => ?_⟩
  rw [h.integral_eq f x, h.integral_eq f y]
  have hg : AEStronglyMeasurable (V.indicator f) (volume.restrict S) := by
    refine (aestronglyMeasurable_indicator_iff h.measurableSet).mpr ?_
    rw [Measure.restrict_restrict h.measurableSet, inter_eq_left.mpr h.subset]
    exact hf
  have hM' : ∀ z ∈ S, |V.indicator f z| ≤ M := by
    intro z _
    by_cases hz : z ∈ V
    · rw [Set.indicator_of_mem hz]
      exact hM z hz
    · rw [Set.indicator_of_notMem hz, abs_zero]
      exact hM0
  have this' : |(∫ η in S, sliceKernel S κ x η * V.indicator f η) -
      ∫ η in S, sliceKernel S κ y η * V.indicator f η| ≤
      holderConst A B Cv (C.G.homogeneousDimension - 1) α * ρ ^ (1 - α) * M *
        (C.dl x y).toReal ^ α := hK.abs_sub_le_holder hS hg hM0 hM' hα0 hα1 hx hy
  refine this'.trans ?_
  have hd : 0 ≤ (C.dl x y).toReal ^ α := Real.rpow_nonneg ENNReal.toReal_nonneg _
  have h1 : 0 ≤ M * (C.dl x y).toReal ^ α := mul_nonneg hM0 hd
  nlinarith [h1]

end Bounds

/-- **The `L^p` bound** (BB p. 544, Prop 11.10; Schur): for every `1 ≤ p < ∞` and
`f ∈ L^p(V)` the operator `T f(ξ) = ∫ κ(ξ, η) f(η) dη` is in `L^p(V)` with
`‖T f‖_p ≤ Λ ‖f‖_p`, and `Λ` is independent of `p` and `f`. -/
theorem PatchKernel.exists_lp_bound (h : C.PatchKernel S V κ) :
    ∃ Λ : ℝ, 0 < Λ ∧ ∀ p : ℝ≥0∞, 1 ≤ p → p ≠ ⊤ → ∀ f : (Fin (n + m) → ℝ) → ℝ,
      MemLp f p (volume.restrict V) →
        MemLp (fun ξ => ∫ η, κ ξ η * f η) p (volume.restrict V) ∧
        eLpNorm (fun ξ => ∫ η, κ ξ η * f η) p (volume.restrict V) ≤
          ENNReal.ofReal Λ * eLpNorm f p (volume.restrict V) := by
  obtain ⟨ρ, Cv, hS⟩ := C.exists_shellData_patch h.isCompact h.subset_U
  obtain ⟨A, B, hK⟩ := C.exists_sliceBounds_of_hasKernelBounds h.subset_U h.bounds h.measurable
  have hA := hK.A_nonneg
  have hC := hS.Cv_nonneg
  have hρ := hS.ρ_pos
  have hΛ0 : 0 < A * (Cv * 2 ^ (C.G.homogeneousDimension - 1 + 1)) * (2 * ρ) + 1 := by positivity
  refine ⟨A * (Cv * 2 ^ (C.G.homogeneousDimension - 1 + 1)) * (2 * ρ) + 1, hΛ0,
    fun p hp1 hpt f hf => ?_⟩
  have hp'1 : (1 : ℝ) ≤ p.toReal := by
    have := ENNReal.toReal_mono hpt hp1
    simpa using this
  have hpe : ENNReal.ofReal p.toReal = p := ENNReal.ofReal_toReal hpt
  have hgS : MemLp (V.indicator f) (ENNReal.ofReal p.toReal) (volume.restrict S) := by
    rw [hpe, memLp_indicator_iff_restrict h.measurableSet,
      Measure.restrict_restrict h.measurableSet, inter_eq_left.mpr h.subset]
    exact hf
  obtain ⟨hmem, hnorm⟩ := hK.memLp_and_eLpNorm_le hS hΛ0
    (le_add_of_nonneg_right zero_le_one) hp'1 hgS
  have hfun : (fun ξ => ∫ η, κ ξ η * f η) =
      fun x => ∫ y, sliceKernel S κ x y * V.indicator f y ∂(volume.restrict S) := by
    funext ξ
    exact h.integral_eq f ξ
  have hμ : (volume : Measure (Fin (n + m) → ℝ)).restrict V ≤ volume.restrict S :=
    Measure.restrict_mono h.subset le_rfl
  have hnormf : eLpNorm (V.indicator f) p (volume.restrict S) =
      eLpNorm f p (volume.restrict V) := by
    rw [eLpNorm_indicator_eq_eLpNorm_restrict h.measurableSet,
      Measure.restrict_restrict h.measurableSet, inter_eq_left.mpr h.subset]
  rw [hfun]
  rw [hpe] at hmem hnorm
  refine ⟨hmem.mono_measure hμ, ?_⟩
  calc eLpNorm (fun x => ∫ y, sliceKernel S κ x y * V.indicator f y ∂(volume.restrict S)) p
        (volume.restrict V)
      ≤ eLpNorm (fun x => ∫ y, sliceKernel S κ x y * V.indicator f y ∂(volume.restrict S)) p
        (volume.restrict S) := eLpNorm_mono_measure _ hμ
    _ ≤ _ := hnorm
    _ = _ := by rw [hnormf]

/-- **`L^∞ → C^α` for `holderENorm`**: for `0 < α < 1` there is `CH` with
`‖T f‖_{C^α(V)} ≤ CH · sup_V |f|` (`holderENorm` with the lifted control distance `d̃`), for every
`f` measurable on `V`. -/
theorem PatchKernel.exists_holderENorm_bound (h : C.PatchKernel S V κ) {α : ℝ} (hα0 : 0 < α)
    (hα1 : α < 1) :
    ∃ CH : ℝ, 0 < CH ∧ ∀ f : (Fin (n + m) → ℝ) → ℝ,
      AEStronglyMeasurable f (volume.restrict V) →
        holderENorm C.dl α V (fun x => ∫ η, κ x η * f η) ≤
          ENNReal.ofReal CH * ⨆ x : V, ENNReal.ofReal |f x| := by
  obtain ⟨Cs, hCs, hsup⟩ := h.exists_sup_bound
  obtain ⟨Ch, hCh, hhol⟩ := h.exists_holder_bound hα0 hα1
  refine ⟨Cs + Ch, by positivity, fun f hf => ?_⟩
  by_cases hT : (⨆ x : V, ENNReal.ofReal |f x|) = ⊤
  · rw [hT, ENNReal.mul_top (ENNReal.ofReal_pos.mpr (by positivity)).ne']
    exact le_top
  · set M : ℝ := (⨆ x : V, ENNReal.ofReal |f x|).toReal with hMdef
    have hM0 : 0 ≤ M := ENNReal.toReal_nonneg
    have hM : ∀ y ∈ V, |f y| ≤ M := fun y hy =>
      (ENNReal.ofReal_le_iff_le_toReal hT).mp
        (le_iSup (fun x : V => ENNReal.ofReal |f x|) ⟨y, hy⟩)
    have hMe : ENNReal.ofReal M = ⨆ x : V, ENNReal.ofReal |f x| := ENNReal.ofReal_toReal hT
    have hsupT : (⨆ x : V, ENNReal.ofReal |∫ η, κ x η * f η|) ≤ ENNReal.ofReal (Cs * M) :=
      iSup_le fun x => ENNReal.ofReal_le_ofReal (hsup f M hM0 hM x)
    have hsemi : holderSeminorm C.dl α V (fun x => ∫ η, κ x η * f η) ≤
        ENNReal.ofReal (Ch * M) := by
      refine sInf_le ⟨ENNReal.ofReal_lt_top, fun x hx y hy hxy => ?_⟩
      have hb := hhol f hf M hM0 hM x (h.subset hx) y (h.subset hy)
      show ENNReal.ofReal |(∫ η, κ x η * f η) - ∫ η, κ y η * f η| ≤
        ENNReal.ofReal (Ch * M) * C.dl x y ^ α
      calc ENNReal.ofReal |(∫ η, κ x η * f η) - ∫ η, κ y η * f η|
          ≤ ENNReal.ofReal (Ch * M * (C.dl x y).toReal ^ α) := ENNReal.ofReal_le_ofReal hb
        _ = ENNReal.ofReal (Ch * M) * ENNReal.ofReal ((C.dl x y).toReal ^ α) :=
            ENNReal.ofReal_mul (by positivity)
        _ = ENNReal.ofReal (Ch * M) * C.dl x y ^ α := by
            rw [← ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hα0.le,
              ENNReal.ofReal_toReal hxy.ne]
    calc holderENorm C.dl α V (fun x => ∫ η, κ x η * f η)
        = (⨆ x : V, ENNReal.ofReal |∫ η, κ x η * f η|) +
            holderSeminorm C.dl α V (fun x => ∫ η, κ x η * f η) := rfl
      _ ≤ ENNReal.ofReal (Cs * M) + ENNReal.ofReal (Ch * M) := add_le_add hsupT hsemi
      _ = ENNReal.ofReal ((Cs + Ch) * M) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          ring
      _ = ENNReal.ofReal (Cs + Ch) * ENNReal.ofReal M := ENNReal.ofReal_mul (by positivity)
      _ = ENNReal.ofReal (Cs + Ch) * ⨆ x : V, ENNReal.ofReal |f x| := by rw [hMe]

/-- **The Hölder bound for a patch kernel** (BB pp. 566–576, Thm 11.29): for `0 < α < 1`,
`‖T f‖_{C^α(V)} ≤ CH ‖f‖_{C^α(V)}` in `holderENorm` with `d̃`, for every `f`
(`‖f‖_{C^α(V)} = ∞` is trivial; otherwise `f` is continuous, hence measurable, on `V ⊆ U`). -/
theorem PatchKernel.exists_holderENorm_bound_of_holderENorm (h : C.PatchKernel S V κ) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ CH : ℝ, 0 < CH ∧ ∀ f : (Fin (n + m) → ℝ) → ℝ,
      holderENorm C.dl α V (fun x => ∫ η, κ x η * f η) ≤
        ENNReal.ofReal CH * holderENorm C.dl α V f := by
  obtain ⟨CH, hCH, hbound⟩ := h.exists_holderENorm_bound hα0 hα1
  refine ⟨CH, hCH, fun f => ?_⟩
  by_cases hH : holderENorm C.dl α V f = ⊤
  · rw [hH, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hCH).ne']
    exact le_top
  · have hf : AEStronglyMeasurable f (volume.restrict V) :=
      aestronglyMeasurable_of_holderENorm_lt_top (fun y hy => h.subset_U (h.subset hy))
        h.measurableSet hα0 (lt_top_iff_ne_top.mpr hH)
    refine (hbound f hf).trans ?_
    have hsup_le : (⨆ x : V, ENNReal.ofReal |f x|) ≤ holderENorm C.dl α V f := le_self_add
    gcongr

end LiftedChart
end RothschildStein.P1
