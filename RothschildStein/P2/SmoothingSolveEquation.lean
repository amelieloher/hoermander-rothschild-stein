-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.Solvability
public import RothschildStein.P2.Hypoellipticity
public import RothschildStein.P2.SmoothingSobolev
public import RothschildStein.Definitions.driftWeight
public import RothschildStein.Definitions.memHolderX
public import RothschildStein.Definitions.memSobolevX

/-!
# Local solvability (statement) and the abstract part of lift, solve and subtract

* `weakDriftEquation V X v g` / `intrinsicDriftEquation V X v g`: the equation `L v = g`,
  `L = ∑ Xᵢ² + X₀`, for `v ∈ W^{2,p}` through the weak word derivatives `X₀ v`, `Xᵢ Xᵢ v`
  (a.e. on `V`), respectively for `v ∈ C^{2,α}` through the intrinsic word derivatives (pointwise
  on `V`), the form of the conclusion of the Hölder regularity theorem `rs3_drift_holder`.
* `LocalSolvability C`: local solvability in the lifted drift chart, as needed for smoothing
  (BB pp. 605-608, Prop 11.61, (11.97)-(11.100)) in a lifted drift chart: for all sufficiently
  small balls `U_R = B̃(ξ₀, R)`, `g ∈ L^p(U_R)` has `v ∈ W^{2,p}_{X̃}(U_R)` with `L̃ v = g` a.e.
  and `g ∈ C^α_{X̃}(U_R)` has `v ∈ C^{2,α}_{X̃}(U_{R/2})` with `L̃ v = g` there.
* `hasDistributionEquationWithDrift_ofFun_of_weakDriftEquation` (the weak-derivative definition, for `v ∈ W^{2,p}`): a weak
  solution is a distributional solution.
* `exists_smooth_add_of_hasDistributionEquationWithDrift` (lift, solve and subtract, abstract part):
  if `T ∈ 𝒟'(V)` has `L T = f`, `v` solves `L v = f` weakly and the fields satisfy the Hörmander
  condition on `V`, then `T = v + H` with `H` smooth on `V` (`H = T - v` solves `L H = 0`,
  the homogeneous hypoellipticity statement).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped ENNReal NNReal Topology BigOperators Distributions
open RothschildStein.P1
namespace RothschildStein.P2

section Equations

variable {n q : ℕ}

/-- The weak drift equation `L v = g` on `V`, `L = ∑ Xᵢ² + X₀`: `X₀ v` and `Xᵢ Xᵢ v` exist as weak
word derivatives and `(∑ᵢ XᵢXᵢ v) + X₀ v = g` almost everywhere on `V`. -/
def weakDriftEquation (V : Opens (Fin n → ℝ))
    (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ)) (v g : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (g₀ : (Fin n → ℝ) → ℝ) (gs : Fin q → (Fin n → ℝ) → ℝ),
    hasWeakWordDeriv X V [0] v g₀ ∧
    (∀ i : Fin q, hasWeakWordDeriv X V [i.succ, i.succ] v (gs i)) ∧
    ∀ᵐ x ∂(volume.restrict (V : Set (Fin n → ℝ))), (∑ i, gs i x) + g₀ x = g x

/-- The intrinsic drift equation `L v = g` on `V`: `X₀ v` and `Xᵢ Xᵢ v` exist as intrinsic
word derivatives and `(∑ᵢ XᵢXᵢ v) + X₀ v = g` at every point of `V` (the shape of the conclusion of
the drift Hölder regularity theorem). -/
def intrinsicDriftEquation (V : Opens (Fin n → ℝ))
    (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ)) (v g : (Fin n → ℝ) → ℝ) : Prop :=
  ∃ (g₀ : (Fin n → ℝ) → ℝ) (gs : Fin q → (Fin n → ℝ) → ℝ),
    hasIntrinsicWordDeriv X V [0] v g₀ ∧
    (∀ i : Fin q, hasIntrinsicWordDeriv X V [i.succ, i.succ] v (gs i)) ∧
    ∀ x ∈ (V : Set (Fin n → ℝ)), (∑ i, gs i x) + g₀ x = g x

theorem locallyIntegrableOn_finsetSum {V : Set (Fin n → ℝ)} {ι : Type*} (s : Finset ι)
    {f : ι → (Fin n → ℝ) → ℝ} (hf : ∀ i ∈ s, LocallyIntegrableOn (f i) V volume) :
    LocallyIntegrableOn (fun x => ∑ i ∈ s, f i x) V volume := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using locallyIntegrableOn_zero
  | insert a s ha ih =>
    have h1 := hf a (Finset.mem_insert_self a s)
    have h2 := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    have he : (fun x => ∑ i ∈ insert a s, f i x) = fun x => f a x + ∑ i ∈ s, f i x :=
      funext fun x => Finset.sum_insert ha
    rw [he]
    exact h1.add h2

/-- The right-hand side of a weak drift equation is locally integrable on `V`. -/
theorem weakDriftEquation.locallyIntegrableOn {V : Opens (Fin n → ℝ)}
    {X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ)} {v g : (Fin n → ℝ) → ℝ}
    (h : weakDriftEquation V X v g) : LocallyIntegrableOn g (V : Set (Fin n → ℝ)) volume := by
  obtain ⟨g₀, gs, h0, hs, hae⟩ := h
  have hsum : LocallyIntegrableOn (fun x => (∑ i, gs i x) + g₀ x) (V : Set (Fin n → ℝ)) volume :=
    (locallyIntegrableOn_finsetSum Finset.univ (fun i _ => (hs i).2.1)).add h0.2.1
  exact hsum.congr hae

/-- The function `v` of a weak drift equation is locally integrable on `V`. -/
theorem weakDriftEquation.locallyIntegrableOn_left {V : Opens (Fin n → ℝ)}
    {X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ)} {v g : (Fin n → ℝ) → ℝ}
    (h : weakDriftEquation V X v g) : LocallyIntegrableOn v (V : Set (Fin n → ℝ)) volume := by
  obtain ⟨g₀, gs, h0, -, -⟩ := h
  exact h0.1

theorem fieldTransposeTest_eq_wordTransposeTest_singleton {k : ℕ} (V : Opens (Fin n → ℝ))
    (X : Fin k → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (V : Set (Fin n → ℝ))) (i : Fin k)
    (φ : TestFunction V ℝ (⊤ : ℕ∞)) :
    wordTransposeTest V X hX [i] φ = fieldTransposeTest V (X i) (hX i) φ := by
  apply TestFunction.ext
  intro x
  rw [RothschildStein.S.wordTransposeTest_apply, RothschildStein.S.fieldTransposeTest_apply]
  rfl

theorem fieldTransposeTest_comp_eq_wordTransposeTest_pair {k : ℕ} (V : Opens (Fin n → ℝ))
    (X : Fin k → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (V : Set (Fin n → ℝ))) (i : Fin k)
    (φ : TestFunction V ℝ (⊤ : ℕ∞)) :
    wordTransposeTest V X hX [i, i] φ =
      fieldTransposeTest V (X i) (hX i) (fieldTransposeTest V (X i) (hX i) φ) := by
  apply TestFunction.ext
  intro x
  rw [RothschildStein.S.wordTransposeTest_apply, RothschildStein.S.fieldTransposeTest_apply,
    RothschildStein.S.fieldTransposeTest_coe]
  rfl

/-- `ofFun` of a finite sum, evaluated on a test. -/
theorem ofFun_finsetSum_apply {V : Opens (Fin n → ℝ)} {ι : Type*} (s : Finset ι)
    {f : ι → (Fin n → ℝ) → ℝ} (hf : ∀ i ∈ s, LocallyIntegrableOn (f i) (V : Set (Fin n → ℝ)) volume)
    (φ : TestFunction V ℝ (⊤ : ℕ∞)) :
    Distribution.ofFun V (fun x => ∑ i ∈ s, f i x) volume (⊤ : ℕ∞) φ =
      ∑ i ∈ s, Distribution.ofFun V (f i) volume (⊤ : ℕ∞) φ := by
  have hsum := locallyIntegrableOn_finsetSum s hf
  rw [Distribution.ofFun_apply hsum,
    Finset.sum_congr rfl (fun i hi => Distribution.ofFun_apply (hf i hi))]
  simp_rw [Finset.smul_sum]
  exact integral_finsetSum s (fun i hi => φ.integrable_smul (hf i hi))

/-- A weak solution is a distributional solution: if `X₀ v` and `Xᵢ Xᵢ v` exist as weak
word derivatives on `V` and `(∑ XᵢXᵢ v) + X₀ v = g` a.e., then the distribution of `v` satisfies the
distributional equation `L (ofFun v) = g` (BB p. 67-68, Def 2.1). -/
theorem hasDistributionEquationWithDrift_ofFun_of_weakDriftEquation (V : Opens (Fin n → ℝ))
    (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (V : Set (Fin n → ℝ)))
    {v g : (Fin n → ℝ) → ℝ} (hv : weakDriftEquation V X v g) :
    hasDistributionEquationWithDrift V X hX (Distribution.ofFun V v volume (⊤ : ℕ∞)) g := by
  have hg := hv.locallyIntegrableOn
  obtain ⟨g₀, gs, h0, hs, hae⟩ := hv
  refine ⟨hg, fun φ => ?_⟩
  have e0 : Distribution.ofFun V v volume (⊤ : ℕ∞) (fieldTransposeTest V (X 0) (hX 0) φ) =
      Distribution.ofFun V g₀ volume (⊤ : ℕ∞) φ := by
    have := congrArg (fun D : Distribution V ℝ (⊤ : ℕ∞) => D φ)
      (RothschildStein.S.distributionWord_ofFun_eq V X hX [0] v g₀ h0)
    simp only [RothschildStein.S.distributionWordCLM_apply,
      fieldTransposeTest_eq_wordTransposeTest_singleton] at this
    exact this
  have e1 : ∀ i : Fin q, Distribution.ofFun V v volume (⊤ : ℕ∞)
      (fieldTransposeTest V (X i.succ) (hX i.succ) (fieldTransposeTest V (X i.succ) (hX i.succ) φ)) =
        Distribution.ofFun V (gs i) volume (⊤ : ℕ∞) φ := by
    intro i
    have := congrArg (fun D : Distribution V ℝ (⊤ : ℕ∞) => D φ)
      (RothschildStein.S.distributionWord_ofFun_eq V X hX [i.succ, i.succ] v (gs i) (hs i))
    simp only [RothschildStein.S.distributionWordCLM_apply,
      fieldTransposeTest_comp_eq_wordTransposeTest_pair] at this
    exact this
  have hsumloc := locallyIntegrableOn_finsetSum (V := (V : Set (Fin n → ℝ))) Finset.univ
    (fun i _ => (hs i).2.1)
  have hadd := congrArg (fun D : Distribution V ℝ (⊤ : ℕ∞) => D φ)
    (Distribution.ofFun_add (Ω := V) (n := (⊤ : ℕ∞)) (μ := volume) hsumloc h0.2.1)
  have hcongr := congrArg (fun D : Distribution V ℝ (⊤ : ℕ∞) => D φ)
    (Distribution.ofFun_congr_ae (Ω := V) (n := (⊤ : ℕ∞)) (μ := volume) hae)
  have hadd' : Distribution.ofFun V (fun x => (∑ i, gs i x) + g₀ x) volume (⊤ : ℕ∞) φ =
      Distribution.ofFun V (fun x => ∑ i, gs i x) volume (⊤ : ℕ∞) φ +
        Distribution.ofFun V g₀ volume (⊤ : ℕ∞) φ := hadd
  unfold sumSquaresWithDriftTransposeTest
  rw [map_add, map_sum, e0]
  simp_rw [e1]
  rw [← ofFun_finsetSum_apply Finset.univ (fun i _ => (hs i).2.1), add_comm]
  exact (hadd'.symm.trans hcongr)

/-- The distributional drift equation restricts to a smaller open set (`L` is local). -/
theorem hasDistributionEquationWithDrift_restrict (V U : Opens (Fin n → ℝ)) (hUV : U ≤ V)
    (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (V : Set (Fin n → ℝ)))
    {T : Distribution V ℝ (⊤ : ℕ∞)} {f : (Fin n → ℝ) → ℝ}
    (hT : hasDistributionEquationWithDrift V X hX T f) :
    hasDistributionEquationWithDrift U X (fun i => (hX i).mono hUV)
      (RothschildStein.S.distributionRestrictionCLM V U T) f := by
  refine ⟨hT.1.mono_set hUV, fun φ => ?_⟩
  let φ' : TestFunction V ℝ (⊤ : ℕ∞) :=
    ⟨φ, φ.contDiff, φ.hasCompactSupport, φ.tsupport_subset.trans hUV⟩
  have hcoe : (sumSquaresWithDriftTransposeTest U X (fun i => (hX i).mono hUV) φ :
      (Fin n → ℝ) → ℝ) = sumSquaresWithDriftTranspose X φ :=
    P1.sumSquaresWithDriftTransposeTest_coe U X _ φ
  have hcoe' : (sumSquaresWithDriftTransposeTest V X hX φ' : (Fin n → ℝ) → ℝ) =
      sumSquaresWithDriftTranspose X φ' :=
    P1.sumSquaresWithDriftTransposeTest_coe V X hX φ'
  rw [RothschildStein.S.distributionRestrictionCLM_apply V U hUV T]
  have hmem : (⟨(sumSquaresWithDriftTransposeTest U X (fun i => (hX i).mono hUV) φ :
      (Fin n → ℝ) → ℝ), (sumSquaresWithDriftTransposeTest U X (fun i => (hX i).mono hUV) φ).contDiff,
      (sumSquaresWithDriftTransposeTest U X (fun i => (hX i).mono hUV) φ).hasCompactSupport,
      (sumSquaresWithDriftTransposeTest U X (fun i => (hX i).mono hUV) φ).tsupport_subset.trans
        hUV⟩ : TestFunction V ℝ (⊤ : ℕ∞)) = sumSquaresWithDriftTransposeTest V X hX φ' := by
    apply TestFunction.ext
    intro x
    change (sumSquaresWithDriftTransposeTest U X (fun i => (hX i).mono hUV) φ :
      (Fin n → ℝ) → ℝ) x = (sumSquaresWithDriftTransposeTest V X hX φ' : (Fin n → ℝ) → ℝ) x
    rw [hcoe, hcoe']
    rfl
  rw [hmem, hT.2 φ', Distribution.ofFun_apply hT.1, Distribution.ofFun_apply (hT.1.mono_set hUV)]
  rfl

/-- Let `V` be open, the fields smooth on `V` with the
Hörmander rank condition `bracketSpansOn V X`, `T ∈ 𝒟'(V)` with `L T = f`, and `v` a weak solution
of `L v = g` on `V` with `f = g` a.e. Then `H = T - v` solves `L H = 0` distributionally,
so by the homogeneous hypoellipticity statement it is a smooth function `h`, and `T` is the regular distribution of `v + h`
(BB p. 609-610: `T = v + H`). -/
theorem exists_smooth_add_of_hasDistributionEquationWithDrift (V : Opens (Fin n → ℝ))
    (X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ))
    (hX : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (X i) (V : Set (Fin n → ℝ)))
    (hspan : bracketSpansOn (V : Set (Fin n → ℝ)) X) (T : Distribution V ℝ (⊤ : ℕ∞))
    {f v g : (Fin n → ℝ) → ℝ} (hT : hasDistributionEquationWithDrift V X hX T f)
    (hv : weakDriftEquation V X v g)
    (hfg : f =ᵐ[volume.restrict (V : Set (Fin n → ℝ))] g) :
    ∃ h : (Fin n → ℝ) → ℝ, ContDiffOn ℝ (⊤ : ℕ∞) h (V : Set (Fin n → ℝ)) ∧
      T = Distribution.ofFun V (fun x => v x + h x) volume (⊤ : ℕ∞) := by
  have hvloc := hv.locallyIntegrableOn_left
  have hDv := hasDistributionEquationWithDrift_ofFun_of_weakDriftEquation V X hX hv
  have hH : hasDistributionEquationWithDrift V X hX
      (T - Distribution.ofFun V v volume (⊤ : ℕ∞)) 0 := by
    refine ⟨locallyIntegrableOn_zero, fun φ => ?_⟩
    have h1 := hT.2 φ
    have h2 := hDv.2 φ
    have h3 : Distribution.ofFun V f volume (⊤ : ℕ∞) φ =
        Distribution.ofFun V g volume (⊤ : ℕ∞) φ :=
      congrArg (fun D : Distribution V ℝ (⊤ : ℕ∞) => D φ)
        (Distribution.ofFun_congr_ae (Ω := V) (n := (⊤ : ℕ∞)) (μ := volume) hfg)
    have h4 : (T - Distribution.ofFun V v volume (⊤ : ℕ∞))
        (sumSquaresWithDriftTransposeTest V X hX φ) =
        T (sumSquaresWithDriftTransposeTest V X hX φ) -
          Distribution.ofFun V v volume (⊤ : ℕ∞) (sumSquaresWithDriftTransposeTest V X hX φ) := rfl
    rw [h4, h1, h2, h3, sub_self]
    have : Distribution.ofFun V (0 : (Fin n → ℝ) → ℝ) volume (⊤ : ℕ∞) = 0 := Distribution.ofFun_zero
    rw [this]
    rfl
  obtain ⟨h, hsm, hHeq, -⟩ :=
    exists_smooth_representative_of_hasDistributionEquationWithDrift V X hX hspan _ hH
  refine ⟨h, hsm, ?_⟩
  have hhloc : LocallyIntegrableOn h (V : Set (Fin n → ℝ)) volume :=
    hsm.continuousOn.locallyIntegrableOn V.isOpen.measurableSet
  have hsum := Distribution.ofFun_add (Ω := V) (n := (⊤ : ℕ∞)) (μ := volume) hvloc hhloc
  have : T = Distribution.ofFun V v volume (⊤ : ℕ∞) +
      (T - Distribution.ofFun V v volume (⊤ : ℕ∞)) := by abel
  rw [this, hHeq]
  exact hsum.symm

/-- The Hörmander rank condition from the step condition at every point of a set. -/
theorem bracketSpansOn_of_stepSpansAt {k : ℕ} {w : Fin k → ℕ+} {s : ℕ}
    {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {S : Set (Fin n → ℝ)}
    (h : ∀ x ∈ S, StepSpansAt w s X x) : bracketSpansOn S X := by
  intro x hx
  apply top_unique
  have hx' := h x hx
  unfold StepSpansAt at hx'
  rw [← hx']
  apply Submodule.span_mono
  rintro v ⟨I, hI, -, rfl⟩
  exact ⟨I, hI, rfl⟩

end Equations

section Statement

variable {n q s m : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}

/-- **Local solvability needed for smoothing** (BB pp. 605-608, Prop 11.61, (11.97)-(11.100)),
in a fixed lifted drift chart `C`. For every centre `ξ₀ ∈ U`:

* for `1 < p < ∞` there is `R₀ > 0` (depending only on the chart data and `p`) such that for every
  `0 < R < R₀`, on the open ball `U_R = B̃(ξ₀, R)` every `g ∈ L^p(U_R)` has a `v ∈ W^{2,p}_{X̃}(U_R)`
  (`memSobolevX`) with `L̃ v = g` almost everywhere (`weakDriftEquation`);
* for `0 < α < 1` there is `R₀ > 0` (depending only on the chart data and `α`) such that for every
  `0 < R < R₀`, every `g ∈ C^α_{X̃}(U_R)` (`memHolderX`, order `0`) has a
  `v ∈ C^{2,α}_{X̃}(U_{R/2})` (`memHolderX`, order `2`) with `L̃ v = g` on `U_{R/2}`
  (`intrinsicDriftEquation`).

The balls `U_R` are control balls of the lifted distance `d̃`; they are Euclidean open for small `R`,
and the statement quantifies over every open set `UR` equal to the ball. This is the exact
statement of local solvability; the weaker distributional form already proved
(`exists_lp_solution_of_lpIdentity`, `exists_holder_solution_of_lpIdentity`) gives `L̃ v = g` in
distributions, and its membership/regularity half is the gain theorem. -/
def LocalSolvability
    (C : P1.LiftedChart (fun i : Fin (q + 1) => if i = 0 then (2 : ℕ+) else 1) s Ω hΩ X x₀ m) :
    Prop :=
  ∀ ξ₀ ∈ C.U,
    (∀ p : ℝ≥0∞, 1 < p → p < ⊤ → ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, 0 < R → R < R₀ →
      ∀ UR : Opens (Fin (n + m) → ℝ), (UR : Set (Fin (n + m) → ℝ)) = C.driftBall ξ₀ R →
        ∀ g : (Fin (n + m) → ℝ) → ℝ, MemLp g p (volume.restrict (UR : Set (Fin (n + m) → ℝ))) →
          ∃ v : (Fin (n + m) → ℝ) → ℝ, memSobolevX driftWeight C.Xl UR 2 p v ∧
            weakDriftEquation UR C.Xl v g) ∧
    (∀ α : ℝ, 0 < α → α < 1 → ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R : ℝ, 0 < R → R < R₀ →
      ∀ UR UR' : Opens (Fin (n + m) → ℝ), (UR : Set (Fin (n + m) → ℝ)) = C.driftBall ξ₀ R →
        (UR' : Set (Fin (n + m) → ℝ)) = C.driftBall ξ₀ (R / 2) →
        ∀ g : (Fin (n + m) → ℝ) → ℝ, memHolderX driftWeight C.Xl C.dl UR 0 α g →
          ∃ v : (Fin (n + m) → ℝ) → ℝ, memHolderX driftWeight C.Xl C.dl UR' 2 α v ∧
            intrinsicDriftEquation UR' C.Xl v g)

end Statement

end RothschildStein.P2
