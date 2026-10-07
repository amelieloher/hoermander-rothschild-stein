-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.TransferCoverCore
public import RothschildStein.H3.SobolevGlobalCutoff
public import RothschildStein.S.SobolevCutoffZero
public import RothschildStein.S.SobolevSubtraction
public import RothschildStein.S.CompactSobolevRestriction
public import RothschildStein.S.CutoffBounds
public import RothschildStein.S.SobolevAE
public import RothschildStein.P1.WeakExtensionJet

/-!
# Support lemmas for the higher Sobolev regularity (no drift)

Elementary facts on the weak-word Sobolev classes used by the compact recurrence, the cutoff
estimates and the regularity induction of the higher Sobolev estimate (BB pp. 588-591):

* weak word derivatives of a function vanishing off a closed set vanish a.e. off that set
  (`hasWeakWordDeriv_ae_zero_off`), so a Sobolev function that vanishes a.e. off a compact subset of `V`
  lies in the closure space `W_0(V)` (`memSobolevXZero_of_zero_off`);
* additivity, real multiples and finite sums of Sobolev functions, with the triangle inequality for
  `sobolevXENorm`;
* monotonicity of `sobolevXENorm` in the order, and `‖X̃_i u‖_{W^{N}} ≤ ‖u‖_{W^{N+1}}`
  (all weights one);
* extension by zero of a compactly supported function with a weak operator value
  (`HasWeakOperatorValue.extend`) and of Sobolev membership.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Filter TopologicalSpace
open scoped ENNReal Topology BigOperators
namespace RothschildStein.P2

section ZeroOff

variable {N k : ℕ} {w : Fin k → ℕ+} {Xt : Fin k → (Fin N → ℝ) → (Fin N → ℝ)}
  {V : Opens (Fin N → ℝ)}

/-- The weak word derivatives of a function that vanishes off a closed set `K₀` vanish a.e. off
`K₀` (locality of weak derivatives on the open set `V \ K₀`). -/
theorem hasWeakWordDeriv_ae_zero_off {K₀ : Set (Fin N → ℝ)} (hK₀ : IsClosed K₀)
    {I : List (Fin k)} {v g : (Fin N → ℝ) → ℝ} (hv : ∀ x, x ∉ K₀ → v x = 0)
    (h : hasWeakWordDeriv Xt V I v g) :
    ∀ᵐ x ∂(volume.restrict (V : Set (Fin N → ℝ))), x ∉ K₀ → g x = 0 := by
  let U : Opens (Fin N → ℝ) := ⟨(V : Set (Fin N → ℝ)) ∩ K₀ᶜ, V.isOpen.inter hK₀.isOpen_compl⟩
  have hUV : (U : Set (Fin N → ℝ)) ⊆ (V : Set (Fin N → ℝ)) := inter_subset_left
  have hv0 : v =ᵐ[volume.restrict (U : Set (Fin N → ℝ))] (fun _ => 0) := by
    rw [Filter.EventuallyEq, ae_restrict_iff' U.isOpen.measurableSet]
    exact Filter.Eventually.of_forall fun x hx => hv x hx.2
  have hg0 := RothschildStein.S.hasWeakWordDeriv_locality Xt V U hUV h hv0
  rw [Filter.EventuallyEq, ae_restrict_iff' U.isOpen.measurableSet] at hg0
  rw [ae_restrict_iff' V.isOpen.measurableSet]
  filter_upwards [hg0] with x hx hxV hxK
  exact hx ⟨hxV, hxK⟩

/-- A Sobolev function that vanishes a.e. off a compact subset of `V` lies in the closure space
`W^{kk,P}_{X̃,0}(V)` (multiplication by a test function equal to one near the compact set). -/
theorem memSobolevXZero_of_zero_off {P : ℝ≥0∞} [Fact (1 ≤ P)]
    (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Xt i) (V : Set (Fin N → ℝ)))
    {K₀ : Set (Fin N → ℝ)} (hK₀ : IsCompact K₀) (hKV : K₀ ⊆ (V : Set (Fin N → ℝ)))
    (hP : P ≠ ⊤) {kk : ℕ} {h : (Fin N → ℝ) → ℝ} (hh : memSobolevX w Xt V kk P h)
    (hz : ∀ᵐ x ∂(volume.restrict (V : Set (Fin N → ℝ))), x ∉ K₀ → h x = 0) :
    memSobolevXZero w Xt V kk P h := by
  obtain ⟨χ, U, -, hKU, -, hχ⟩ := RothschildStein.S.exists_test_plateau V ⟨K₀, hK₀⟩ hKV
  have hmul := RothschildStein.S.memSobolevXZero_mul_test w Xt V hXt kk hP hh χ
  have hae : (fun x => h x * χ x) =ᵐ[volume.restrict (V : Set (Fin N → ℝ))] h := by
    filter_upwards [hz] with x hx
    by_cases hxK : x ∈ K₀
    · have := hχ (hKU hxK)
      simp only [Pi.one_apply] at this
      rw [this, mul_one]
    · rw [hx hxK, zero_mul]
  exact (RothschildStein.S.memSobolevXZero_congr_ae Xt V w kk P hae).1 hmul

end ZeroOff

section Algebra

variable {N k : ℕ} {w : Fin k → ℕ+} {Xt : Fin k → (Fin N → ℝ) → (Fin N → ℝ)}
  {V : Opens (Fin N → ℝ)}

/-- Sobolev classes are closed under addition. -/
theorem memSobolevX_add' (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Xt i) (V : Set (Fin N → ℝ)))
    {kk : ℕ} {P : ℝ≥0∞} {f₁ f₂ : (Fin N → ℝ) → ℝ} (h₁ : memSobolevX w Xt V kk P f₁)
    (h₂ : memSobolevX w Xt V kk P f₂) : memSobolevX w Xt V kk P (fun x => f₁ x + f₂ x) := by
  refine ⟨h₁.1.add h₂.1, fun I hI => ?_⟩
  obtain ⟨g₁, hg₁, hl₁⟩ := h₁.2 I hI
  obtain ⟨g₂, hg₂, hl₂⟩ := h₂.2 I hI
  exact ⟨fun x => g₁ x + g₂ x, RothschildStein.S.hasWeakWordDeriv_add Xt V hXt hg₁ hg₂,
    hl₁.add hl₂⟩

/-- Sobolev classes are closed under multiplication by constants. -/
theorem memSobolevX_const_mul {kk : ℕ} {P : ℝ≥0∞} {f : (Fin N → ℝ) → ℝ} (c : ℝ)
    (h : memSobolevX w Xt V kk P f) : memSobolevX w Xt V kk P (fun x => c * f x) := by
  refine ⟨h.1.const_mul c, fun I hI => ?_⟩
  obtain ⟨g, hg, hl⟩ := h.2 I hI
  exact ⟨fun x => c * g x, RothschildStein.S.hasWeakWordDeriv_smul Xt V hg c, hl.const_mul c⟩

/-- The zero function is a Sobolev function. -/
theorem memSobolevX_zero_fun {kk : ℕ} {P : ℝ≥0∞} :
    memSobolevX w Xt V kk P (fun _ => (0 : ℝ)) := by
  refine ⟨MemLp.zero, fun I _ => ⟨fun _ => 0, RothschildStein.S.hasWeakWordDeriv_zero Xt V I,
    MemLp.zero⟩⟩

/-- Finite sums of Sobolev functions are Sobolev functions. -/
theorem memSobolevX_finset_sum (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Xt i) (V : Set (Fin N → ℝ)))
    {ι : Type*} (s : Finset ι) {kk : ℕ} {P : ℝ≥0∞} {f : ι → (Fin N → ℝ) → ℝ}
    (h : ∀ i ∈ s, memSobolevX w Xt V kk P (f i)) :
    memSobolevX w Xt V kk P (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using memSobolevX_zero_fun (w := w) (Xt := Xt) (V := V) (kk := kk) (P := P)
  | insert a s ha ih =>
    have h1 := memSobolevX_add' hXt (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))
    simpa only [Finset.sum_insert ha] using h1

/-- The triangle inequality for `sobolevXENorm`. -/
theorem sobolevXENorm_add_le' (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Xt i) (V : Set (Fin N → ℝ)))
    {kk : ℕ} {P : ℝ≥0∞} (hP : 1 ≤ P) {f₁ f₂ : (Fin N → ℝ) → ℝ}
    (h₁ : memSobolevX w Xt V kk P f₁) (h₂ : memSobolevX w Xt V kk P f₂) :
    sobolevXENorm w Xt V kk P (fun x => f₁ x + f₂ x) ≤
      sobolevXENorm w Xt V kk P f₁ + sobolevXENorm w Xt V kk P f₂ := by
  unfold sobolevXENorm
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun I hI => ?_
  obtain ⟨g₁, hg₁, -⟩ := h₁.2 I hI
  obtain ⟨g₂, hg₂, -⟩ := h₂.2 I hI
  rw [RothschildStein.S.weakWordENorm_eq Xt V I P _ _
      (RothschildStein.S.hasWeakWordDeriv_add Xt V hXt hg₁ hg₂),
    RothschildStein.S.weakWordENorm_eq Xt V I P _ _ hg₁,
    RothschildStein.S.weakWordENorm_eq Xt V I P _ _ hg₂]
  exact eLpNorm_add_le hP

/-- The `sobolevXENorm` of a constant multiple. -/
theorem sobolevXENorm_const_mul {kk : ℕ} {P : ℝ≥0∞} {f : (Fin N → ℝ) → ℝ} (c : ℝ)
    (h : memSobolevX w Xt V kk P f) :
    sobolevXENorm w Xt V kk P (fun x => c * f x) = ENNReal.ofReal |c| * sobolevXENorm w Xt V kk P f := by
  unfold sobolevXENorm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun I hI => ?_
  obtain ⟨g, hg, -⟩ := h.2 I hI
  rw [RothschildStein.S.weakWordENorm_eq Xt V I P _ _
      (RothschildStein.S.hasWeakWordDeriv_smul Xt V hg c),
    RothschildStein.S.weakWordENorm_eq Xt V I P _ _ hg]
  have : (fun x => c * g x) = c • g := rfl
  rw [this, eLpNorm_const_smul, Real.enorm_eq_ofReal_abs]

/-- The `sobolevXENorm` of a finite sum. -/
theorem sobolevXENorm_finset_sum_le (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Xt i) (V : Set (Fin N → ℝ)))
    {ι : Type*} (s : Finset ι) {kk : ℕ} {P : ℝ≥0∞} (hP : 1 ≤ P) {f : ι → (Fin N → ℝ) → ℝ}
    (h : ∀ i ∈ s, memSobolevX w Xt V kk P (f i)) :
    sobolevXENorm w Xt V kk P (fun x => ∑ i ∈ s, f i x) ≤
      ∑ i ∈ s, sobolevXENorm w Xt V kk P (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    unfold sobolevXENorm
    refine le_of_eq (Finset.sum_eq_zero fun I _ => ?_)
    rw [RothschildStein.S.weakWordENorm_eq Xt V I P _ _ (RothschildStein.S.hasWeakWordDeriv_zero Xt V I)]
    simp
  | insert a s ha ih =>
    have hs : ∀ i ∈ s, memSobolevX w Xt V kk P (f i) := fun i hi => h i (Finset.mem_insert_of_mem hi)
    have h1 := sobolevXENorm_add_le' hXt hP (h a (Finset.mem_insert_self a s))
      (memSobolevX_finset_sum hXt s hs)
    simp only [Finset.sum_insert ha]
    exact h1.trans (add_le_add le_rfl (ih hs))

/-- `sobolevXENorm` is monotone in the order. -/
theorem sobolevXENorm_mono_order {kk ll : ℕ} (hkl : kk ≤ ll) {P : ℝ≥0∞}
    (f : (Fin N → ℝ) → ℝ) :
    sobolevXENorm w Xt V kk P f ≤ sobolevXENorm w Xt V ll P f := by
  unfold sobolevXENorm
  refine Finset.sum_le_sum_of_subset fun I hI => ?_
  rw [RothschildStein.S.mem_wordFamily_iff] at hI ⊢
  exact hI.trans hkl

end Algebra

section Derivative

variable {N k : ℕ} {w : Fin k → ℕ+} {Xt : Fin k → (Fin N → ℝ) → (Fin N → ℝ)}
  {V : Opens (Fin N → ℝ)}

theorem wordWeight_eq_length' (hw : ∀ j, (w j : ℕ) = 1) (L : List (Fin k)) :
    wordWeight w L = L.length :=
  RothschildStein.P1.wordWeight_eq_length hw L

/-- For a weak jet of `u` of order `N' + 1` (all weights one), the first derivative `X̃_i u` lies in
`W^{N',P}` and `‖X̃_i u‖_{W^{N'}} ≤ ‖u‖_{W^{N'+1}}`. -/
theorem memSobolevX_jet_deriv (hXt : ∀ i, ContDiffOn ℝ (⊤ : ℕ∞) (Xt i) (V : Set (Fin N → ℝ)))
    (hw : ∀ j, (w j : ℕ) = 1) {N' : ℕ} {P : ℝ≥0∞} {u : (Fin N → ℝ) → ℝ}
    {D : List (Fin k) → (Fin N → ℝ) → ℝ} (hD : RothschildStein.P1.IsWeakJet w Xt V (N' + 1) P u D)
    (i : Fin k) :
    memSobolevX w Xt V N' P (D [i]) ∧
      sobolevXENorm w Xt V N' P (D [i]) ≤ sobolevXENorm w Xt V (N' + 1) P u := by
  have hmem : ∀ J ∈ wordFamily w N', J ++ [i] ∈ wordFamily w (N' + 1) := by
    intro J hJ
    rw [RothschildStein.S.mem_wordFamily_iff] at hJ ⊢
    rw [wordWeight_eq_length' hw] at hJ ⊢
    simp only [List.length_append, List.length_singleton]
    omega
  have hder : ∀ J ∈ wordFamily w N', hasWeakWordDeriv Xt V J (D [i]) (D (J ++ [i])) :=
    fun J hJ => hD.hasWeakWordDeriv_append hXt [i] J (hmem J hJ)
  refine ⟨⟨(hD [i] ?_).2, fun J hJ => ⟨D (J ++ [i]), hder J hJ, (hD _ (hmem J hJ)).2⟩⟩, ?_⟩
  · rw [RothschildStein.S.mem_wordFamily_iff, wordWeight_eq_length' hw]
    simp
  · unfold sobolevXENorm
    have h1 : ∑ J ∈ wordFamily w N', weakWordENorm Xt V J P (D [i]) =
        ∑ J ∈ wordFamily w N', weakWordENorm Xt V (J ++ [i]) P u := by
      refine Finset.sum_congr rfl fun J hJ => ?_
      rw [RothschildStein.S.weakWordENorm_eq Xt V J P _ _ (hder J hJ),
        RothschildStein.S.weakWordENorm_eq Xt V (J ++ [i]) P _ _ (hD _ (hmem J hJ)).1]
    rw [h1, ← Finset.sum_image (f := fun I => weakWordENorm Xt V I P u)
      (s := wordFamily w N') (g := fun J => J ++ [i]) (fun a _ b _ hab => by
        simpa using hab)]
    refine Finset.sum_le_sum_of_subset fun I hI => ?_
    obtain ⟨J, hJ, rfl⟩ := Finset.mem_image.1 hI
    exact hmem J hJ

end Derivative

section Extension

variable {N k : ℕ} {w : Fin k → ℕ+} {Xt : Fin k → (Fin N → ℝ) → (Fin N → ℝ)}

/-- A function vanishing off a compact subset `K₀ ⊆ U` coincides with its extension by zero. -/
theorem indicator_eq_self_of_zero_off {U : Set (Fin N → ℝ)} {K₀ : Set (Fin N → ℝ)} (hKU : K₀ ⊆ U)
    {v : (Fin N → ℝ) → ℝ} (hv : ∀ x, x ∉ K₀ → v x = 0) : U.indicator v = v := by
  funext x
  by_cases hx : x ∈ U
  · exact indicator_of_mem hx v
  · rw [indicator_of_notMem hx]
    exact (hv x fun hxK => hx (hKU hxK)).symm

/-- Extension by zero of a weak operator value: if `v` vanishes off a compact `K₀ ⊆ U ⊆ V'`
and `L̃ v = f` weakly on `U`, then `L̃ v = 1_U f` weakly on `V'`. -/
theorem HasWeakOperatorValue.extend {ι : Type} [Fintype ι] {J : ι → List (Fin k)}
    {U V' : Opens (Fin N → ℝ)} (hUV : (U : Set (Fin N → ℝ)) ⊆ (V' : Set (Fin N → ℝ)))
    {K₀ : Set (Fin N → ℝ)} (hK₀ : IsCompact K₀) (hKU : K₀ ⊆ (U : Set (Fin N → ℝ)))
    {v f : (Fin N → ℝ) → ℝ} (hv : ∀ x, x ∉ K₀ → v x = 0)
    (h : HasWeakOperatorValue Xt U J v f) :
    HasWeakOperatorValue Xt V' J v ((U : Set (Fin N → ℝ)).indicator f) := by
  obtain ⟨g, hg, hf⟩ := h
  have hvi := indicator_eq_self_of_zero_off hKU hv
  refine ⟨fun i => (U : Set (Fin N → ℝ)).indicator (g i), fun i => ?_, ?_⟩
  · have := RothschildStein.S.hasWeakWordDeriv_zeroExtension Xt V' U hUV ⟨K₀, hK₀⟩ hKU (J i) v
      (g i) (hg i) (Filter.Eventually.of_forall fun x _ hx => hv x hx)
    rwa [hvi] at this
  · rw [Filter.EventuallyEq, ae_restrict_iff' V'.isOpen.measurableSet]
    have h1 := (ae_restrict_iff' U.isOpen.measurableSet).1 hf
    filter_upwards [h1] with x hx _
    by_cases hxU : x ∈ (U : Set (Fin N → ℝ))
    · simp only [indicator_of_mem hxU, hx hxU]
    · simp only [indicator_of_notMem hxU, Finset.sum_const_zero]

/-- Extension by zero of Sobolev membership: a compactly supported Sobolev function of `U ⊆ V'`
is a Sobolev function of `V'`. -/
theorem memSobolevX_extend {U V' : Opens (Fin N → ℝ)}
    (_hUV : (U : Set (Fin N → ℝ)) ⊆ (V' : Set (Fin N → ℝ))) {kk : ℕ} {P : ℝ≥0∞}
    {v : (Fin N → ℝ) → ℝ} (hv : memSobolevX w Xt U kk P v) (hc : HasCompactSupport v)
    (hs : tsupport v ⊆ (U : Set (Fin N → ℝ))) : memSobolevX w Xt V' kk P v :=
  RothschildStein.S.memSobolevX_restrict w Xt ⊤ V' (fun _ _ => trivial)
    (RothschildStein.H3.memSobolevX_globalize_of_compact_support w Xt U hv hc hs)

end Extension

end RothschildStein.P2
