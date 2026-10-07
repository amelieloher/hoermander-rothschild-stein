-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.SobolevInterpolationFamily
public import RothschildStein.P1.ParametrixKernelBoundsDeriv
public import RothschildStein.P1.ContinuityRegularAssembly

/-!
# Sobolev interpolation, kernel derivative bounds for a type-1 kernel: the jet bounds

For a type-`1` operator `T` of a lifted frame (the operator `F_l` of the representation
`X̃_l v = F_l L̃v + S_l v`) the far part of the Sobolev interpolation inequality needs, away from the pole, the first and second
field derivatives of the kernel in the integration variable `η`, of size `d̃^(1-Q-w_i)` and
`d̃^(1-Q-w_i-w_j)` (the six contributions of BB p. 581), together with the smoothness of `T.kernel ξ`
off the diagonal. `KernelJetBounds C L kk M` records exactly this for a kernel `kk` on a compact
`L ⊆ U`.

* a principal term `a(ξ) b(η) (D^{ξ,η} Γ)(Θ(η, ξ))` of degree `≤ 1` has the jet bounds, by the
  weighted symbol calculus (`principalTerm_wtSym`, `ChartExt.exists_derivative_bounds`);
* a regular remainder (jointly `C²`, compact support) has the jet bounds with bounded jets;
* jet bounds are stable under finite sums and under changes on the diagonal, so every type-1 kernel
  has them (`typeKernel_jetBounds`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set Filter MeasureTheory
open scoped Topology BigOperators ENNReal
namespace RothschildStein.P2

open RothschildStein.P1

section Calculus

variable {N : ℕ}

/-- Additivity of the field derivative at a point of differentiability. -/
theorem fieldDerivative_add_of_differentiableAt {V : (Fin N → ℝ) → (Fin N → ℝ)}
    {f g : (Fin N → ℝ) → ℝ} {x : Fin N → ℝ}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    fieldDerivative V (fun y => f y + g y) x = fieldDerivative V f x + fieldDerivative V g x := by
  unfold fieldDerivative
  rw [fderiv_fun_add hf hg]
  rfl

/-- The field derivative of the zero function vanishes. -/
theorem fieldDerivative_const_zero {V : (Fin N → ℝ) → (Fin N → ℝ)} {x : Fin N → ℝ} :
    fieldDerivative V (fun _ => (0 : ℝ)) x = 0 := by
  simp [fieldDerivative]

/-- A field derivative of a `C²` function along a `C¹` field is `C¹`. -/
theorem contDiffAt_fieldDerivative {V : (Fin N → ℝ) → (Fin N → ℝ)} {f : (Fin N → ℝ) → ℝ}
    {x : Fin N → ℝ} (hf : ContDiffAt ℝ 2 f x) (hV : ContDiffAt ℝ 1 V x) :
    ContDiffAt ℝ 1 (fieldDerivative V f) x :=
  (hf.fderiv_right (m := 1) (by norm_num)).clm_apply hV

/-- Additivity of the iterated field derivative for `C²` functions. -/
theorem fieldDerivative_fieldDerivative_add {V W : (Fin N → ℝ) → (Fin N → ℝ)}
    {f g : (Fin N → ℝ) → ℝ} {x : Fin N → ℝ} (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x)
    (hW : ContDiffAt ℝ 1 W x) :
    fieldDerivative V (fieldDerivative W (fun y => f y + g y)) x =
      fieldDerivative V (fieldDerivative W f) x + fieldDerivative V (fieldDerivative W g) x := by
  have hev : fieldDerivative W (fun y => f y + g y) =ᶠ[𝓝 x]
      fun y => fieldDerivative W f y + fieldDerivative W g y := by
    filter_upwards [hf.eventually (by simp), hg.eventually (by simp)] with y hfy hgy
    exact fieldDerivative_add_of_differentiableAt (hfy.differentiableAt (by norm_num))
      (hgy.differentiableAt (by norm_num))
  rw [fieldDerivative_congr_eventually hev]
  exact fieldDerivative_add_of_differentiableAt
    ((contDiffAt_fieldDerivative hf hW).differentiableAt (by norm_num))
    ((contDiffAt_fieldDerivative hg hW).differentiableAt (by norm_num))

/-- The field derivative of a slice `η ↦ f(ξ, η)` of a function on a product is the
derivative of `f` in the direction `(0, V η)`. -/
theorem fieldDerivative_slice {V : (Fin N → ℝ) → (Fin N → ℝ)}
    {f : (Fin N → ℝ) × (Fin N → ℝ) → ℝ} {ξ η : Fin N → ℝ}
    (hf : DifferentiableAt ℝ f (ξ, η)) :
    fieldDerivative V (fun η' => f (ξ, η')) η = fderiv ℝ f (ξ, η) (0, V η) := by
  have h : HasFDerivAt (fun η' => f (ξ, η'))
      ((fderiv ℝ f (ξ, η)).comp (ContinuousLinearMap.inr ℝ (Fin N → ℝ) (Fin N → ℝ))) η :=
    hf.hasFDerivAt.comp η (hasFDerivAt_prodMk_right ξ η)
  unfold fieldDerivative
  rw [h.fderiv]
  rfl

/-- Integer powers: `x^a ≤ D^(a-b) x^b` for `0 < x ≤ D` and `b ≤ a`. -/
theorem zpow_le_mul_zpow_of_le {x D : ℝ} (hx : 0 < x) (hxD : x ≤ D) {a b : ℤ} (hba : b ≤ a) :
    x ^ a ≤ D ^ (a - b) * x ^ b := by
  have h1 : x ^ a = x ^ (a - b) * x ^ b := by
    rw [← zpow_add₀ hx.ne']
    congr 1
    ring
  rw [h1]
  exact mul_le_mul_of_nonneg_right (kzpow_le_of_nonneg hx hxD (sub_nonneg.2 hba))
    (zpow_pos hx _).le

end Calculus

section Jets

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {F : KernelFrame (n + m)}

/-- The lifted fields are `C¹` at every point of the chart domain. -/
theorem contDiffAt_Xl {η : Fin (n + m) → ℝ} (hη : η ∈ C.U) (i : Fin k) :
    ContDiffAt ℝ 1 (C.Xl i) η :=
  ((C.contDiffOn_Xl_U i).contDiffAt (C.isOpen_U.mem_nhds hη)).of_le (by simp)

variable (C) in
/-- **Jet bounds of a kernel on a compact set** `L ⊆ U`: for `ξ ≠ η`
in `L` the function `η' ↦ kk ξ η'` is `C²` at `η`, and, with `d̃ = d̃(ξ, η)`, `|kk ξ η| ≤ M d̃^(1-Q)`,
`|X̃_i kk ξ (η)| ≤ M d̃^(1-Q-w_i)` and `|X̃_j X̃_i kk ξ (η)| ≤ M d̃^(1-Q-w_i-w_j)`
(the sizes of the six contributions of BB p. 581, in the input variable). -/
def KernelJetBounds (L : Set (Fin (n + m) → ℝ))
    (kk : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ) (M : ℝ) : Prop :=
  0 ≤ M ∧ ∀ ξ ∈ L, ∀ η ∈ L, ξ ≠ η →
    ContDiffAt ℝ 2 (kk ξ) η ∧
    |kk ξ η| ≤ M * (C.dl ξ η).toReal ^ ((1 : ℤ) - (C.G.homogeneousDimension : ℤ)) ∧
    (∀ i : Fin k, |fieldDerivative (C.Xl i) (kk ξ) η| ≤
      M * (C.dl ξ η).toReal ^ ((1 : ℤ) - (C.G.homogeneousDimension : ℤ) - ((w i : ℕ) : ℤ))) ∧
    (∀ i j : Fin k, |fieldDerivative (C.Xl j) (fieldDerivative (C.Xl i) (kk ξ)) η| ≤
      M * (C.dl ξ η).toReal ^ ((1 : ℤ) - (C.G.homogeneousDimension : ℤ) - ((w i : ℕ) : ℤ) -
        ((w j : ℕ) : ℤ)))

variable {L : Set (Fin (n + m) → ℝ)} {kk kk₁ kk₂ : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ}
  {M M₁ M₂ : ℝ}

/-- The zero kernel has the jet bounds with constant `0`. -/
theorem KernelJetBounds.zero : KernelJetBounds C L (fun _ _ => 0) 0 := by
  have h0 : ∀ i : Fin k, fieldDerivative (C.Xl i) (fun _ : Fin (n + m) → ℝ => (0 : ℝ)) =
      fun _ => 0 := fun i => funext fun x => fieldDerivative_const_zero
  refine ⟨le_rfl, fun ξ _ η _ _ => ⟨contDiffAt_const, by simp, fun i => ?_, fun i j => ?_⟩⟩
  · simp [fieldDerivative_const_zero]
  · show |fieldDerivative (C.Xl j) (fieldDerivative (C.Xl i) (fun _ : Fin (n + m) → ℝ => (0 : ℝ))) η| ≤ _
    rw [h0 i, fieldDerivative_const_zero]
    simp

/-- Jet bounds are stable under sums. -/
theorem KernelJetBounds.add (hLU : L ⊆ C.U) (h₁ : KernelJetBounds C L kk₁ M₁)
    (h₂ : KernelJetBounds C L kk₂ M₂) :
    KernelJetBounds C L (fun ξ η => kk₁ ξ η + kk₂ ξ η) (M₁ + M₂) := by
  refine ⟨add_nonneg h₁.1 h₂.1, fun ξ hξ η hη hne => ?_⟩
  obtain ⟨a1, a2, a3, a4⟩ := h₁.2 ξ hξ η hη hne
  obtain ⟨b1, b2, b3, b4⟩ := h₂.2 ξ hξ η hη hne
  have hX : ∀ i, ContDiffAt ℝ 1 (C.Xl i) η := fun i => contDiffAt_Xl (hLU hη) i
  refine ⟨a1.add b1, ?_, fun i => ?_, fun i j => ?_⟩
  · calc |kk₁ ξ η + kk₂ ξ η| ≤ |kk₁ ξ η| + |kk₂ ξ η| := abs_add_le _ _
      _ ≤ _ := add_le_add a2 b2
      _ = _ := by ring
  · have e : fieldDerivative (C.Xl i) (fun η' => kk₁ ξ η' + kk₂ ξ η') η =
        fieldDerivative (C.Xl i) (kk₁ ξ) η + fieldDerivative (C.Xl i) (kk₂ ξ) η :=
      fieldDerivative_add_of_differentiableAt (a1.differentiableAt (by norm_num))
        (b1.differentiableAt (by norm_num))
    show |fieldDerivative (C.Xl i) (fun η' => kk₁ ξ η' + kk₂ ξ η') η| ≤ _
    rw [e]
    calc _ ≤ |fieldDerivative (C.Xl i) (kk₁ ξ) η| + |fieldDerivative (C.Xl i) (kk₂ ξ) η| :=
          abs_add_le _ _
      _ ≤ _ := add_le_add (a3 i) (b3 i)
      _ = _ := by ring
  · have e := fieldDerivative_fieldDerivative_add (V := C.Xl j) a1 b1 (hX i)
    show |fieldDerivative (C.Xl j) (fieldDerivative (C.Xl i) (fun η' => kk₁ ξ η' + kk₂ ξ η')) η| ≤ _
    rw [e]
    calc _ ≤ |fieldDerivative (C.Xl j) (fieldDerivative (C.Xl i) (kk₁ ξ)) η| +
          |fieldDerivative (C.Xl j) (fieldDerivative (C.Xl i) (kk₂ ξ)) η| := abs_add_le _ _
      _ ≤ _ := add_le_add (a4 i j) (b4 i j)
      _ = _ := by ring

/-- Jet bounds only see the off-diagonal values of the kernel. -/
theorem KernelJetBounds.congr (h : KernelJetBounds C L kk M)
    (he : ∀ ξ η, ξ ≠ η → kk₂ ξ η = kk ξ η) : KernelJetBounds C L kk₂ M := by
  refine ⟨h.1, fun ξ hξ η hη hne => ?_⟩
  obtain ⟨a1, a2, a3, a4⟩ := h.2 ξ hξ η hη hne
  have hev : kk₂ ξ =ᶠ[𝓝 η] kk ξ := by
    filter_upwards [isOpen_ne.mem_nhds (show η ∈ {y : Fin (n + m) → ℝ | y ≠ ξ} from hne.symm)]
      with y hy using he ξ y (Ne.symm hy)
  refine ⟨a1.congr_of_eventuallyEq hev, ?_, fun i => ?_, fun i j => ?_⟩
  · rw [he ξ η hne]
    exact a2
  · rw [fieldDerivative_congr_eventually hev]
    exact a3 i
  · rw [fieldDerivative_fieldDerivative_congr_eventually hev]
    exact a4 i j

/-- A finite sum of kernels with jet bounds has jet bounds. -/
theorem KernelJetBounds.list_sum_of_exists {ι : Type*} (hLU : L ⊆ C.U) (l : List ι)
    {κ : ι → (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ}
    (h : ∀ i ∈ l, ∃ M, KernelJetBounds C L (κ i) M) :
    ∃ M, KernelJetBounds C L (fun ξ η => (l.map (fun i => κ i ξ η)).sum) M := by
  induction l with
  | nil => exact ⟨0, by simpa using (KernelJetBounds.zero (C := C) (L := L))⟩
  | cons a l ih =>
    obtain ⟨M₁, h₁⟩ := h a List.mem_cons_self
    obtain ⟨M₂, h₂⟩ := ih (fun i hi => h i (List.mem_cons_of_mem _ hi))
    exact ⟨M₁ + M₂, by simpa only [List.map_cons, List.sum_cons] using h₁.add hLU h₂⟩

variable (hL : IsCompact L) (hLU : L ⊆ C.U)
include hL hLU

/-- On a compact `L ⊆ U` a constant is dominated by a multiple of `d̃^p`, `p ≤ 0`. -/
theorem exists_one_le_mul_dl_zpow {p : ℤ} (hp : p ≤ 0) :
    ∃ K : ℝ, 0 < K ∧ ∀ ξ ∈ L, ∀ η ∈ L, ξ ≠ η → 1 ≤ K * (C.dl ξ η).toReal ^ p := by
  obtain ⟨D₀, hD₀, hD⟩ := LiftedChart.exists_dl_bound (C := C) hL hLU
  refine ⟨D₀ ^ (-p), zpow_pos hD₀ _, fun ξ hξ η hη hne => ?_⟩
  have hpos := C.dl_toReal_pos (hLU hξ) (hLU hη) hne.symm
  have h1 : D₀ ^ p ≤ (C.dl ξ η).toReal ^ p := kzpow_le_of_nonpos hpos (hD ξ hξ η hη) hp
  calc (1 : ℝ) = D₀ ^ (-p) * D₀ ^ p := by
        rw [← zpow_add₀ hD₀.ne']
        simp
    _ ≤ D₀ ^ (-p) * (C.dl ξ η).toReal ^ p :=
        mul_le_mul_of_nonneg_left h1 (zpow_pos hD₀ _).le

/-- **The regular remainder has the jet bounds**: a jointly `C²` kernel has bounded jets on
the compact set `L × L`, and `d̃^p ≥ D^p` is bounded below for `p ≤ 0`. -/
theorem regular_jetBounds {r : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ) → ℝ}
    (hr : ContDiff ℝ 2 (fun z : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) => r z.1 z.2)) :
    ∃ M, KernelJetBounds C L r M := by
  set R2 : (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) → ℝ := fun z => r z.1 z.2 with hR2
  have hdiff : ∀ p, DifferentiableAt ℝ R2 p := fun p => hr.differentiable (by norm_num) p
  have hS : IsOpen ((univ : Set (Fin (n + m) → ℝ)) ×ˢ C.U) := isOpen_univ.prod C.isOpen_U
  have hLL : L ×ˢ L ⊆ (univ : Set (Fin (n + m) → ℝ)) ×ˢ C.U := fun p hp => ⟨trivial, hLU hp.2⟩
  -- the first jets as functions on the product
  set g₁ : Fin k → (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) → ℝ :=
    fun i p => fderiv ℝ R2 p (0, C.Xl i p.2) with hg₁
  have hfd : ContDiff ℝ 1 (fderiv ℝ R2) := hr.fderiv_right (m := 1) (by norm_num)
  have hg₁at : ∀ i, ∀ p ∈ (univ : Set (Fin (n + m) → ℝ)) ×ˢ C.U, ContDiffAt ℝ 1 (g₁ i) p := by
    intro i p hp
    refine hfd.contDiffAt.clm_apply (contDiffAt_const.prodMk ?_)
    exact (contDiffAt_Xl hp.2 i).comp p (contDiff_snd.contDiffAt)
  have hg₁on : ∀ i, ContDiffOn ℝ 1 (g₁ i) ((univ : Set (Fin (n + m) → ℝ)) ×ˢ C.U) :=
    fun i p hp => (hg₁at i p hp).contDiffWithinAt
  set g₂ : Fin k → Fin k → (Fin (n + m) → ℝ) × (Fin (n + m) → ℝ) → ℝ :=
    fun i j p => fderiv ℝ (g₁ i) p (0, C.Xl j p.2) with hg₂
  have hg₂cont : ∀ i j, ContinuousOn (g₂ i j) ((univ : Set (Fin (n + m) → ℝ)) ×ˢ C.U) := by
    intro i j
    refine ((hg₁on i).continuousOn_fderiv_of_isOpen hS le_rfl).clm_apply ?_
    exact continuousOn_const.prodMk (((C.contDiffOn_Xl_U j).continuousOn).comp continuousOn_snd
      (fun p hp => hp.2))
  have hg₀cont : ContinuousOn R2 ((univ : Set (Fin (n + m) → ℝ)) ×ˢ C.U) :=
    hr.continuous.continuousOn
  have hg₁cont : ∀ i, ContinuousOn (g₁ i) ((univ : Set (Fin (n + m) → ℝ)) ×ˢ C.U) :=
    fun i => (hg₁on i).continuousOn
  have hLc : IsCompact (L ×ˢ L) := hL.prod hL
  obtain ⟨B₀, hB₀⟩ := hLc.exists_bound_of_continuousOn (hg₀cont.mono hLL)
  choose B₁ hB₁ using fun i => hLc.exists_bound_of_continuousOn ((hg₁cont i).mono hLL)
  choose B₂ hB₂ using fun i j => hLc.exists_bound_of_continuousOn ((hg₂cont i j).mono hLL)
  -- the lower bounds of the distance powers
  obtain ⟨K₀, hK₀, hK₀'⟩ := exists_one_le_mul_dl_zpow hL hLU
    (p := (1 : ℤ) - (C.G.homogeneousDimension : ℤ)) (by
      have := G2.homogeneousDimension_pos C.G
      omega)
  choose K₁ hK₁ hK₁' using fun i : Fin k => exists_one_le_mul_dl_zpow hL hLU
    (p := (1 : ℤ) - (C.G.homogeneousDimension : ℤ) - ((w i : ℕ) : ℤ)) (by
      have := G2.homogeneousDimension_pos C.G
      have := (w i).pos
      omega)
  choose K₂ hK₂ hK₂' using fun i j : Fin k => exists_one_le_mul_dl_zpow hL hLU
    (p := (1 : ℤ) - (C.G.homogeneousDimension : ℤ) - ((w i : ℕ) : ℤ) - ((w j : ℕ) : ℤ)) (by
      have := G2.homogeneousDimension_pos C.G
      have := (w i).pos
      have := (w j).pos
      omega)
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ℝ, c₀ = max B₀ 0 * K₀ := ⟨_, rfl⟩
  obtain ⟨c₁, hc₁⟩ : ∃ c₁ : Fin k → ℝ, ∀ i, c₁ i = max (B₁ i) 0 * K₁ i := ⟨_, fun _ => rfl⟩
  obtain ⟨c₂, hc₂⟩ : ∃ c₂ : Fin k → Fin k → ℝ, ∀ i j, c₂ i j = max (B₂ i j) 0 * K₂ i j :=
    ⟨_, fun _ _ => rfl⟩
  have hc₀0 : 0 ≤ c₀ := by rw [hc₀]; exact mul_nonneg (le_max_right _ _) hK₀.le
  have hc₁0 : ∀ i, 0 ≤ c₁ i := fun i => by
    rw [hc₁ i]; exact mul_nonneg (le_max_right _ _) (hK₁ i).le
  have hc₂0 : ∀ i j, 0 ≤ c₂ i j := fun i j => by
    rw [hc₂ i j]; exact mul_nonneg (le_max_right _ _) (hK₂ i j).le
  have hsum₁ : ∀ i, c₁ i ≤ ∑ i, c₁ i :=
    fun i => Finset.single_le_sum (f := c₁) (fun i' _ => hc₁0 i') (Finset.mem_univ i)
  have hsum₂ : ∀ i j, c₂ i j ≤ ∑ i, ∑ j, c₂ i j := by
    intro i j
    have h1 : c₂ i j ≤ ∑ j', c₂ i j' :=
      Finset.single_le_sum (f := fun j' => c₂ i j') (fun j' _ => hc₂0 i j') (Finset.mem_univ j)
    have h3 : ∑ j', c₂ i j' ≤ ∑ i', ∑ j', c₂ i' j' :=
      Finset.single_le_sum (f := fun i' => ∑ j', c₂ i' j')
        (fun i' _ => Finset.sum_nonneg fun j' _ => hc₂0 i' j') (Finset.mem_univ i)
    exact h1.trans h3
  have h₁nn : 0 ≤ ∑ i, c₁ i := Finset.sum_nonneg fun i _ => hc₁0 i
  have h₂nn : 0 ≤ ∑ i, ∑ j, c₂ i j :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hc₂0 i j
  refine ⟨c₀ + ∑ i, c₁ i + ∑ i, ∑ j, c₂ i j, ?_, fun ξ hξ η hη hne => ?_⟩
  · exact add_nonneg (add_nonneg hc₀0 h₁nn) h₂nn
  have hηU : η ∈ C.U := hLU hη
  have hmem : (ξ, η) ∈ L ×ˢ L := ⟨hξ, hη⟩
  have hpos := C.dl_toReal_pos (hLU hξ) (hLU hη) hne.symm
  have hslice : ContDiffAt ℝ 2 (r ξ) η :=
    (hr.comp (contDiff_const.prodMk contDiff_id)).contDiffAt
  -- identification of the jets
  have hjet1 : ∀ i, ∀ η' : Fin (n + m) → ℝ,
      fieldDerivative (C.Xl i) (r ξ) η' = g₁ i (ξ, η') := fun i η' =>
    fieldDerivative_slice (hdiff (ξ, η'))
  have hfun1 : ∀ i, fieldDerivative (C.Xl i) (r ξ) = fun η' => g₁ i (ξ, η') :=
    fun i => funext (hjet1 i)
  have hjet2 : ∀ i j, fieldDerivative (C.Xl j) (fieldDerivative (C.Xl i) (r ξ)) η =
      g₂ i j (ξ, η) := by
    intro i j
    rw [hfun1 i]
    exact fieldDerivative_slice (((hg₁at i (ξ, η) ⟨trivial, hηU⟩)).differentiableAt (by norm_num))
  refine ⟨hslice, ?_, fun i => ?_, fun i j => ?_⟩
  · have h1 := hB₀ (ξ, η) hmem
    have h2 := hK₀' ξ hξ η hη hne
    have h3 : |r ξ η| ≤ max B₀ 0 := by
      have : |R2 (ξ, η)| ≤ B₀ := by simpa [Real.norm_eq_abs] using h1
      exact this.trans (le_max_left _ _)
    have hP : 0 < (C.dl ξ η).toReal ^ ((1 : ℤ) - (C.G.homogeneousDimension : ℤ)) :=
      zpow_pos hpos _
    calc |r ξ η| ≤ max B₀ 0 * 1 := by rw [mul_one]; exact h3
      _ ≤ max B₀ 0 * (K₀ * (C.dl ξ η).toReal ^ ((1 : ℤ) - (C.G.homogeneousDimension : ℤ))) :=
          mul_le_mul_of_nonneg_left h2 (le_max_right _ _)
      _ = c₀ * (C.dl ξ η).toReal ^ ((1 : ℤ) - (C.G.homogeneousDimension : ℤ)) := by
          rw [hc₀]; ring
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_right ?_ hP.le
          have : 0 ≤ ∑ i, c₁ i + ∑ i, ∑ j, c₂ i j := add_nonneg h₁nn h₂nn
          linarith
  · rw [hjet1 i]
    have h1 := hB₁ i (ξ, η) hmem
    have h2 := hK₁' i ξ hξ η hη hne
    have h3 : |g₁ i (ξ, η)| ≤ max (B₁ i) 0 := by
      have : |g₁ i (ξ, η)| ≤ B₁ i := by simpa [Real.norm_eq_abs] using h1
      exact this.trans (le_max_left _ _)
    have hP : 0 < (C.dl ξ η).toReal ^ ((1 : ℤ) - (C.G.homogeneousDimension : ℤ) - ((w i : ℕ) : ℤ)) :=
      zpow_pos hpos _
    calc |g₁ i (ξ, η)| ≤ max (B₁ i) 0 * 1 := by rw [mul_one]; exact h3
      _ ≤ max (B₁ i) 0 * (K₁ i * (C.dl ξ η).toReal ^
            ((1 : ℤ) - (C.G.homogeneousDimension : ℤ) - ((w i : ℕ) : ℤ))) :=
          mul_le_mul_of_nonneg_left h2 (le_max_right _ _)
      _ = c₁ i * (C.dl ξ η).toReal ^
            ((1 : ℤ) - (C.G.homogeneousDimension : ℤ) - ((w i : ℕ) : ℤ)) := by
          rw [hc₁ i]; ring
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_right ?_ hP.le
          have := hsum₁ i
          have : 0 ≤ ∑ i, ∑ j, c₂ i j := h₂nn
          linarith
  · rw [hjet2 i j]
    have h1 := hB₂ i j (ξ, η) hmem
    have h2 := hK₂' i j ξ hξ η hη hne
    have h3 : |g₂ i j (ξ, η)| ≤ max (B₂ i j) 0 := by
      have : |g₂ i j (ξ, η)| ≤ B₂ i j := by simpa [Real.norm_eq_abs] using h1
      exact this.trans (le_max_left _ _)
    have hP : 0 < (C.dl ξ η).toReal ^ ((1 : ℤ) - (C.G.homogeneousDimension : ℤ) -
        ((w i : ℕ) : ℤ) - ((w j : ℕ) : ℤ)) := zpow_pos hpos _
    calc |g₂ i j (ξ, η)| ≤ max (B₂ i j) 0 * 1 := by rw [mul_one]; exact h3
      _ ≤ max (B₂ i j) 0 * (K₂ i j * (C.dl ξ η).toReal ^
            ((1 : ℤ) - (C.G.homogeneousDimension : ℤ) - ((w i : ℕ) : ℤ) - ((w j : ℕ) : ℤ))) :=
          mul_le_mul_of_nonneg_left h2 (le_max_right _ _)
      _ = c₂ i j * (C.dl ξ η).toReal ^
            ((1 : ℤ) - (C.G.homogeneousDimension : ℤ) - ((w i : ℕ) : ℤ) - ((w j : ℕ) : ℤ)) := by
          rw [hc₂ i j]; ring
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_right ?_ hP.le
          have := hsum₂ i j
          have : 0 ≤ ∑ i, c₁ i := h₁nn
          linarith

omit hL hLU in
/-- A principal term of degree `≤ 1` has `C^∞` kernel off the diagonal in `η`. -/
theorem principalTerm_contDiffOn_input (hF : C.IsLiftedFrame F) (t : PrincipalTerm F)
    {ξ : Fin (n + m) → ℝ} (hξ : ξ ∈ C.U) :
    ContDiffOn ℝ (⊤ : ℕ∞) (t.kernel ξ) (C.U \ {ξ}) := by
  have hA : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun z : KZ (n + m) =>
        t.a z.1 * t.b z.2.1 * (t.D z.1 z.2.1).apply (F.pole t.star) z.2.2) {z | z.2.2 ≠ 0} :=
    (principalTerm_wtSym hF t (L := ∅) isCompact_empty 1 0).contDiffOn
  have hθ : ContDiffOn ℝ (⊤ : ℕ∞) (fun η' => C.Θ η' ξ) C.U :=
    C.theta_smooth.comp (contDiffOn_id.prodMk contDiffOn_const) (fun η' hη' => ⟨hη', hξ⟩)
  have hf : ContDiffOn ℝ (⊤ : ℕ∞) (fun η' => ((ξ, η', C.Θ η' ξ) : KZ (n + m))) (C.U \ {ξ}) :=
    (contDiffOn_const.prodMk (contDiffOn_id.prodMk hθ)).mono Set.sdiff_subset
  have hc := hA.comp hf (fun η' hη' => by
    show C.Θ η' ξ ≠ 0
    exact (C.theta_eq_zero_iff hη'.1 hξ).not.mpr (fun h => hη'.2 h.symm))
  refine hc.congr (fun η' _ => ?_)
  simp only [Function.comp, PrincipalTerm.kernel, hF.Θ_eq]

/-- **A principal term of degree `≤ 1` has the jet bounds**: the
derivative bounds of the symbol class (`ChartExt.exists_derivative_bounds`) for the family
`a(ξ) b(η) (D^{ξ,η} Γ)(u)` of degree `d = 2 - deg D - Q ≥ 1 - Q`, with the exponents lowered to
`1 - Q - …` on the bounded set `L`. -/
theorem principalTerm_jetBounds (hF : C.IsLiftedFrame F) (t : PrincipalTerm F)
    (hdeg : t.degree ≤ 1) : ∃ M, KernelJetBounds C L t.kernel M := by
  obtain ⟨ex⟩ := C.exists_chartExt hL hLU
  obtain ⟨D₀, hD₀, hD⟩ := LiftedChart.exists_dl_bound (C := C) hL hLU
  obtain ⟨M₁, hM₁0, hM₁⟩ := ex.exists_derivative_bounds hL hLU
    (d := 2 - t.degree - (C.G.homogeneousDimension : ℤ))
    (A := fun z : KZ (n + m) =>
      t.a z.1 * t.b z.2.1 * (t.D z.1 z.2.1).apply (F.pole t.star) z.2.2)
    (fun R _ => principalTerm_wtSym hF t hL R 2)
  obtain ⟨A₀, S₀, hA₀, hS₀, hsz, -⟩ := PrincipalTerm.hasKernelBounds hF t hdeg hL hLU
  set e : ℤ := 1 - t.degree with he
  have he0 : 0 ≤ e := by omega
  refine ⟨A₀ + M₁ * D₀ ^ e, add_nonneg hA₀ (mul_nonneg hM₁0 (zpow_pos hD₀ _).le),
    fun ξ hξ η hη hne => ?_⟩
  have hpos := C.dl_toReal_pos (hLU hξ) (hLU hη) hne.symm
  have hDe : 0 ≤ D₀ ^ e := (zpow_pos hD₀ _).le
  have hdl := hD ξ hξ η hη
  have hker : (fun η' => t.a ξ * t.b η' * (t.D ξ η').apply (F.pole t.star) (C.Θ η' ξ)) =
      t.kernel ξ := by
    funext η'
    simp only [PrincipalTerm.kernel, hF.Θ_eq]
  have hc2 : ContDiffAt ℝ 2 (t.kernel ξ) η := by
    have h := (principalTerm_contDiffOn_input hF t (hLU hξ)).contDiffAt
      ((C.isOpen_U.sdiff isClosed_singleton).mem_nhds ⟨hLU hη, fun h => hne h.symm⟩)
    exact h.of_le (by simp)
  refine ⟨hc2, ?_, fun i => ?_, fun i j => ?_⟩
  · have h := hsz ξ hξ η hη hne
    have hP : 0 < (C.dl ξ η).toReal ^ ((1 : ℤ) - (C.G.homogeneousDimension : ℤ)) := zpow_pos hpos _
    have h' : |t.kernel ξ η| ≤ A₀ * (C.dl ξ η).toReal ^ ((1 : ℤ) - (C.G.homogeneousDimension : ℤ)) := by
      simpa only [Nat.cast_one] using h
    refine h'.trans (mul_le_mul_of_nonneg_right ?_ hP.le)
    have : 0 ≤ M₁ * D₀ ^ e := mul_nonneg hM₁0 hDe
    linarith
  · obtain ⟨-, ⟨c1, -⟩⟩ := hM₁ ξ hξ η hη hne i i
    have c1' : |fieldDerivative (C.Xl i) (t.kernel ξ) η| ≤
        M₁ * (C.dl ξ η).toReal ^ (2 - t.degree - (C.G.homogeneousDimension : ℤ) - ((w i : ℕ) : ℤ)) := by
      rw [← hker]
      exact c1
    have hP : 0 < (C.dl ξ η).toReal ^ ((1 : ℤ) - (C.G.homogeneousDimension : ℤ) - ((w i : ℕ) : ℤ)) :=
      zpow_pos hpos _
    have hle := zpow_le_mul_zpow_of_le hpos hdl
      (a := 2 - t.degree - (C.G.homogeneousDimension : ℤ) - ((w i : ℕ) : ℤ))
      (b := (1 : ℤ) - (C.G.homogeneousDimension : ℤ) - ((w i : ℕ) : ℤ)) (by omega)
    have hexp : (2 - t.degree - (C.G.homogeneousDimension : ℤ) - ((w i : ℕ) : ℤ)) -
        ((1 : ℤ) - (C.G.homogeneousDimension : ℤ) - ((w i : ℕ) : ℤ)) = e := by rw [he]; ring
    rw [hexp] at hle
    calc |fieldDerivative (C.Xl i) (t.kernel ξ) η|
        ≤ M₁ * (C.dl ξ η).toReal ^ (2 - t.degree - (C.G.homogeneousDimension : ℤ) - ((w i : ℕ) : ℤ)) := c1'
      _ ≤ M₁ * (D₀ ^ e * (C.dl ξ η).toReal ^
            ((1 : ℤ) - (C.G.homogeneousDimension : ℤ) - ((w i : ℕ) : ℤ))) :=
          mul_le_mul_of_nonneg_left hle hM₁0
      _ = (M₁ * D₀ ^ e) * (C.dl ξ η).toReal ^
            ((1 : ℤ) - (C.G.homogeneousDimension : ℤ) - ((w i : ℕ) : ℤ)) := by ring
      _ ≤ (A₀ + M₁ * D₀ ^ e) * (C.dl ξ η).toReal ^
            ((1 : ℤ) - (C.G.homogeneousDimension : ℤ) - ((w i : ℕ) : ℤ)) :=
          mul_le_mul_of_nonneg_right (by linarith) hP.le
  · obtain ⟨-, ⟨-, c2⟩⟩ := hM₁ ξ hξ η hη hne i j
    have c2' : |fieldDerivative (C.Xl j) (fieldDerivative (C.Xl i) (t.kernel ξ)) η| ≤
        M₁ * (C.dl ξ η).toReal ^ (2 - t.degree - (C.G.homogeneousDimension : ℤ) -
          ((w i : ℕ) : ℤ) - ((w j : ℕ) : ℤ)) := by
      rw [← hker]
      exact c2
    have hP : 0 < (C.dl ξ η).toReal ^ ((1 : ℤ) - (C.G.homogeneousDimension : ℤ) -
        ((w i : ℕ) : ℤ) - ((w j : ℕ) : ℤ)) := zpow_pos hpos _
    have hle := zpow_le_mul_zpow_of_le hpos hdl
      (a := 2 - t.degree - (C.G.homogeneousDimension : ℤ) - ((w i : ℕ) : ℤ) - ((w j : ℕ) : ℤ))
      (b := (1 : ℤ) - (C.G.homogeneousDimension : ℤ) - ((w i : ℕ) : ℤ) - ((w j : ℕ) : ℤ))
      (by omega)
    have hexp : (2 - t.degree - (C.G.homogeneousDimension : ℤ) - ((w i : ℕ) : ℤ) -
        ((w j : ℕ) : ℤ)) - ((1 : ℤ) - (C.G.homogeneousDimension : ℤ) - ((w i : ℕ) : ℤ) -
        ((w j : ℕ) : ℤ)) = e := by rw [he]; ring
    rw [hexp] at hle
    calc |fieldDerivative (C.Xl j) (fieldDerivative (C.Xl i) (t.kernel ξ)) η|
        ≤ M₁ * (C.dl ξ η).toReal ^ (2 - t.degree - (C.G.homogeneousDimension : ℤ) -
            ((w i : ℕ) : ℤ) - ((w j : ℕ) : ℤ)) := c2'
      _ ≤ M₁ * (D₀ ^ e * (C.dl ξ η).toReal ^ ((1 : ℤ) - (C.G.homogeneousDimension : ℤ) -
            ((w i : ℕ) : ℤ) - ((w j : ℕ) : ℤ))) :=
          mul_le_mul_of_nonneg_left hle hM₁0
      _ = (M₁ * D₀ ^ e) * (C.dl ξ η).toReal ^ ((1 : ℤ) - (C.G.homogeneousDimension : ℤ) -
            ((w i : ℕ) : ℤ) - ((w j : ℕ) : ℤ)) := by ring
      _ ≤ (A₀ + M₁ * D₀ ^ e) * (C.dl ξ η).toReal ^ ((1 : ℤ) - (C.G.homogeneousDimension : ℤ) -
            ((w i : ℕ) : ℤ) - ((w j : ℕ) : ℤ)) :=
          mul_le_mul_of_nonneg_right (by linarith) hP.le

end Jets

section TypeOne

variable {n k : ℕ} {w : Fin k → ℕ+} {s : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin k → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ} {m : ℕ}
  {C : LiftedChart w s Ω hΩ X x₀ m} {F : KernelFrame (n + m)}

/-- **Every type-`1` kernel of a lifted frame has the jet bounds on
`cl V`** (the first and second field derivatives in the input variable away from the pole have sizes
`d̃^(1-Q-w_i)` and `d̃^(1-Q-w_i-w_j)`): a type decomposition of budget `2` is a finite sum of
principal terms of degree `≤ 1` and a jointly `C²` regular remainder, and the kernel agrees with it
off the diagonal. -/
theorem typeKernel_jetBounds (hF : C.IsLiftedFrame F) (T : TypeOperator F 1) :
    ∃ M, KernelJetBounds C (closure (F.V : Set (Fin (n + m) → ℝ))) T.kernel M := by
  obtain ⟨d⟩ := T.isType 2
  have hL := hF.isCompact_closure
  have hLU := hF.closure_subset
  obtain ⟨M₁, h₁⟩ := KernelJetBounds.list_sum_of_exists hLU d.principal
    (κ := fun t => t.kernel) (fun t ht =>
      principalTerm_jetBounds hL hLU hF t (by have := d.principal_degree t ht; omega))
  obtain ⟨M₂, h₂⟩ := regular_jetBounds hL hLU
    (r := d.regular) (by simpa using d.regular_isRegular.1)
  exact ⟨M₁ + M₂, (h₁.add hLU h₂).congr (fun ξ η hne => d.eq_off_diagonal ξ η hne)⟩

end TypeOne

end RothschildStein.P2
