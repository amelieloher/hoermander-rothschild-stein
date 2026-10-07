-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.BaseHolderCutoffData
public import RothschildStein.P2.BaseHolderCompact

/-!
# Applying the compact Hölder estimate to cutoff products

Part of the base Hölder estimate (BB p. 601, (11.92)). Let `ζ` be a cutoff of the radial cutoff construction with
`ζ = 1` on `U_t`, `tsupport ζ ⊆ U_m ⊆ U_s ⊆ F.V` and `a = 1` on `U_s`, at the scale `a = 1/A`, and `u` a
function with Hölder weak jet `D` on `F.V`. The compact `C^{2,α}` estimate
is applied to `v = ζ u` (`cutoff_estimate`), whose Leibniz jet is
`prodJet` (`BaseHolderProduct`). With `L̃ (ζ u) = ζ L̃u + 2 ∑ᵢ X̃ᵢζ X̃ᵢu + u L̃ζ`:

* `ζ L̃u` and `X̃ᵢζ X̃ᵢu` are bounded by the Hölder product estimate after zero extension (first exit):
  `‖ζ L̃u‖_{C^α} ≤ C_b A ‖L̃u‖_{C^α(U_m)}`, `‖X̃ᵢζ X̃ᵢu‖_{C^α} ≤ C_b A² ‖X̃ᵢu‖_{C^α(U_m)}`;
* `u L̃ζ` is again a compactly supported `C^{2,α}` function and its Hölder norm is controlled by sup norms
  (`HolderFromSup`, the parametrix identity `v = P₂ L̃v + F₂ v` and the first Hölder interpolation inequality):
  `‖u L̃ζ‖_{C^α} ≤ C₃ (‖L̃ (u L̃ζ)‖_∞ + ‖u L̃ζ‖_∞)`, with sup bounds from `|L̃ζ| ≤ C_b A²`,
  `|X̃ₗ L̃ζ| ≤ C_b A³`, `|L̃L̃ζ| ≤ C_b A⁴`.

The result `cutoff_estimate`: `‖u‖_{C^{2,α}(U_t)} ≤ c (‖L̃u‖_{C^α(U_s)} + ‖Du‖_{C^α(U_m)} + ‖u‖_{L^∞(U_s)})`
with `c = c(Λ, C₃, C_b, A)` an explicit polynomial in `A`. (BB bound the corresponding lower-order terms by
the product absorption with a flow time, and absorb `ε ψ(s)`; here the sup-norm form of the compact estimate
makes `ψ(s)` unnecessary: see `BaseHolderLifted`.)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped ENNReal Topology BigOperators
namespace RothschildStein.P2

open RothschildStein.P1

section Arith

theorem ofReal_abs_mul_le_of_le {x y : ℝ} {B1 B2 : ℝ≥0∞} (hx : ENNReal.ofReal |x| ≤ B1)
    (hy : ENNReal.ofReal |y| ≤ B2) : ENNReal.ofReal |x * y| ≤ B1 * B2 := by
  rw [abs_mul, ENNReal.ofReal_mul (abs_nonneg _)]
  exact mul_le_mul' hx hy

theorem ofReal_abs_add_le_add (x y : ℝ) :
    ENNReal.ofReal |x + y| ≤ ENNReal.ofReal |x| + ENNReal.ofReal |y| := by
  rw [← ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (abs_add_le _ _)

theorem ofReal_abs_finset_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℝ) {g : ι → ℝ≥0∞}
    (h : ∀ i ∈ s, ENNReal.ofReal |f i| ≤ g i) :
    ENNReal.ofReal |∑ i ∈ s, f i| ≤ ∑ i ∈ s, g i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (ofReal_abs_add_le_add _ _).trans
      (add_le_add (h a (Finset.mem_insert_self a s))
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi)))

end Arith

variable {n q st m : ℕ} {Ω : Set (Fin n → ℝ)} {hΩ : IsOpen Ω}
  {X : Fin (q + 1) → (Fin n → ℝ) → (Fin n → ℝ)} {x₀ : Fin n → ℝ}
  {C : LiftedChart driftWeight st Ω hΩ X x₀ m} {F : KernelFrame (n + m)}

/-- The data of a cutoff `ζ` at the scale `1/A`: `ζ = 1` on `U_t`, supported in
`U_m ⊆ U_s ⊆ F.V` with `a = 1` on `U_s`, Hölder norms `‖ζ‖_{C^α} ≤ C_b A`, `‖X̃_lζ‖_{C^α} ≤ C_b A²` and sup
bounds `|L̃ζ| ≤ C_b A²`, `|X̃_l L̃ζ| ≤ C_b A³`, `|L̃L̃ζ| ≤ C_b A⁴`. -/
structure CutoffData (C : LiftedChart driftWeight st Ω hΩ X x₀ m) (F : KernelFrame (n + m))
    (a : TestFunction F.V ℝ (⊤ : ℕ∞)) (α Cb A : ℝ) (Ut Um Us : Opens (Fin (n + m) → ℝ))
    (ζ : (Fin (n + m) → ℝ) → ℝ) : Prop where
  Ut_Um : (Ut : Set (Fin (n + m) → ℝ)) ⊆ Um
  Um_Us : (Um : Set (Fin (n + m) → ℝ)) ⊆ Us
  Us_V : (Us : Set (Fin (n + m) → ℝ)) ⊆ F.V
  a_one : ∀ x ∈ (Us : Set (Fin (n + m) → ℝ)), a x = 1
  smooth : ContDiff ℝ (⊤ : ℕ∞) ζ
  compact : HasCompactSupport ζ
  range : ∀ ξ, 0 ≤ ζ ξ ∧ ζ ξ ≤ 1
  one_on : EqOn ζ (fun _ => 1) (Ut : Set (Fin (n + m) → ℝ))
  supp : tsupport ζ ⊆ (Um : Set (Fin (n + m) → ℝ))
  holder0 : holderENorm C.dl α C.O ζ ≤ ENNReal.ofReal (Cb * A)
  holder1 : ∀ l : Fin q,
    holderENorm C.dl α C.O (fieldDerivative (C.Xl l.succ) ζ) ≤ ENNReal.ofReal (Cb * A ^ 2)
  sup0 : ∀ ξ, |sumSquaresWithDrift C.Xl ζ ξ| ≤ Cb * A ^ 2
  sup1 : ∀ (l : Fin q) ξ, |fieldDerivative (C.Xl l.succ) (sumSquaresWithDrift C.Xl ζ) ξ| ≤ Cb * A ^ 3
  sup2 : ∀ ξ, |sumSquaresWithDrift C.Xl (sumSquaresWithDrift C.Xl ζ) ξ| ≤ Cb * A ^ 4
  Cb_nonneg : 0 ≤ Cb
  A_nonneg : 0 ≤ A

/-- The Hölder norm on the patch of a product `f b`, `b` supported in the
compact `K ⊆ U_m`, is at most `‖f‖_{C^α(U_m)} B` when `‖b‖_{C^α(U_m)} ≤ B` (first exit, the Hölder product estimate). -/
theorem holderENorm_zeroExt_mul_le (hF : C.IsLiftedFrame F) {α : ℝ} (hα0 : 0 < α)
    {Um : Opens (Fin (n + m) → ℝ)} (hUmV : (Um : Set (Fin (n + m) → ℝ)) ⊆ F.V)
    {K : Set (Fin (n + m) → ℝ)} (hK : IsCompact K) (hKU : K ⊆ (Um : Set (Fin (n + m) → ℝ)))
    {f b : (Fin (n + m) → ℝ) → ℝ} (hb0 : ∀ z, z ∉ K → b z = 0) {B : ℝ}
    (hbB : holderENorm C.dl α (Um : Set (Fin (n + m) → ℝ)) b ≤ ENNReal.ofReal B)
    (hf : holderENorm C.dl α (Um : Set (Fin (n + m) → ℝ)) f ≠ ⊤) :
    holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) (fun x => f x * b x) ≤
      holderENorm C.dl α (Um : Set (Fin (n + m) → ℝ)) f * ENNReal.ofReal B := by
  have hUmU : (Um : Set (Fin (n + m) → ℝ)) ⊆ C.U := hUmV.trans hF.subset_U
  have hsep : ∀ x ∈ (Um : Set (Fin (n + m) → ℝ)), ∀ y ∈ (Um : Set (Fin (n + m) → ℝ)),
      C.dl x y = 0 → x = y := fun x hx y hy hd =>
    congrArg Subtype.val
      ((C.distanceGeometry.distance_eq_zero_iff ⟨x, hUmU hx⟩ ⟨y, hUmU hy⟩).mp hd)
  have heq := holderENorm_cutoff_product_eq (Ω := C.O) (w := driftWeight) (X := C.Xl)
    driftWeight_le_two hα0 f b hK Um.isOpen hKU hUmV hb0
  have heq' : holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) (fun x => f x * b x) =
      holderENorm C.dl α (Um : Set (Fin (n + m) → ℝ)) (fun x => f x * b x) := heq
  rw [heq']
  exact (S.holderENorm_mul_le C.dl hα0 (Um : Set (Fin (n + m) → ℝ)) hsep f b
    (lt_top_iff_ne_top.2 hf) (hbB.trans_lt ENNReal.ofReal_lt_top)).trans (mul_le_mul' le_rfl hbB)

/-- On an open set where the cutoff is `1` the Leibniz jet is the jet of `u`. -/
theorem prodJet_eqOn_of_eqOn_one {U : Opens (Fin (n + m) → ℝ)} {ζ u : (Fin (n + m) → ℝ) → ℝ}
    {D : List (Fin (q + 1)) → (Fin (n + m) → ℝ) → ℝ}
    (h1 : EqOn ζ (fun _ => 1) (U : Set (Fin (n + m) → ℝ)))
    (hnil : EqOn (D []) u (U : Set (Fin (n + m) → ℝ))) {I : List (Fin (q + 1))}
    (hI : I ∈ wordFamily driftWeight 2) :
    EqOn (prodJet C.Xl ζ u D I) (D I) (U : Set (Fin (n + m) → ℝ)) := by
  intro x hx
  have h0 : ∀ Y : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ), fieldDerivative Y ζ x = 0 := fun Y =>
    fieldDerivative_eq_zero_of_eqOn_one U.isOpen h1 hx
  have h00 : ∀ Y Y' : (Fin (n + m) → ℝ) → (Fin (n + m) → ℝ),
      fieldDerivative Y (fieldDerivative Y' ζ) x = 0 := by
    intro Y Y'
    have hev : fieldDerivative Y' ζ =ᶠ[nhds x] fun _ => (0 : ℝ) := by
      filter_upwards [U.isOpen.mem_nhds hx] with y hy using fieldDerivative_eq_zero_of_eqOn_one
        U.isOpen h1 hy
    rw [fieldDerivative_congr_eventually hev]
    simp [fieldDerivative]
  rcases wordFamily_drift_cases hI with rfl | ⟨i, rfl⟩ | ⟨j, i, rfl⟩
  · simp only [prodJet, h1 hx, mul_one]
    exact (hnil hx).symm
  · simp [prodJet, h1 hx, h0]
  · simp [prodJet, h1 hx, h0, h00]

/-- The constant of the cutoff estimate (an explicit polynomial in `A = 1/a`). -/
def cutoffConst (Λ C₃ Cb A : ℝ) : ℝ :=
  Λ * (Cb * A + 2 * (Cb * A ^ 2) +
    C₃ * ((Cb * A ^ 2 + 2 * (Cb * A ^ 3) + Cb * A ^ 4) + Cb * A ^ 2) + 1)

theorem cutoffConst_nonneg {Λ C₃ Cb A : ℝ} (hΛ : 0 ≤ Λ) (hC₃ : 0 ≤ C₃) (hCb : 0 ≤ Cb)
    (hA : 0 ≤ A) : 0 ≤ cutoffConst Λ C₃ Cb A := by
  unfold cutoffConst
  positivity

/-- **The cutoff estimate.** Let `ζ` be a cutoff
at the scale `1/A` (`CutoffData`), `u` of finite Hölder norm with Hölder weak jet `D` on the patch `F.V`, and
assume the compact `C^{2,α}` estimate (`CompactHolderEstimate`, constant `Λ`) and the Hölder-from-sup bound
(`HolderFromSup`, constant `C₃`). Then
`‖u‖_{C^{2,α}(U_t)} ≤ c (‖L̃u‖_{C^α(U_s)} + ∑ₗ ‖X̃ₗu‖_{C^α(U_m)} + ‖u‖_{L^∞(U_s)})`
with `c = cutoffConst Λ C₃ C_b A`, `‖u‖_{C^{2,α}(U_t)}` computed on the weak jet. -/
theorem cutoff_estimate (hF : C.IsLiftedFrame F) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (a : TestFunction F.V ℝ (⊤ : ℕ∞)) {Λ C₃ Cb A : ℝ} (hΛ : 0 ≤ Λ) (hC₃ : 0 ≤ C₃)
    (hcomp : CompactHolderEstimate C F a α Λ) (hsupH : HolderFromSup C F a α C₃)
    {Ut Um Us : Opens (Fin (n + m) → ℝ)} {ζ : (Fin (n + m) → ℝ) → ℝ}
    (hZ : CutoffData C F a α Cb A Ut Um Us ζ)
    {u : (Fin (n + m) → ℝ) → ℝ} {D : List (Fin (q + 1)) → (Fin (n + m) → ℝ) → ℝ}
    (hu : holderENorm C.dl α (F.V : Set (Fin (n + m) → ℝ)) u ≠ ⊤)
    (hD : LiftedChart.IsHolderWeakJet driftWeight C.Xl C.dl F.V 2 α u D) :
    jetENorm C.dl α (Ut : Set (Fin (n + m) → ℝ)) D ≤ ENNReal.ofReal (cutoffConst Λ C₃ Cb A) *
      (holderENorm C.dl α (Us : Set (Fin (n + m) → ℝ)) (weakSumSquaresWithDrift D) +
        ∑ l : Fin q, holderENorm C.dl α (Um : Set (Fin (n + m) → ℝ)) (D [l.succ]) +
          supNormE (Us : Set (Fin (n + m) → ℝ)) u) := by
  classical
  have hw0 : ((driftWeight (0 : Fin (q + 1)) : ℕ+) : ℕ) = 2 := by simp [driftWeight]
  have hw : ∀ j : Fin q, ((driftWeight j.succ : ℕ+) : ℕ) = 1 := fun j => by
    simp [driftWeight, Fin.succ_ne_zero]
  set V : Set (Fin (n + m) → ℝ) := (F.V : Set (Fin (n + m) → ℝ)) with hV
  have hUmV : (Um : Set (Fin (n + m) → ℝ)) ⊆ V := hZ.Um_Us.trans hZ.Us_V
  have hUtV : (Ut : Set (Fin (n + m) → ℝ)) ⊆ V := hZ.Ut_Um.trans hUmV
  have hUmU : (Um : Set (Fin (n + m) → ℝ)) ⊆ C.U := hUmV.trans hF.subset_U
  have hUmO : (Um : Set (Fin (n + m) → ℝ)) ⊆ C.O := fun ξ hξ =>
    C.closure_U_subset (subset_closure (hUmU hξ))
  have hζV : tsupport ζ ⊆ V := hZ.supp.trans hUmV
  have hζU : tsupport ζ ⊆ C.U := hζV.trans hF.subset_U
  have hK : IsCompact (tsupport ζ) := hZ.compact
  have hz0 : ∀ z, z ∉ tsupport ζ → ζ z = 0 := fun z hz => image_eq_zero_of_notMem_tsupport hz
  have hucont : ContinuousOn u V :=
    LiftedChart.continuousOn_of_holderENorm_lt_top hF.subset_U hα0 (lt_top_iff_ne_top.2 hu)
  have hnil : EqOn (D []) u V := holderWeakJet_nil_eqOn (C := C) (V := F.V) hF.subset_U hα0 hucont
    (hD [] (S.nil_mem_wordFamily _ _)).1 (lt_top_iff_ne_top.2 (hD [] (S.nil_mem_wordFamily _ _)).2)
  -- sets and budgets
  set Hf := holderENorm C.dl α (Us : Set (Fin (n + m) → ℝ)) (weakSumSquaresWithDrift D) with hHf
  set E1 := ∑ l : Fin q, holderENorm C.dl α (Um : Set (Fin (n + m) → ℝ)) (D [l.succ]) with hE1
  set Eu := supNormE (Us : Set (Fin (n + m) → ℝ)) u with hEu
  set Sf := supNormE (Us : Set (Fin (n + m) → ℝ)) (weakSumSquaresWithDrift D) with hSf
  set Y := Hf + E1 + Eu with hY
  have hHfY : Hf ≤ Y := le_trans le_self_add le_self_add
  have hE1Y : E1 ≤ Y := le_trans le_add_self le_self_add
  have hEuY : Eu ≤ Y := le_add_self
  have hSfY : Sf ≤ Y := (supNormE_le_holderENorm _ _).trans hHfY
  -- finiteness of jet entries on `U_m`
  have hLfin : holderENorm C.dl α V (weakSumSquaresWithDrift D) ≠ ⊤ :=
    hD.weakSumSquaresWithDrift_ne_top hw0 hw hα0
  have hLfinm : holderENorm C.dl α (Um : Set (Fin (n + m) → ℝ)) (weakSumSquaresWithDrift D) ≠ ⊤ :=
    ne_top_of_le_ne_top hLfin (S.holderENorm_mono C.dl α V _ hUmV)
  have hDfinm : ∀ l : Fin q, holderENorm C.dl α (Um : Set (Fin (n + m) → ℝ)) (D [l.succ]) ≠ ⊤ :=
    fun l => ne_top_of_le_ne_top
      (hD [l.succ] (LiftedChart.horizontal_mem_wordFamily (w := driftWeight) hw l)).2
      (S.holderENorm_mono C.dl α V _ hUmV)
  -- the jet of the product `v = ζ u`
  have hjet := isHolderWeakJet_prodJet_ext hF (P := F.V) le_rfl hα0 hα1.le hZ.smooth hZ.compact hζV
    hu hD
  have hvC := memHolderXCompact_prod_ext hF (P := F.V) le_rfl hα0 hα1.le hZ.smooth hZ.compact hζV
    hu hD
  have hav : ∀ x, a x * (fun x => u x * ζ x) x = (fun x => u x * ζ x) x := by
    intro x
    by_cases hx : x ∈ tsupport ζ
    · simp [hZ.a_one x (hZ.Um_Us (hZ.supp hx))]
    · simp [hz0 x hx]
  have hmain := hcomp _ _ hvC hjet hav
  have hJle : jetENorm C.dl α (Ut : Set (Fin (n + m) → ℝ)) D ≤
      jetENorm C.dl α V (prodJet C.Xl ζ u D) := by
    have e : jetENorm C.dl α (Ut : Set (Fin (n + m) → ℝ)) D =
        jetENorm C.dl α (Ut : Set (Fin (n + m) → ℝ)) (prodJet C.Xl ζ u D) :=
      jetENorm_congr fun I hI =>
        (prodJet_eqOn_of_eqOn_one (C := C) hZ.one_on (hnil.mono hUtV) hI).symm
    rw [e]
    exact jetENorm_mono_set hUtV _
  -- the three terms of `L̃ (ζ u)`
  set g1 : (Fin (n + m) → ℝ) → ℝ := fun x => weakSumSquaresWithDrift D x * ζ x with hg1
  set h : (Fin (n + m) → ℝ) → ℝ := fun x =>
    ∑ i : Fin q, D [i.succ] x * fieldDerivative (C.Xl i.succ) ζ x with hh
  set g3 : (Fin (n + m) → ℝ) → ℝ := fun x => u x * sumSquaresWithDrift C.Xl ζ x with hg3
  have hLeq : ∀ x, weakSumSquaresWithDrift (prodJet C.Xl ζ u D) x = (g1 x + (h x + h x)) + g3 x :=
    fun x => by
      rw [weakSumSquaresWithDrift_prodJet]
      simp only [hg1, hh, hg3]
      ring
  have hLnorm : holderENorm C.dl α V (weakSumSquaresWithDrift (prodJet C.Xl ζ u D)) ≤
      (holderENorm C.dl α V g1 + (holderENorm C.dl α V h + holderENorm C.dl α V h)) +
        holderENorm C.dl α V g3 := by
    rw [S.holderENorm_congr C.dl α V _ (fun x _ => hLeq x)]
    exact (holderENorm_add_le hα0.le (fun x => g1 x + (h x + h x)) g3).trans
      (add_le_add ((holderENorm_add_le hα0.le g1 (fun x => h x + h x)).trans
        (add_le_add le_rfl (holderENorm_add_le hα0.le h h))) le_rfl)
  -- (1) `ζ L̃u`
  have hG1 : holderENorm C.dl α V g1 ≤ ENNReal.ofReal (Cb * A) * Hf := by
    have h1 := holderENorm_zeroExt_mul_le hF hα0 hUmV hK hZ.supp hz0
      ((S.holderENorm_mono C.dl α C.O ζ hUmO).trans hZ.holder0) hLfinm
    refine h1.trans ?_
    rw [mul_comm]
    exact mul_le_mul' le_rfl (S.holderENorm_mono C.dl α _ _ hZ.Um_Us)
  -- (2) the cross terms
  have hH : holderENorm C.dl α V h ≤ ENNReal.ofReal (Cb * A ^ 2) * E1 := by
    have h1 := holderENorm_sum_le_sum (d := C.dl) (α := α) (V := V) hα0.le
      (Finset.univ : Finset (Fin q))
      (fun i x => D [i.succ] x * fieldDerivative (C.Xl i.succ) ζ x)
    have h2 : ∀ i : Fin q, holderENorm C.dl α V
        (fun x => D [i.succ] x * fieldDerivative (C.Xl i.succ) ζ x) ≤
        holderENorm C.dl α (Um : Set (Fin (n + m) → ℝ)) (D [i.succ]) *
          ENNReal.ofReal (Cb * A ^ 2) := fun i =>
      holderENorm_zeroExt_mul_le hF hα0 hUmV hK hZ.supp
        (fun z hz => fieldDerivative_eq_zero_of_notMem_tsupport hz)
        ((S.holderENorm_mono C.dl α C.O _ hUmO).trans (hZ.holder1 i)) (hDfinm i)
    refine h1.trans ((Finset.sum_le_sum fun i _ => h2 i).trans ?_)
    rw [← Finset.sum_mul, mul_comm]
  -- (3) the term `u L̃ζ`
  set b : (Fin (n + m) → ℝ) → ℝ := sumSquaresWithDrift C.Xl ζ with hb
  have hbsub : tsupport b ⊆ tsupport ζ := tsupport_sumSquaresWithDrift_subset C.Xl ζ
  have hbsm : ContDiff ℝ (⊤ : ℕ∞) b := LiftedChart.contDiff_sumSquaresWithDrift_Xl hZ.smooth hζU
  have hbc : HasCompactSupport b := hZ.compact.of_isClosed_subset (isClosed_tsupport _) hbsub
  have hjet' := isHolderWeakJet_prodJet_ext hF (P := F.V) le_rfl hα0 hα1.le hbsm hbc
    (hbsub.trans hζV) hu hD
  have hvC' := memHolderXCompact_prod_ext hF (P := F.V) le_rfl hα0 hα1.le hbsm hbc
    (hbsub.trans hζV) hu hD
  have hav' : ∀ x, a x * (fun x => u x * b x) x = (fun x => u x * b x) x := by
    intro x
    by_cases hx : x ∈ tsupport b
    · simp [hZ.a_one x (hZ.Um_Us (hZ.supp (hbsub hx)))]
    · simp [image_eq_zero_of_notMem_tsupport hx]
  have hG3 := hsupH _ _ hvC' hjet' hav'
  have hSL : supNormE V (weakSumSquaresWithDrift (prodJet C.Xl b u D)) ≤
      ENNReal.ofReal (Cb * A ^ 2) * Sf + ENNReal.ofReal 2 * (ENNReal.ofReal (Cb * A ^ 3) * E1) +
        ENNReal.ofReal (Cb * A ^ 4) * Eu := by
    refine supNormE_le_of_forall fun x hxV => ?_
    rw [weakSumSquaresWithDrift_prodJet]
    by_cases hx : x ∈ tsupport ζ
    · have hxUm : x ∈ (Um : Set (Fin (n + m) → ℝ)) := hZ.supp hx
      have hxUs : x ∈ (Us : Set (Fin (n + m) → ℝ)) := hZ.Um_Us hxUm
      have t1 : ENNReal.ofReal |weakSumSquaresWithDrift D x * b x| ≤
          Sf * ENNReal.ofReal (Cb * A ^ 2) :=
        ofReal_abs_mul_le_of_le (ofReal_abs_le_supNormE hxUs)
          (ENNReal.ofReal_le_ofReal (hZ.sup0 x))
      have t2 : ENNReal.ofReal |2 * ∑ i : Fin q, D [i.succ] x * fieldDerivative (C.Xl i.succ) b x| ≤
          ENNReal.ofReal 2 * (E1 * ENNReal.ofReal (Cb * A ^ 3)) := by
        rw [abs_mul, ENNReal.ofReal_mul (abs_nonneg _), abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        refine mul_le_mul' le_rfl ?_
        rw [hE1, Finset.sum_mul]
        refine ofReal_abs_finset_sum_le _ _ fun i _ => ofReal_abs_mul_le_of_le ?_
          (ENNReal.ofReal_le_ofReal (hZ.sup1 i x))
        exact S.enorm_le_holderENorm C.dl α _ _ hxUm
      have t3 : ENNReal.ofReal |u x * sumSquaresWithDrift C.Xl b x| ≤
          Eu * ENNReal.ofReal (Cb * A ^ 4) :=
        ofReal_abs_mul_le_of_le (ofReal_abs_le_supNormE hxUs)
          (ENNReal.ofReal_le_ofReal (hZ.sup2 x))
      refine (ofReal_abs_add_le_add _ _).trans ?_
      refine (add_le_add (ofReal_abs_add_le_add _ _) le_rfl).trans ?_
      rw [mul_comm Sf, mul_comm E1, mul_comm Eu] at *
      exact add_le_add (add_le_add t1 t2) t3
    · have hb0 : b x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hbsub h))
      have hb1 : ∀ i : Fin q, fieldDerivative (C.Xl i.succ) b x = 0 := fun i =>
        fieldDerivative_eq_zero_of_notMem_tsupport (fun h => hx (hbsub h))
      have hb2 : sumSquaresWithDrift C.Xl b x = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hx ((tsupport_sumSquaresWithDrift_subset C.Xl b).trans
          hbsub h))
      simp [hb0, hb1, hb2]
  have hSw : supNormE V (fun x => u x * b x) ≤ ENNReal.ofReal (Cb * A ^ 2) * Eu := by
    refine supNormE_le_of_forall fun x hxV => ?_
    by_cases hx : x ∈ tsupport ζ
    · have hxUs : x ∈ (Us : Set (Fin (n + m) → ℝ)) := hZ.Um_Us (hZ.supp hx)
      rw [mul_comm]
      exact ofReal_abs_mul_le_of_le (ENNReal.ofReal_le_ofReal (hZ.sup0 x))
        (ofReal_abs_le_supNormE hxUs)
    · have hb0 : b x = 0 := image_eq_zero_of_notMem_tsupport (fun h => hx (hbsub h))
      simp [hb0]
  have hSv : supNormE V (fun x => u x * ζ x) ≤ Eu := by
    refine supNormE_le_of_forall fun x hxV => ?_
    by_cases hx : x ∈ tsupport ζ
    · have hxUs : x ∈ (Us : Set (Fin (n + m) → ℝ)) := hZ.Um_Us (hZ.supp hx)
      obtain ⟨hz0', hz1'⟩ := hZ.range x
      rw [abs_mul, abs_of_nonneg hz0', ENNReal.ofReal_mul (abs_nonneg _)]
      calc ENNReal.ofReal |u x| * ENNReal.ofReal (ζ x) ≤ Eu * 1 :=
            mul_le_mul' (ofReal_abs_le_supNormE hxUs) (by
              rw [← ENNReal.ofReal_one]; exact ENNReal.ofReal_le_ofReal hz1')
        _ = Eu := mul_one _
    · simp [hz0 x hx]
  -- assemble
  have bg1 : BoundedBy (holderENorm C.dl α V g1) Y (Cb * A) :=
    (BoundedBy.of_const_mul_le (mul_nonneg hZ.Cb_nonneg hZ.A_nonneg) hHfY).mono_left hG1
  have bg2 : BoundedBy (holderENorm C.dl α V h + holderENorm C.dl α V h) Y
      (2 * (Cb * A ^ 2)) := by
    have hb' : BoundedBy (ENNReal.ofReal (Cb * A ^ 2) * E1) Y (Cb * A ^ 2) :=
      BoundedBy.of_const_mul_le (by have := hZ.Cb_nonneg; positivity) hE1Y
    have := (hb'.const_mul (k := 2) (by norm_num))
    refine this.mono_left ?_
    rw [← two_mul]
    calc 2 * holderENorm C.dl α V h ≤ 2 * (ENNReal.ofReal (Cb * A ^ 2) * E1) :=
          mul_le_mul' le_rfl hH
      _ = ENNReal.ofReal 2 * (ENNReal.ofReal (Cb * A ^ 2) * E1) := by
          rw [ENNReal.ofReal_ofNat]
  have bSL : BoundedBy (supNormE V (weakSumSquaresWithDrift (prodJet C.Xl b u D))) Y
      ((Cb * A ^ 2 + 2 * (Cb * A ^ 3)) + Cb * A ^ 4) := by
    have hCb0 := hZ.Cb_nonneg
    have hA0 := hZ.A_nonneg
    have c1 : BoundedBy (ENNReal.ofReal (Cb * A ^ 2) * Sf) Y (Cb * A ^ 2) :=
      BoundedBy.of_const_mul_le (by positivity) hSfY
    have c2 : BoundedBy (ENNReal.ofReal 2 * (ENNReal.ofReal (Cb * A ^ 3) * E1)) Y
        (2 * (Cb * A ^ 3)) :=
      (BoundedBy.of_const_mul_le (by positivity) hE1Y).const_mul (by norm_num)
    have c3 : BoundedBy (ENNReal.ofReal (Cb * A ^ 4) * Eu) Y (Cb * A ^ 4) :=
      BoundedBy.of_const_mul_le (by positivity) hEuY
    exact ((c1.add c2 (by positivity) (by positivity)).add c3 (by positivity)
      (by positivity)).mono_left hSL
  have bSw : BoundedBy (supNormE V (fun x => u x * b x)) Y (Cb * A ^ 2) :=
    (BoundedBy.of_const_mul_le (by have := hZ.Cb_nonneg; positivity) hEuY).mono_left hSw
  have bg3 : BoundedBy (holderENorm C.dl α V g3) Y
      (C₃ * (((Cb * A ^ 2 + 2 * (Cb * A ^ 3)) + Cb * A ^ 4) + Cb * A ^ 2)) := by
    have hCb0 := hZ.Cb_nonneg
    have hA0 := hZ.A_nonneg
    have := ((bSL.add bSw (by positivity) (by positivity)).const_mul hC₃)
    exact this.mono_left hG3
  have bSv : BoundedBy (supNormE V (fun x => u x * ζ x)) Y 1 :=
    (BoundedBy.of_le hEuY).mono_left hSv
  have hCb0 := hZ.Cb_nonneg
  have hA0 := hZ.A_nonneg
  have hall := (((bg1.add bg2 (by positivity) (by positivity)).add bg3 (by positivity)
    (by positivity)).mono_left hLnorm).add bSv (by positivity) zero_le_one
  unfold BoundedBy at hall
  calc jetENorm C.dl α (Ut : Set (Fin (n + m) → ℝ)) D ≤ jetENorm C.dl α V (prodJet C.Xl ζ u D) := hJle
    _ ≤ ENNReal.ofReal Λ * (holderENorm C.dl α V (weakSumSquaresWithDrift (prodJet C.Xl ζ u D)) +
        supNormE V (fun x => u x * ζ x)) := hmain
    _ ≤ ENNReal.ofReal Λ * (ENNReal.ofReal (Cb * A + 2 * (Cb * A ^ 2) +
        C₃ * (((Cb * A ^ 2 + 2 * (Cb * A ^ 3)) + Cb * A ^ 4) + Cb * A ^ 2) + 1) * Y) :=
        mul_le_mul' le_rfl hall
    _ = ENNReal.ofReal (cutoffConst Λ C₃ Cb A) * Y := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hΛ]
        rfl

end RothschildStein.P2
