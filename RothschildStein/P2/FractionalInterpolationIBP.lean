-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P2.FractionalInterpolationJet
public import RothschildStein.P2.CutoffsSymbols

/-!
# Hölder interpolation: integration by parts for a second-order operator

The far part of the first interpolation inequality moves `L̃` from `v` onto the kernel
(the formal adjoint formula, BB p. 560, (11.40)). The adjoint is used with `C²` kernels (the regular
remainders of a type decomposition are only `C^m`), so the pairing identity is proved here for an arbitrary
second-order operator in coordinates
`L f = ∑_{a,b} A_{ab} ∂_a ∂_b f + ∑_a B_a ∂_a f`
(`diffOp2`) and a `C²` test function `φ` with compact support in the open set `O`
(`integral_diffOp2_mul_eq`): `∫ (L f) φ = ∫ f (L* φ)` with the divergence-form adjoint
`L* φ = ∑ ∂_b ∂_a (A_{ab} φ) - ∑ ∂_a (B_a φ)` (`adjOp2`), and its coefficient form `adjForm`
(`adjOp2_eq_adjForm`) by the product rule. The kernel `K(ξ, η) = L*_η H(ξ, ·)(η)` of a `C³`
kernel `H` is the function `adjKernel` of `ℝ^N × ℝ^N` (`adjOp2_slice`), built from the jets of
`H` of `FractionalInterpolationJet`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory Filter
open scoped Topology BigOperators
namespace RothschildStein.P2

variable {N : ℕ}

section Integrals

/-- A function continuous on a compact set and zero outside it is integrable. -/
theorem integrable_of_continuousOn_of_zero {F : (Fin N → ℝ) → ℝ} {K : Set (Fin N → ℝ)}
    (hK : IsCompact K) (hF : ContinuousOn F K) (h0 : ∀ x, x ∉ K → F x = 0) : Integrable F := by
  have h1 : IntegrableOn F K volume := hF.integrableOn_compact hK
  refine (integrableOn_iff_integrable_of_support_subset (s := K) ?_).mp h1
  intro x hx
  by_contra hxK
  exact hx (h0 x hxK)

/-- A `C^n` function on an open set that vanishes off a closed subset of that set is a
globally `C^n` function. -/
theorem contDiff_of_contDiffOn_of_zero {n : WithTop ℕ∞} {F : (Fin N → ℝ) → ℝ}
    {O K : Set (Fin N → ℝ)} (hO : IsOpen O) (hKc : IsClosed K) (hKO : K ⊆ O)
    (hF : ContDiffOn ℝ n F O) (h0 : ∀ x, x ∉ K → F x = 0) : ContDiff ℝ n F := by
  refine contDiff_iff_contDiffAt.2 (fun x => ?_)
  by_cases hx : x ∈ O
  · exact hF.contDiffAt (hO.mem_nhds hx)
  · have hxK : x ∉ K := fun h => hx (hKO h)
    have : F =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [hKc.isOpen_compl.mem_nhds hxK] with y hy
      exact h0 y hy
    exact contDiffAt_const.congr_of_eventuallyEq this

/-- The product of a function that is `C^n` on `O` with a `C^n` function whose support lies
in a compact subset of `O` is globally `C^n`. -/
theorem contDiff_mul_of_support {n : WithTop ℕ∞} {A φ : (Fin N → ℝ) → ℝ}
    {O : Set (Fin N → ℝ)} (hO : IsOpen O) (hA : ContDiffOn ℝ n A O) (hφ : ContDiff ℝ n φ)
    (hφO : tsupport φ ⊆ O) : ContDiff ℝ n (fun x => A x * φ x) :=
  contDiff_of_contDiffOn_of_zero hO (isClosed_tsupport φ) hφO
    (hA.mul hφ.contDiffOn) (fun x hx => by rw [image_eq_zero_of_notMem_tsupport hx, mul_zero])

theorem hasCompactSupport_mul_of_support {A φ : (Fin N → ℝ) → ℝ} (hφ : HasCompactSupport φ) :
    HasCompactSupport (fun x => A x * φ x) :=
  hφ.mul_left

theorem tsupport_mul_subset' {A φ : (Fin N → ℝ) → ℝ} :
    tsupport (fun x => A x * φ x) ⊆ tsupport φ :=
  tsupport_mul_subset_right

/-- Coordinate integration by parts: `∫ ∂_a g · ψ = - ∫ g · ∂_a ψ` for `g` `C¹` on the open
set `O` and `ψ` a `C¹` function with compact support in `O`. -/
theorem integral_pdv_mul_eq {O : Set (Fin N → ℝ)} (hO : IsOpen O) {g ψ : (Fin N → ℝ) → ℝ}
    (hg : ContDiffOn ℝ 1 g O) (hψ : ContDiff ℝ 1 ψ) (hψc : HasCompactSupport ψ)
    (hψO : tsupport ψ ⊆ O) (a : Fin N) :
    ∫ x, pdv a g x * ψ x = -∫ x, g x * pdv a ψ x := by
  have hgc : ContinuousOn g O := hg.continuousOn
  have hdg : ContinuousOn (fun x => fderiv ℝ g x (Pi.single a 1)) O :=
    (hg.continuousOn_fderiv_of_isOpen hO le_rfl).clm_apply continuousOn_const
  have hdψ : Continuous (fun x => fderiv ℝ ψ x (Pi.single a 1)) :=
    (hψ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hKc : IsCompact (tsupport ψ) := hψc
  have hψ0 : ∀ x, x ∉ tsupport ψ → ψ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  have hdψ0 : ∀ x, x ∉ tsupport ψ → fderiv ℝ ψ x (Pi.single a 1) = 0 := fun x hx => by
    rw [fderiv_of_notMem_tsupport ℝ hx]; rfl
  have i1 : Integrable (fun x => pdv a g x * ψ x) :=
    integrable_of_continuousOn_of_zero hKc
      ((hdg.mono hψO).mul hψ.continuous.continuousOn) (fun x hx => by
        simp [hψ0 x hx])
  have i2 : Integrable (fun x => g x * pdv a ψ x) :=
    integrable_of_continuousOn_of_zero hKc
      ((hgc.mono hψO).mul hdψ.continuousOn) (fun x hx => by
        simp [pdv, hdψ0 x hx])
  have i3 : Integrable (fun x => g x * ψ x) :=
    integrable_of_continuousOn_of_zero hKc
      ((hgc.mono hψO).mul hψ.continuous.continuousOn) (fun x hx => by simp [hψ0 x hx])
  have i1' : Integrable (fun x => fderiv ℝ ψ x (Pi.single a 1) * g x) := by
    refine integrable_of_continuousOn_of_zero hKc
      (hdψ.continuousOn.mul (hgc.mono hψO)) (fun x hx => by simp [hdψ0 x hx])
  have i2' : Integrable (fun x => ψ x * fderiv ℝ g x (Pi.single a 1)) := by
    refine integrable_of_continuousOn_of_zero hKc
      (hψ.continuous.continuousOn.mul (hdg.mono hψO)) (fun x hx => by simp [hψ0 x hx])
  have i3' : Integrable (fun x => ψ x * g x) := by
    refine integrable_of_continuousOn_of_zero hKc
      (hψ.continuous.continuousOn.mul (hgc.mono hψO)) (fun x hx => by simp [hψ0 x hx])
  have h := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (μ := volume) (f := ψ) (g := g)
    (v := Pi.single a 1) i1' i2' i3'
    (fun x _ => hψ.differentiable one_ne_zero x)
    (fun x hx => (hg.contDiffAt (hO.mem_nhds (hψO hx))).differentiableAt one_ne_zero)
  have e1 : ∫ x, pdv a g x * ψ x = ∫ x, ψ x * fderiv ℝ g x (Pi.single a 1) := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [pdv]; ring
  have e2 : ∫ x, g x * pdv a ψ x = ∫ x, fderiv ℝ ψ x (Pi.single a 1) * g x := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [pdv]; ring
  rw [e1, e2]
  exact h

end Integrals

section Operator

/-- A second-order operator in coordinates:
`L f = ∑_{a,b} A_{ab} ∂_a ∂_b f + ∑_a B_a ∂_a f` (`∂_a ∂_b f = pdv a (pdv b f)`). -/
def diffOp2 (A : Fin N → Fin N → (Fin N → ℝ) → ℝ) (B : Fin N → (Fin N → ℝ) → ℝ)
    (f : (Fin N → ℝ) → ℝ) (x : Fin N → ℝ) : ℝ :=
  ∑ a, ∑ b, A a b x * pdv a (pdv b f) x + ∑ a, B a x * pdv a f x

/-- The divergence-form formal adjoint
`L* φ = ∑_{a,b} ∂_b ∂_a (A_{ab} φ) - ∑_a ∂_a (B_a φ)` of `diffOp2 A B`. -/
def adjOp2 (A : Fin N → Fin N → (Fin N → ℝ) → ℝ) (B : Fin N → (Fin N → ℝ) → ℝ)
    (φ : (Fin N → ℝ) → ℝ) (x : Fin N → ℝ) : ℝ :=
  ∑ a, ∑ b, pdv b (pdv a (fun y => A a b y * φ y)) x - ∑ a, pdv a (fun y => B a y * φ y) x

theorem contDiff_pdv {n : ℕ} {ψ : (Fin N → ℝ) → ℝ}
    (hψ : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) ψ) (a : Fin N) :
    ContDiff ℝ (n : WithTop ℕ∞) (pdv a ψ) :=
  (hψ.fderiv_right (by push_cast; exact le_rfl)).clm_apply contDiff_const

theorem contDiffOn_pdv {n : ℕ} {f : (Fin N → ℝ) → ℝ} {O : Set (Fin N → ℝ)} (hO : IsOpen O)
    (hf : ContDiffOn ℝ ((n + 1 : ℕ) : WithTop ℕ∞) f O) (a : Fin N) :
    ContDiffOn ℝ (n : WithTop ℕ∞) (pdv a f) O :=
  (hf.fderiv_of_isOpen hO (by push_cast; exact le_rfl)).clm_apply contDiffOn_const

theorem tsupport_pdv_subset {ψ : (Fin N → ℝ) → ℝ} (a : Fin N) :
    tsupport (pdv a ψ) ⊆ tsupport ψ :=
  tsupport_fderiv_apply_subset ℝ _

theorem hasCompactSupport_pdv {ψ : (Fin N → ℝ) → ℝ} (hψ : HasCompactSupport ψ) (a : Fin N) :
    HasCompactSupport (pdv a ψ) :=
  hψ.fderiv_apply ℝ _

theorem pdv_eq_zero_of_notMem {ψ : (Fin N → ℝ) → ℝ} {x : Fin N → ℝ} (hx : x ∉ tsupport ψ)
    (a : Fin N) : pdv a ψ x = 0 := by
  simp only [pdv]
  rw [fderiv_of_notMem_tsupport ℝ hx]
  rfl

/-- **Integration by parts for a second-order operator against a `C²` test function**
(the formal adjoint formula, BB p. 560, (11.40), in coordinates): for `f` `C²` on the open set `O`, `A, B`
smooth enough on `O` and `φ` a `C²` function with compact support in `O`,
`∫ (L f) φ = ∫ f (L* φ)`. -/
theorem integral_diffOp2_mul_eq {O : Set (Fin N → ℝ)} (hO : IsOpen O)
    {A : Fin N → Fin N → (Fin N → ℝ) → ℝ} {B : Fin N → (Fin N → ℝ) → ℝ}
    (hA : ∀ a b, ContDiffOn ℝ 2 (A a b) O) (hB : ∀ a, ContDiffOn ℝ 1 (B a) O)
    {f : (Fin N → ℝ) → ℝ} (hf : ContDiffOn ℝ 2 f O)
    {φ : (Fin N → ℝ) → ℝ} (hφ : ContDiff ℝ 2 φ) (hφc : HasCompactSupport φ)
    (hφO : tsupport φ ⊆ O) :
    ∫ x, diffOp2 A B f x * φ x = ∫ x, f x * adjOp2 A B φ x := by
  have hK : IsCompact (tsupport φ) := hφc
  have hφ0 : ∀ x, x ∉ tsupport φ → φ x = 0 := fun x hx => image_eq_zero_of_notMem_tsupport hx
  have hf1 : ContDiffOn ℝ 1 f O := hf.of_le (by norm_num)
  have hfb : ∀ b, ContDiffOn ℝ 1 (pdv b f) O := fun b => contDiffOn_pdv (n := 1) hO hf b
  have hfab : ∀ a b, ContinuousOn (pdv a (pdv b f)) O := fun a b =>
    (contDiffOn_pdv (n := 0) hO (hfb b) a).continuousOn
  -- the test functions `A_{ab} φ` and `B_a φ`
  have hψ : ∀ a b, ContDiff ℝ 2 (fun y => A a b y * φ y) := fun a b =>
    contDiff_mul_of_support hO (hA a b) hφ hφO
  have hψO : ∀ a b, tsupport (fun y => A a b y * φ y) ⊆ O := fun a b =>
    tsupport_mul_subset'.trans hφO
  have hψc : ∀ a b, HasCompactSupport (fun y => A a b y * φ y) := fun a b =>
    hasCompactSupport_mul_of_support hφc
  have hχ : ∀ a, ContDiff ℝ 1 (fun y => B a y * φ y) := fun a =>
    contDiff_mul_of_support hO (hB a) (hφ.of_le (by norm_num)) hφO
  have hχO : ∀ a, tsupport (fun y => B a y * φ y) ⊆ O := fun a => tsupport_mul_subset'.trans hφO
  have hχc : ∀ a, HasCompactSupport (fun y => B a y * φ y) := fun a =>
    hasCompactSupport_mul_of_support hφc
  -- second-order terms
  have T1 : ∀ a b, ∫ x, A a b x * pdv a (pdv b f) x * φ x =
      ∫ x, f x * pdv b (pdv a (fun y => A a b y * φ y)) x := by
    intro a b
    have e : ∀ x, A a b x * pdv a (pdv b f) x * φ x = pdv a (pdv b f) x * (A a b x * φ x) :=
      fun x => by ring
    simp_rw [e]
    have h1 := integral_pdv_mul_eq hO (hfb b) (hψ a b |>.of_le (by norm_num)) (hψc a b) (hψO a b) a
    have hd : ContDiff ℝ 1 (pdv a (fun y => A a b y * φ y)) := contDiff_pdv (n := 1) (hψ a b) a
    have h2 := integral_pdv_mul_eq hO hf1 hd (hasCompactSupport_pdv (hψc a b) a)
      ((tsupport_pdv_subset a).trans (hψO a b)) b
    rw [h1, h2]
    simp_rw [neg_neg]
  -- first-order terms
  have T2 : ∀ a, ∫ x, B a x * pdv a f x * φ x = -∫ x, f x * pdv a (fun y => B a y * φ y) x := by
    intro a
    have e : ∀ x, B a x * pdv a f x * φ x = pdv a f x * (B a x * φ x) := fun x => by ring
    simp_rw [e]
    exact integral_pdv_mul_eq hO hf1 (hχ a) (hχc a) (hχO a) a
  -- integrability of the individual terms
  have iL1 : ∀ a b, Integrable (fun x => A a b x * pdv a (pdv b f) x * φ x) := fun a b =>
    integrable_of_continuousOn_of_zero hK
      ((((hA a b).continuousOn.mono hφO).mul (hfab a b |>.mono hφO)).mul
        hφ.continuous.continuousOn) (fun x hx => by simp [hφ0 x hx])
  have iL2 : ∀ a, Integrable (fun x => B a x * pdv a f x * φ x) := fun a =>
    integrable_of_continuousOn_of_zero hK
      ((((hB a).continuousOn.mono hφO).mul ((hfb a).continuousOn.mono hφO)).mul
        hφ.continuous.continuousOn) (fun x hx => by simp [hφ0 x hx])
  have hdd : ∀ a b, Continuous (pdv b (pdv a (fun y => A a b y * φ y))) := fun a b =>
    (contDiff_pdv (n := 0) (contDiff_pdv (n := 1) (hψ a b) a) b).continuous
  have hd1 : ∀ a, Continuous (pdv a (fun y => B a y * φ y)) := fun a =>
    (contDiff_pdv (n := 0) (hχ a) a).continuous
  have z1 : ∀ a b x, x ∉ tsupport φ → pdv b (pdv a (fun y => A a b y * φ y)) x = 0 := by
    intro a b x hx
    have hx1 : x ∉ tsupport (pdv a (fun y => A a b y * φ y)) := fun h =>
      hx (tsupport_mul_subset' (tsupport_pdv_subset a h))
    exact pdv_eq_zero_of_notMem hx1 b
  have z2 : ∀ a x, x ∉ tsupport φ → pdv a (fun y => B a y * φ y) x = 0 := by
    intro a x hx
    exact pdv_eq_zero_of_notMem (fun h => hx (tsupport_mul_subset' h)) a
  have iR1 : ∀ a b, Integrable (fun x => f x * pdv b (pdv a (fun y => A a b y * φ y)) x) :=
    fun a b => integrable_of_continuousOn_of_zero hK
      ((hf.continuousOn.mono hφO).mul (hdd a b).continuousOn) (fun x hx => by simp [z1 a b x hx])
  have iR2 : ∀ a, Integrable (fun x => f x * pdv a (fun y => B a y * φ y) x) := fun a =>
    integrable_of_continuousOn_of_zero hK
      ((hf.continuousOn.mono hφO).mul (hd1 a).continuousOn) (fun x hx => by simp [z2 a x hx])
  -- assemble
  have eL : ∀ x, diffOp2 A B f x * φ x = ∑ a, ∑ b, A a b x * pdv a (pdv b f) x * φ x +
      ∑ a, B a x * pdv a f x * φ x := by
    intro x
    simp only [diffOp2, add_mul, Finset.sum_mul]
  have eR : ∀ x, f x * adjOp2 A B φ x = ∑ a, ∑ b,
      f x * pdv b (pdv a (fun y => A a b y * φ y)) x -
      ∑ a, f x * pdv a (fun y => B a y * φ y) x := by
    intro x
    simp only [adjOp2, mul_sub, Finset.mul_sum]
  simp_rw [eL, eR]
  rw [integral_add (integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => iL1 a b)
      (integrable_finsetSum _ fun a _ => iL2 a),
    integral_sub (integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => iR1 a b)
      (integrable_finsetSum _ fun a _ => iR2 a),
    integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => iL1 a b,
    integral_finsetSum _ fun a _ => iL2 a,
    integral_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => iR1 a b,
    integral_finsetSum _ fun a _ => iR2 a]
  simp_rw [integral_finsetSum _ fun b _ => iL1 _ b, integral_finsetSum _ fun b _ => iR1 _ b]
  have s1 : ∑ a, ∑ b, ∫ x, A a b x * pdv a (pdv b f) x * φ x =
      ∑ a, ∑ b, ∫ x, f x * pdv b (pdv a (fun y => A a b y * φ y)) x :=
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => T1 a b
  have s2 : ∑ a, ∫ x, B a x * pdv a f x * φ x = -∑ a, ∫ x, f x *
      pdv a (fun y => B a y * φ y) x := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun a _ => T2 a
  rw [s1, s2]
  ring

end Operator

section AdjointForm

theorem pdv_mul {g h : (Fin N → ℝ) → ℝ} {x : Fin N → ℝ} (hg : DifferentiableAt ℝ g x)
    (hh : DifferentiableAt ℝ h x) (a : Fin N) :
    pdv a (fun y => g y * h y) x = pdv a g x * h x + g x * pdv a h x := by
  have h : fderiv ℝ (fun y => g y * h y) x = g x • fderiv ℝ h x + h x • fderiv ℝ g x :=
    (hg.hasFDerivAt.mul hh.hasFDerivAt).fderiv
  simp only [pdv]
  rw [h]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

theorem pdv_add {g h : (Fin N → ℝ) → ℝ} {x : Fin N → ℝ} (hg : DifferentiableAt ℝ g x)
    (hh : DifferentiableAt ℝ h x) (a : Fin N) :
    pdv a (fun y => g y + h y) x = pdv a g x + pdv a h x := by
  have h : fderiv ℝ (fun y => g y + h y) x = fderiv ℝ g x + fderiv ℝ h x :=
    (hg.hasFDerivAt.add hh.hasFDerivAt).fderiv
  simp only [pdv]
  rw [h]
  rfl

/-- The product rule for `∂_b ∂_a (A φ)`. -/
theorem pdv_pdv_mul {A φ : (Fin N → ℝ) → ℝ} {O : Set (Fin N → ℝ)} (hO : IsOpen O)
    (hA : ContDiffOn ℝ 2 A O) (hφ : ContDiff ℝ 2 φ) {x : Fin N → ℝ} (hx : x ∈ O) (a b : Fin N) :
    pdv b (pdv a (fun y => A y * φ y)) x =
      pdv b (pdv a A) x * φ x + pdv a A x * pdv b φ x + pdv b A x * pdv a φ x +
        A x * pdv b (pdv a φ) x := by
  have hdφ : ∀ y, DifferentiableAt ℝ φ y := fun y => (hφ.differentiable (by norm_num)) y
  have hdφ1 : ∀ y, DifferentiableAt ℝ (pdv a φ) y := fun y =>
    ((contDiff_pdv (n := 1) hφ a).differentiable one_ne_zero) y
  have hev : pdv a (fun y => A y * φ y) =ᶠ[𝓝 x]
      fun y => pdv a A y * φ y + A y * pdv a φ y := by
    filter_upwards [hO.mem_nhds hx] with y hy
    have hAy : DifferentiableAt ℝ A y := (hA.contDiffAt (hO.mem_nhds hy)).differentiableAt
      (by norm_num)
    rw [pdv_mul hAy (hdφ y) a]
  have hAx : DifferentiableAt ℝ A x := (hA.contDiffAt (hO.mem_nhds hx)).differentiableAt
    (by norm_num)
  have hpAx : DifferentiableAt ℝ (pdv a A) x :=
    ((contDiffOn_pdv (n := 1) hO hA a).contDiffAt (hO.mem_nhds hx)).differentiableAt one_ne_zero
  have e1 : pdv b (pdv a (fun y => A y * φ y)) x =
      pdv b (fun y => pdv a A y * φ y + A y * pdv a φ y) x := by
    show fderiv ℝ (pdv a (fun y => A y * φ y)) x (Pi.single b 1) =
      fderiv ℝ (fun y => pdv a A y * φ y + A y * pdv a φ y) x (Pi.single b 1)
    rw [hev.fderiv_eq]
  have hp1 : DifferentiableAt ℝ (fun y => pdv a A y * φ y) x := hpAx.mul (hdφ x)
  have hp2 : DifferentiableAt ℝ (fun y => A y * pdv a φ y) x := hAx.mul (hdφ1 x)
  rw [e1, pdv_add hp1 hp2 b, pdv_mul hpAx (hdφ x) b, pdv_mul hAx (hdφ1 x) b]
  ring

/-- The coefficient form of the adjoint: `L* φ` as a combination of `φ`, `∂_a φ`,
`∂_b ∂_a φ` with the coefficients `A, ∂A, ∂∂A, B, ∂B`. -/
def adjForm (A : Fin N → Fin N → (Fin N → ℝ) → ℝ) (B : Fin N → (Fin N → ℝ) → ℝ)
    (φ : (Fin N → ℝ) → ℝ) (x : Fin N → ℝ) : ℝ :=
  ∑ a, ∑ b, (pdv b (pdv a (A a b)) x * φ x + pdv a (A a b) x * pdv b φ x +
      pdv b (A a b) x * pdv a φ x + A a b x * pdv b (pdv a φ) x) -
    ∑ a, (pdv a (B a) x * φ x + B a x * pdv a φ x)

theorem adjOp2_eq_adjForm {O : Set (Fin N → ℝ)} (hO : IsOpen O)
    {A : Fin N → Fin N → (Fin N → ℝ) → ℝ} {B : Fin N → (Fin N → ℝ) → ℝ}
    (hA : ∀ a b, ContDiffOn ℝ 2 (A a b) O) (hB : ∀ a, ContDiffOn ℝ 1 (B a) O)
    {φ : (Fin N → ℝ) → ℝ} (hφ : ContDiff ℝ 2 φ) {x : Fin N → ℝ} (hx : x ∈ O) :
    adjOp2 A B φ x = adjForm A B φ x := by
  unfold adjOp2 adjForm
  congr 1
  · refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    exact pdv_pdv_mul hO (hA a b) hφ hx a b
  · refine Finset.sum_congr rfl fun a _ => ?_
    have hBx : DifferentiableAt ℝ (B a) x :=
      ((hB a).contDiffAt (hO.mem_nhds hx)).differentiableAt one_ne_zero
    exact pdv_mul hBx (hφ.differentiable (by norm_num) x) a

end AdjointForm

section Slice

theorem pdv_slice {G : E2 N → ℝ} (hG : Differentiable ℝ G) (ξ η : Fin N → ℝ) (a : Fin N) :
    pdv a (fun η' => G (ξ, η')) η = dirDeriv [dirEta (unitVec a)] G (ξ, η) := by
  have h1 : HasFDerivAt (fun η' : Fin N → ℝ => (ξ, η'))
      ((0 : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ)).prod (ContinuousLinearMap.id ℝ (Fin N → ℝ))) η :=
    (hasFDerivAt_const ξ η).prodMk (hasFDerivAt_id η)
  have h2 : HasFDerivAt (fun η' : Fin N → ℝ => G (ξ, η'))
      ((fderiv ℝ G (ξ, η)).comp
        ((0 : (Fin N → ℝ) →L[ℝ] (Fin N → ℝ)).prod (ContinuousLinearMap.id ℝ (Fin N → ℝ)))) η :=
    (hG (ξ, η)).hasFDerivAt.comp η h1
  simp only [pdv]
  rw [h2.fderiv]
  simp [dirDeriv, dirEta]

theorem pdv_pdv_slice {H : E2 N → ℝ} (hH : ContDiff ℝ 2 H) (ξ η : Fin N → ℝ) (a b : Fin N) :
    pdv b (pdv a (fun η' => H (ξ, η'))) η = etaPartial₂ a b H (ξ, η) := by
  have hd : Differentiable ℝ H := hH.differentiable (by norm_num)
  have h1 : pdv a (fun η' => H (ξ, η')) = fun η' => etaPartial a H (ξ, η') := by
    funext η'; exact pdv_slice hd ξ η' a
  rw [h1]
  have hd1 : Differentiable ℝ (etaPartial a H) := by
    have : ContDiff ℝ ((1 : ℕ) : WithTop ℕ∞) (etaPartial a H) :=
      contDiff_dirDeriv (n := 1) [dirEta (unitVec a)] H (by simpa using hH)
    exact (this.differentiable one_ne_zero)
  exact pdv_slice hd1 ξ η b

/-- The kernel `K(ξ, η) = (L*_η H(ξ, ·))(η)` of the integration by parts, as a function on
`ℝ^N × ℝ^N` built from the `η`-jets of `H` (coefficient form of the adjoint). -/
def adjKernel (A : Fin N → Fin N → (Fin N → ℝ) → ℝ) (B : Fin N → (Fin N → ℝ) → ℝ)
    (H : E2 N → ℝ) (p : E2 N) : ℝ :=
  ∑ a, ∑ b, (pdv b (pdv a (A a b)) p.2 * H p + pdv a (A a b) p.2 * etaPartial b H p +
      pdv b (A a b) p.2 * etaPartial a H p + A a b p.2 * etaPartial₂ a b H p) -
    ∑ a, (pdv a (B a) p.2 * H p + B a p.2 * etaPartial a H p)

theorem adjOp2_slice {O : Set (Fin N → ℝ)} (hO : IsOpen O)
    {A : Fin N → Fin N → (Fin N → ℝ) → ℝ} {B : Fin N → (Fin N → ℝ) → ℝ}
    (hA : ∀ a b, ContDiffOn ℝ 2 (A a b) O) (hB : ∀ a, ContDiffOn ℝ 1 (B a) O)
    {H : E2 N → ℝ} (hH : ContDiff ℝ 3 H) {ξ η : Fin N → ℝ} (hη : η ∈ O) :
    adjOp2 A B (fun η' => H (ξ, η')) η = adjKernel A B H (ξ, η) := by
  have hH2 : ContDiff ℝ 2 H := hH.of_le (by norm_num)
  have hφ : ContDiff ℝ 2 (fun η' : Fin N → ℝ => H (ξ, η')) :=
    hH2.comp (contDiff_const.prodMk contDiff_id)
  rw [adjOp2_eq_adjForm hO hA hB hφ hη]
  have hd : Differentiable ℝ H := hH.differentiable (by norm_num)
  unfold adjForm adjKernel
  have h0 : ∀ a, pdv a (fun η' => H (ξ, η')) η = etaPartial a H (ξ, η) := fun a =>
    pdv_slice hd ξ η a
  simp only [h0, pdv_pdv_slice hH2]

end Slice

end RothschildStein.P2
