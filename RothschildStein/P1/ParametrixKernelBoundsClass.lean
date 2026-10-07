-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import RothschildStein.P1.KernelEstimatesHomogeneous

/-!
# Weighted symbol classes for kernel families `A(ξ, η, u)`

The kernel-estimate machinery (`HasWeightedBounds`, `exists_kernel_estimates_of_weighted`) consumes a kernel
family `Ψ ξ η u` that is `C¹` off `u = 0` with the weighted bounds
`|Ψ| ≤ M ρ^d`, `|∂_ξ Ψ| ≤ M ρ^d`, `|∂_{u_j} Ψ| ≤ M ρ^(d - w_j)` (`ρ = ‖u‖` the max gauge). This
file builds the calculus that produces such families from the pieces of the right parametrix
(BB p. 605, Prop 11.61) and of the Sobolev interpolation inequality: the *symbol class* `WtSym G K R k d A` of functions
`A : (ξ, η, u) ↦ ℝ`, jointly smooth off `u = 0`, bounded by `M ρ(u)^d` for `(ξ, η) ∈ K` and
`ρ(u) ≤ R`, whose first `k` derivatives in any of the variables `ξ, η` (degree preserved) and
`u_j` (degree lowered by the weight `w_j`) are again in the class. It is closed under sums,
products (degrees add), lowering the degree, reflection `(ξ, η, u) ↦ (η, ξ, -u)`, and under
differentiation along a vector field whose coordinates have the matching degrees
(`WtSym.field`), which then lowers the degree by the field's weight.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology BigOperators
namespace RothschildStein.P1

variable {N : ℕ}

/-- The space `(ξ, η, u)` of kernel families. -/
abbrev KZ (N : ℕ) : Type := (Fin N → ℝ) × (Fin N → ℝ) × (Fin N → ℝ)

/-- The derivative letters: coordinates of `ξ`, of `η`, and of `u`. -/
abbrev KLetter (N : ℕ) : Type := Fin N ⊕ Fin N ⊕ Fin N

/-- The coordinate direction of a letter in `(ξ, η, u)` space. -/
def symDir : KLetter N → KZ N
  | Sum.inl l => (Pi.single l 1, 0, 0)
  | Sum.inr (Sum.inl l) => (0, Pi.single l 1, 0)
  | Sum.inr (Sum.inr j) => (0, 0, Pi.single j 1)

/-- The weight of a letter: `0` for parameters, `w_j` for `u_j`. -/
def symWt (G : HomogeneousGroup N) : KLetter N → ℤ
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl _) => 0
  | Sum.inr (Sum.inr j) => (G.weight j : ℤ)

/-- The coordinate of a vector of `(ξ, η, u)` space attached to a letter. -/
def symCoord : KLetter N → KZ N → ℝ
  | Sum.inl l, v => v.1 l
  | Sum.inr (Sum.inl l), v => v.2.1 l
  | Sum.inr (Sum.inr j), v => v.2.2 j

/-- A vector is the sum of its coordinates times the coordinate directions. -/
theorem sum_symCoord_smul_symDir (v : KZ N) : ∑ s : KLetter N, symCoord s v • symDir s = v := by
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · funext i
    simp [symCoord, symDir, Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
  · funext i
    simp [symCoord, symDir, Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
  · funext i
    simp [symCoord, symDir, Prod.snd_sum, Finset.sum_apply, Pi.single_apply]

/-- **Weighted symbol class.** `WtSym G K R k d A`: `A` is `C^∞` on `{u ≠ 0}` jointly in
`(ξ, η, u)`, `|A(ξ, η, u)| ≤ M ρ(u)^d` for `(ξ, η) ∈ K` and `0 < ρ(u) ≤ R`, and (for `k + 1`)
the derivative in each letter direction lies in the class of degree `d - (weight of the letter)`
with `k` further derivatives. -/
def WtSym (G : HomogeneousGroup N) (K : Set ((Fin N → ℝ) × (Fin N → ℝ))) (R : ℝ) :
    ℕ → ℤ → (KZ N → ℝ) → Prop
  | 0, d, A => ContDiffOn ℝ (⊤ : ℕ∞) A {z | z.2.2 ≠ 0} ∧
      ∃ M : ℝ, 0 ≤ M ∧ ∀ z : KZ N, (z.1, z.2.1) ∈ K → z.2.2 ≠ 0 → kgauge G z.2.2 ≤ R →
        |A z| ≤ M * kgauge G z.2.2 ^ d
  | k + 1, d, A => WtSym G K R 0 d A ∧
      ∀ s : KLetter N, WtSym G K R k (d - symWt G s) (fun z => fderiv ℝ A z (symDir s))

section Basic

variable {G : HomogeneousGroup N} {K : Set ((Fin N → ℝ) × (Fin N → ℝ))} {R : ℝ}

theorem WtSym.zero_iff {d : ℤ} {A : KZ N → ℝ} :
    WtSym G K R 0 d A ↔ (ContDiffOn ℝ (⊤ : ℕ∞) A {z | z.2.2 ≠ 0} ∧
      ∃ M : ℝ, 0 ≤ M ∧ ∀ z : KZ N, (z.1, z.2.1) ∈ K → z.2.2 ≠ 0 → kgauge G z.2.2 ≤ R →
        |A z| ≤ M * kgauge G z.2.2 ^ d) := by
  rw [WtSym.eq_1]

theorem WtSym.succ_iff {k : ℕ} {d : ℤ} {A : KZ N → ℝ} :
    WtSym G K R (k + 1) d A ↔ (WtSym G K R 0 d A ∧
      ∀ s : KLetter N, WtSym G K R k (d - symWt G s) (fun z => fderiv ℝ A z (symDir s))) := by
  rw [WtSym.eq_2]

theorem WtSym.intro_zero {d : ℤ} {A : KZ N → ℝ} (hs : ContDiffOn ℝ (⊤ : ℕ∞) A {z | z.2.2 ≠ 0})
    (hb : ∃ M : ℝ, 0 ≤ M ∧ ∀ z : KZ N, (z.1, z.2.1) ∈ K → z.2.2 ≠ 0 → kgauge G z.2.2 ≤ R →
        |A z| ≤ M * kgauge G z.2.2 ^ d) : WtSym G K R 0 d A := WtSym.zero_iff.2 ⟨hs, hb⟩

theorem WtSym.intro_succ {k : ℕ} {d : ℤ} {A : KZ N → ℝ} (h0 : WtSym G K R 0 d A)
    (hs : ∀ s : KLetter N,
      WtSym G K R k (d - symWt G s) (fun z => fderiv ℝ A z (symDir s))) :
    WtSym G K R (k + 1) d A := WtSym.succ_iff.2 ⟨h0, hs⟩

theorem WtSym.zero_part {k : ℕ} {d : ℤ} {A : KZ N → ℝ} (h : WtSym G K R k d A) :
    WtSym G K R 0 d A := by
  cases k with
  | zero => exact h
  | succ k => exact (WtSym.succ_iff.1 h).1

theorem WtSym.contDiffOn {k : ℕ} {d : ℤ} {A : KZ N → ℝ} (h : WtSym G K R k d A) :
    ContDiffOn ℝ (⊤ : ℕ∞) A {z | z.2.2 ≠ 0} := (WtSym.zero_iff.1 h.zero_part).1

theorem WtSym.bound {k : ℕ} {d : ℤ} {A : KZ N → ℝ} (h : WtSym G K R k d A) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z : KZ N, (z.1, z.2.1) ∈ K → z.2.2 ≠ 0 → kgauge G z.2.2 ≤ R →
        |A z| ≤ M * kgauge G z.2.2 ^ d := (WtSym.zero_iff.1 h.zero_part).2

theorem WtSym.letter {k : ℕ} {d : ℤ} {A : KZ N → ℝ} (h : WtSym G K R (k + 1) d A)
    (s : KLetter N) :
    WtSym G K R k (d - symWt G s) (fun z => fderiv ℝ A z (symDir s)) := (WtSym.succ_iff.1 h).2 s

theorem WtSym.degree_congr {k : ℕ} {d d' : ℤ} (hd : d = d') {A : KZ N → ℝ}
    (h : WtSym G K R k d A) : WtSym G K R k d' A := hd ▸ h

theorem WtSym.mono_k {k k' : ℕ} (hk : k' ≤ k) :
    ∀ {d : ℤ} {A : KZ N → ℝ}, WtSym G K R k d A → WtSym G K R k' d A := by
  induction k generalizing k' with
  | zero =>
    intro d A h
    obtain rfl : k' = 0 := Nat.le_zero.mp hk
    exact h
  | succ k ih =>
    intro d A h
    cases k' with
    | zero => exact h.zero_part
    | succ k' =>
      exact WtSym.intro_succ h.zero_part (fun s => ih (Nat.le_of_succ_le_succ hk) (h.letter s))

theorem WtSym.differentiableAt {k : ℕ} {d : ℤ} {A : KZ N → ℝ} (h : WtSym G K R k d A)
    {z : KZ N} (hz : z.2.2 ≠ 0) : DifferentiableAt ℝ A z :=
  (h.contDiffOn.contDiffAt (isOpen_kernelDomain.mem_nhds (show z ∈ {z : KZ N | z.2.2 ≠ 0} from hz))
    ).differentiableAt (by simp)

/-- The letter derivatives of a smooth function are smooth off `u = 0`. -/
theorem contDiffOn_fderiv_letter {B : KZ N → ℝ} (hB : ContDiffOn ℝ (⊤ : ℕ∞) B {z | z.2.2 ≠ 0})
    (v : KZ N) : ContDiffOn ℝ (⊤ : ℕ∞) (fun z => fderiv ℝ B z v) {z | z.2.2 ≠ 0} :=
  (hB.fderiv_of_isOpen isOpen_kernelDomain (by simp)).clm_apply contDiffOn_const

/-- Replacing a family by one that agrees with it on an open set `S ⊇ {(ξ, η) ∈ K}`
(and off `u = 0`) preserves the class; `B` must itself be smooth off `u = 0`. -/
theorem WtSym.congr_on {S : Set (KZ N)} (hS : IsOpen S)
    (hKS : ∀ z : KZ N, (z.1, z.2.1) ∈ K → z ∈ S) :
    ∀ {k : ℕ} {d : ℤ} {A B : KZ N → ℝ}, ContDiffOn ℝ (⊤ : ℕ∞) B {z | z.2.2 ≠ 0} →
      (∀ z ∈ S, z.2.2 ≠ 0 → B z = A z) → WtSym G K R k d A → WtSym G K R k d B := by
  have h0 : ∀ {d : ℤ} {A B : KZ N → ℝ}, ContDiffOn ℝ (⊤ : ℕ∞) B {z | z.2.2 ≠ 0} →
      (∀ z ∈ S, z.2.2 ≠ 0 → B z = A z) → WtSym G K R 0 d A → WtSym G K R 0 d B := by
    intro d A B hB hAB hA
    refine WtSym.intro_zero hB ?_
    obtain ⟨M, hM0, hM⟩ := hA.bound
    refine ⟨M, hM0, fun z hzK hz hρ => ?_⟩
    rw [hAB z (hKS z hzK) hz]
    exact hM z hzK hz hρ
  intro k
  induction k with
  | zero => exact fun hB hAB hA => h0 hB hAB hA
  | succ k ih =>
    intro d A B hB hAB hA
    refine WtSym.intro_succ (h0 hB hAB hA.zero_part) (fun s => ?_)
    refine ih (contDiffOn_fderiv_letter hB _) (fun z hzS hz => ?_) (hA.letter s)
    have hmem : S ∩ {z : KZ N | z.2.2 ≠ 0} ∈ 𝓝 z :=
      (hS.inter isOpen_kernelDomain).mem_nhds ⟨hzS, hz⟩
    have hev : B =ᶠ[𝓝 z] A := Filter.eventuallyEq_of_mem hmem (fun y hy => hAB y hy.1 hy.2)
    simp only [hev.fderiv_eq]

/-- Replacing a family by one that agrees with it off `u = 0` preserves the class. -/
theorem WtSym.congr {k : ℕ} {d : ℤ} {A B : KZ N → ℝ} (hAB : ∀ z : KZ N, z.2.2 ≠ 0 → B z = A z)
    (hA : WtSym G K R k d A) : WtSym G K R k d B :=
  WtSym.congr_on isOpen_univ (fun _ _ => mem_univ _)
    (hA.contDiffOn.congr (fun z hz => hAB z hz)) (fun z _ hz => hAB z hz) hA

/-- Lowering the degree is allowed (`ρ^d ≤ R^(d-d') ρ^{d'}` for `ρ ≤ R`). -/
theorem WtSym.mono_d (hR : 0 < R) :
    ∀ {k : ℕ} {d d' : ℤ} {A : KZ N → ℝ}, d' ≤ d → WtSym G K R k d A → WtSym G K R k d' A := by
  have h0 : ∀ {d d' : ℤ} {A : KZ N → ℝ}, d' ≤ d → WtSym G K R 0 d A → WtSym G K R 0 d' A := by
    intro d d' A hd hA
    obtain ⟨M, hM0, hM⟩ := hA.bound
    refine WtSym.intro_zero hA.contDiffOn ⟨M * R ^ (d - d'), mul_nonneg hM0 (zpow_pos hR _).le,
      fun z hzK hz hρ => ?_⟩
    have hρpos : 0 < kgauge G z.2.2 := kgauge_pos G hz
    have e1 : kgauge G z.2.2 ^ d = kgauge G z.2.2 ^ d' * kgauge G z.2.2 ^ (d - d') := by
      rw [← zpow_add₀ hρpos.ne']
      congr 1
      ring
    have e2 : kgauge G z.2.2 ^ (d - d') ≤ R ^ (d - d') :=
      kzpow_le_of_nonneg hρpos hρ (by omega)
    calc |A z| ≤ M * kgauge G z.2.2 ^ d := hM z hzK hz hρ
      _ = M * kgauge G z.2.2 ^ (d - d') * kgauge G z.2.2 ^ d' := by rw [e1]; ring
      _ ≤ M * R ^ (d - d') * kgauge G z.2.2 ^ d' :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left e2 hM0) (zpow_pos hρpos _).le
  intro k
  induction k with
  | zero => exact fun hd hA => h0 hd hA
  | succ k ih =>
    exact fun hd hA => WtSym.intro_succ (h0 hd hA.zero_part)
      (fun s => ih (by linarith) (hA.letter s))

theorem WtSym.zero_fun : ∀ {k : ℕ} {d : ℤ}, WtSym G K R k d (fun _ : KZ N => (0 : ℝ)) := by
  intro k
  induction k with
  | zero =>
    intro d
    exact WtSym.intro_zero contDiffOn_const ⟨0, le_rfl, fun z _ _ _ => by simp⟩
  | succ k ih =>
    intro d
    refine WtSym.intro_succ (WtSym.intro_zero contDiffOn_const ⟨0, le_rfl, fun z _ _ _ => by simp⟩)
      (fun s => ?_)
    have h : (fun z : KZ N => fderiv ℝ (fun _ : KZ N => (0 : ℝ)) z (symDir s)) =
        fun _ => (0 : ℝ) := by
      funext z
      simp
    rw [h]
    exact ih

theorem WtSym.add_zero_part {d : ℤ} {A B : KZ N → ℝ} (hA : WtSym G K R 0 d A)
    (hB : WtSym G K R 0 d B) : WtSym G K R 0 d (fun z => A z + B z) := by
  refine WtSym.intro_zero (hA.contDiffOn.add hB.contDiffOn) ?_
  obtain ⟨M₁, h₁0, h₁⟩ := hA.bound
  obtain ⟨M₂, h₂0, h₂⟩ := hB.bound
  refine ⟨M₁ + M₂, add_nonneg h₁0 h₂0, fun z hzK hz hρ => ?_⟩
  calc |A z + B z| ≤ |A z| + |B z| := abs_add_le _ _
    _ ≤ M₁ * kgauge G z.2.2 ^ d + M₂ * kgauge G z.2.2 ^ d :=
        add_le_add (h₁ z hzK hz hρ) (h₂ z hzK hz hρ)
    _ = (M₁ + M₂) * kgauge G z.2.2 ^ d := by ring

theorem WtSym.add :
    ∀ {k : ℕ} {d : ℤ} {A B : KZ N → ℝ}, WtSym G K R k d A → WtSym G K R k d B →
      WtSym G K R k d (fun z => A z + B z) := by
  intro k
  induction k with
  | zero => intro d A B hA hB; exact WtSym.add_zero_part hA hB
  | succ k ih =>
    intro d A B hA hB
    refine WtSym.intro_succ (WtSym.add_zero_part hA.zero_part hB.zero_part) (fun s => ?_)
    refine WtSym.congr (fun z hz => ?_) (ih (hA.letter s) (hB.letter s))
    have hAd := hA.differentiableAt hz
    have hBd := hB.differentiableAt hz
    rw [(hAd.hasFDerivAt.fun_add hBd.hasFDerivAt).fderiv]
    rfl

theorem WtSym.sum {ι : Type*} {k : ℕ} {d : ℤ} (s : Finset ι) (A : ι → KZ N → ℝ)
    (h : ∀ i ∈ s, WtSym G K R k d (A i)) : WtSym G K R k d (fun z => ∑ i ∈ s, A i z) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have e : (fun z : KZ N => ∑ i ∈ (∅ : Finset ι), A i z) = fun _ => (0 : ℝ) := by
      funext z
      simp
    rw [e]
    exact WtSym.zero_fun
  | insert a s ha ih =>
    have e : (fun z : KZ N => ∑ i ∈ insert a s, A i z) = fun z => A a z + ∑ i ∈ s, A i z := by
      funext z
      rw [Finset.sum_insert ha]
    rw [e]
    exact WtSym.add (h a (Finset.mem_insert_self a s))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

theorem WtSym.smul_zero_part (a : ℝ) {d : ℤ} {A : KZ N → ℝ} (hA : WtSym G K R 0 d A) :
    WtSym G K R 0 d (fun z => a * A z) := by
  refine WtSym.intro_zero (contDiffOn_const.mul hA.contDiffOn) ?_
  obtain ⟨M, hM0, hM⟩ := hA.bound
  refine ⟨|a| * M, mul_nonneg (abs_nonneg a) hM0, fun z hzK hz hρ => ?_⟩
  rw [abs_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hM z hzK hz hρ) (abs_nonneg a)

theorem WtSym.smul (a : ℝ) :
    ∀ {k : ℕ} {d : ℤ} {A : KZ N → ℝ}, WtSym G K R k d A → WtSym G K R k d (fun z => a * A z) := by
  intro k
  induction k with
  | zero => intro d A hA; exact WtSym.smul_zero_part a hA
  | succ k ih =>
    intro d A hA
    refine WtSym.intro_succ (WtSym.smul_zero_part a hA.zero_part) (fun s => ?_)
    refine WtSym.congr (fun z hz => ?_) (ih (hA.letter s))
    have hAd := hA.differentiableAt hz
    rw [(hAd.hasFDerivAt.const_mul a).fderiv]
    simp

theorem WtSym.mul_zero_part {d e : ℤ} {A B : KZ N → ℝ} (hA : WtSym G K R 0 d A)
    (hB : WtSym G K R 0 e B) : WtSym G K R 0 (d + e) (fun z => A z * B z) := by
  refine WtSym.intro_zero (hA.contDiffOn.mul hB.contDiffOn) ?_
  obtain ⟨M₁, h₁0, h₁⟩ := hA.bound
  obtain ⟨M₂, h₂0, h₂⟩ := hB.bound
  refine ⟨M₁ * M₂, mul_nonneg h₁0 h₂0, fun z hzK hz hρ => ?_⟩
  have hν : kgauge G z.2.2 ≠ 0 := (kgauge_pos G hz).ne'
  have ha := h₁ z hzK hz hρ
  have hb := h₂ z hzK hz hρ
  rw [abs_mul, zpow_add₀ hν]
  calc |A z| * |B z| ≤ (M₁ * kgauge G z.2.2 ^ d) * (M₂ * kgauge G z.2.2 ^ e) :=
        mul_le_mul ha hb (abs_nonneg _) ((abs_nonneg _).trans ha)
    _ = M₁ * M₂ * (kgauge G z.2.2 ^ d * kgauge G z.2.2 ^ e) := by ring

/-- Products: degrees add. -/
theorem WtSym.mul :
    ∀ {k : ℕ} {d e : ℤ} {A B : KZ N → ℝ}, WtSym G K R k d A → WtSym G K R k e B →
      WtSym G K R k (d + e) (fun z => A z * B z) := by
  intro k
  induction k with
  | zero => intro d e A B hA hB; exact WtSym.mul_zero_part hA hB
  | succ k ih =>
    intro d e A B hA hB
    refine WtSym.intro_succ (WtSym.mul_zero_part hA.zero_part hB.zero_part) (fun s => ?_)
    have h1 := ih (hA.letter s) (WtSym.mono_k (Nat.le_succ k) hB)
    have h2 := (ih (WtSym.mono_k (Nat.le_succ k) hA) (hB.letter s)).degree_congr
      (show d + (e - symWt G s) = d - symWt G s + e by ring)
    have h3 := (WtSym.add (G := G) h1 h2).degree_congr
      (show d - symWt G s + e = d + e - symWt G s by ring)
    refine WtSym.congr (fun z hz => ?_) h3
    have hAd := hA.differentiableAt hz
    have hBd := hB.differentiableAt hz
    rw [(hAd.hasFDerivAt.fun_mul hBd.hasFDerivAt).fderiv]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring

/-- Differentiation along a vector field `V` in `(ξ, η, u)` space whose letter
coordinates have degree `wt s - e` lowers the degree by `e`. -/
theorem WtSym.field {k : ℕ} {d e : ℤ} (V : KZ N → KZ N)
    (hV : ∀ s : KLetter N, WtSym G K R k (symWt G s - e) (fun z => symCoord s (V z)))
    {A : KZ N → ℝ} (hA : WtSym G K R (k + 1) d A) :
    WtSym G K R k (d - e) (fun z => fderiv ℝ A z (V z)) := by
  have h : WtSym G K R k (d - e)
      (fun z => ∑ s : KLetter N, symCoord s (V z) * fderiv ℝ A z (symDir s)) := by
    refine WtSym.sum Finset.univ _ (fun s _ => ?_)
    have h1 := WtSym.mul (hV s) (hA.letter s)
    rw [show symWt G s - e + (d - symWt G s) = d - e by ring] at h1
    exact h1
  refine WtSym.congr (fun z _ => ?_) h
  conv_lhs => rw [← sum_symCoord_smul_symDir (V z)]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [map_smul, smul_eq_mul]

/-- The reflection `(ξ, η, u) ↦ (η, ξ, -u)` as a continuous linear map. -/
def reflCLM (N : ℕ) : KZ N →L[ℝ] KZ N :=
  ContinuousLinearMap.prod
    ((ContinuousLinearMap.fst ℝ (Fin N → ℝ) (Fin N → ℝ)).comp
      (ContinuousLinearMap.snd ℝ (Fin N → ℝ) ((Fin N → ℝ) × (Fin N → ℝ))))
    (ContinuousLinearMap.prod
      (ContinuousLinearMap.fst ℝ (Fin N → ℝ) ((Fin N → ℝ) × (Fin N → ℝ)))
      (-((ContinuousLinearMap.snd ℝ (Fin N → ℝ) (Fin N → ℝ)).comp
        (ContinuousLinearMap.snd ℝ (Fin N → ℝ) ((Fin N → ℝ) × (Fin N → ℝ))))))

theorem reflCLM_apply (z : KZ N) : reflCLM N z = (z.2.1, z.1, -z.2.2) := rfl

/-- Chain rule for the reflection. -/
theorem fderiv_refl {A : KZ N → ℝ} {z : KZ N} (hA : DifferentiableAt ℝ A (reflCLM N z))
    (v : KZ N) :
    fderiv ℝ (fun z : KZ N => A (z.2.1, z.1, -z.2.2)) z v =
      fderiv ℝ A (reflCLM N z) (reflCLM N v) := by
  have h : fderiv ℝ (A ∘ reflCLM N) z =
      (fderiv ℝ A (reflCLM N z)).comp (reflCLM N) := by
    rw [fderiv_comp z hA (reflCLM N).differentiableAt, ContinuousLinearMap.fderiv]
  exact congrArg (fun L => L v) h

/-- **Reflection.** If `A ∈ WtSym` on `K'` and `K` is mapped into `K'` by exchanging the
two parameters, then `(ξ, η, u) ↦ A(η, ξ, -u)` is in the class on `K` (same degree: the gauge
is even; the letters `ξ_l ↔ η_l` are exchanged and `∂_{u_j}` changes sign). -/
theorem WtSym.reflect {K' : Set ((Fin N → ℝ) × (Fin N → ℝ))} (hK : ∀ p ∈ K, (p.2, p.1) ∈ K') :
    ∀ {k : ℕ} {d : ℤ} {A : KZ N → ℝ}, WtSym G K' R k d A →
      WtSym G K R k d (fun z => A (z.2.1, z.1, -z.2.2)) := by
  have hcd : ContDiff ℝ (⊤ : ℕ∞) (fun z : KZ N => ((z.2.1, z.1, -z.2.2) : KZ N)) :=
    contDiff_snd.fst.prodMk (contDiff_fst.prodMk contDiff_snd.snd.neg)
  have h0 : ∀ {d : ℤ} {A : KZ N → ℝ}, WtSym G K' R 0 d A →
      WtSym G K R 0 d (fun z => A (z.2.1, z.1, -z.2.2)) := by
    intro d A hA
    refine WtSym.intro_zero ?_ ?_
    · exact hA.contDiffOn.comp hcd.contDiffOn (fun z hz => by
        simpa using (show z.2.2 ≠ 0 from hz))
    · obtain ⟨M, hM0, hM⟩ := hA.bound
      refine ⟨M, hM0, fun z hzK hz hρ => ?_⟩
      have := hM (z.2.1, z.1, -z.2.2) (hK _ hzK) (neg_ne_zero.mpr hz)
        (by rw [kgauge_neg]; exact hρ)
      simpa [kgauge_neg] using this
  intro k
  induction k with
  | zero => exact fun hA => h0 hA
  | succ k ih =>
    intro d A hA
    refine WtSym.intro_succ (h0 hA.zero_part) (fun s => ?_)
    have hdiff : ∀ z : KZ N, z.2.2 ≠ 0 → DifferentiableAt ℝ A (reflCLM N z) := fun z hz =>
      hA.differentiableAt (show (reflCLM N z).2.2 ≠ 0 from neg_ne_zero.mpr hz)
    rcases s with l | l | j
    · have h1 := (ih (hA.letter (Sum.inr (Sum.inl l)))).degree_congr
        (show d - symWt G (Sum.inr (Sum.inl l)) = d - symWt G (Sum.inl l) by simp [symWt])
      refine WtSym.congr (fun z hz => ?_) h1
      rw [fderiv_refl (hdiff z hz)]
      have hr : reflCLM N (symDir (Sum.inl l)) = symDir (Sum.inr (Sum.inl l)) := by
        simp [symDir, reflCLM_apply]
      rw [hr]
      rfl
    · have h1 := (ih (hA.letter (Sum.inl l))).degree_congr
        (show d - symWt G (Sum.inl l) = d - symWt G (Sum.inr (Sum.inl l)) by simp [symWt])
      refine WtSym.congr (fun z hz => ?_) h1
      rw [fderiv_refl (hdiff z hz)]
      have hr : reflCLM N (symDir (Sum.inr (Sum.inl l))) = symDir (Sum.inl l) := by
        simp [symDir, reflCLM_apply]
      rw [hr]
      rfl
    · have h1 := WtSym.smul (-1) (ih (hA.letter (Sum.inr (Sum.inr j))))
      refine WtSym.congr (fun z hz => ?_) h1
      rw [fderiv_refl (hdiff z hz)]
      have hr : reflCLM N (symDir (Sum.inr (Sum.inr j))) = -symDir (Sum.inr (Sum.inr j)) := by
        simp [symDir, reflCLM_apply]
      rw [hr, map_neg]
      show -(fderiv ℝ A (reflCLM N z) (symDir (Sum.inr (Sum.inr j)))) =
        -1 * (fderiv ℝ A (reflCLM N z) (symDir (Sum.inr (Sum.inr j))))
      ring

/-- A family vanishing identically on `{η ∈ W}` (`W` open) has the class on every
parameter set that splits into a part where the class holds and a part inside `W`. -/
theorem WtSym.of_support {W : Set (Fin N → ℝ)} (hW : IsOpen W)
    {K₁ : Set ((Fin N → ℝ) × (Fin N → ℝ))} (hK : ∀ p ∈ K, p ∈ K₁ ∨ p.2 ∈ W) :
    ∀ {k : ℕ} {d : ℤ} {A : KZ N → ℝ}, (∀ z : KZ N, z.2.1 ∈ W → A z = 0) →
      WtSym G K₁ R k d A → WtSym G K R k d A := by
  have h0 : ∀ {d : ℤ} {A : KZ N → ℝ}, (∀ z : KZ N, z.2.1 ∈ W → A z = 0) →
      WtSym G K₁ R 0 d A → WtSym G K R 0 d A := by
    intro d A hA0 hA
    refine WtSym.intro_zero hA.contDiffOn ?_
    obtain ⟨M, hM0, hM⟩ := hA.bound
    refine ⟨M, hM0, fun z hzK hz hρ => ?_⟩
    rcases hK _ hzK with h | h
    · exact hM z h hz hρ
    · rw [hA0 z h, abs_zero]
      exact mul_nonneg hM0 (zpow_pos (kgauge_pos G hz) d).le
  intro k
  induction k with
  | zero => exact fun hA0 hA => h0 hA0 hA
  | succ k ih =>
    intro d A hA0 hA
    refine WtSym.intro_succ (h0 hA0 hA.zero_part) (fun s => ih (fun z hz => ?_) (hA.letter s))
    have hopen : IsOpen {z : KZ N | z.2.1 ∈ W} := hW.preimage (continuous_fst.comp continuous_snd)
    have hev : A =ᶠ[𝓝 z] fun _ => (0 : ℝ) :=
      Filter.eventuallyEq_of_mem (hopen.mem_nhds hz) (fun y hy => hA0 y hy)
    simp [hev.fderiv_eq]

/-- **Weighted bounds from a symbol class.** If a family `A(ξ, η, u)` lies in the class
`WtSym` of degree `d` (one derivative) on `L × L` for every compact `L` and radius `R`, then
`Ψ ξ η u = A(ξ, η, u)` satisfies the weighted bounds `HasWeightedBounds` of the kernel-estimate machinery. -/
theorem hasWeightedBounds_of_wtSym {d : ℤ} {A : KZ N → ℝ}
    (hA : ∀ L : Set (Fin N → ℝ), IsCompact L → ∀ R : ℝ, 0 < R → WtSym G (L ×ˢ L) R 1 d A) :
    HasWeightedBounds G d (fun ξ η u => A (ξ, η, u)) := by
  intro L hL R
  have hRpos : 0 < max R 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hAL := hA L hL (max R 1) hRpos
  obtain ⟨M₀, hM₀0, hM₀⟩ := hAL.bound
  choose M hM0 hM using fun s : KLetter N => (hAL.letter s).bound
  set Mt : ℝ := M₀ + ∑ s, M s with hMt
  have hsum0 : 0 ≤ ∑ s, M s := Finset.sum_nonneg (fun s _ => hM0 s)
  have hMt0 : 0 ≤ Mt := add_nonneg hM₀0 hsum0
  have hMs : ∀ s, M s ≤ Mt := fun s => by
    have := Finset.single_le_sum (f := M) (fun s _ => hM0 s) (Finset.mem_univ s)
    linarith
  refine ⟨Mt, hMt0, fun ξ hξ η hη u hu hρ => ?_⟩
  have hρR : kgauge G u ≤ max R 1 := hρ.trans (le_max_left _ _)
  have hρpos : 0 < kgauge G u := kgauge_pos G hu
  have hzK : (((ξ, η, u) : KZ N).1, ((ξ, η, u) : KZ N).2.1) ∈ L ×ˢ L := ⟨hξ, hη⟩
  have hk : kernelUncurry (fun ξ η u => A (ξ, η, u)) = A := rfl
  refine ⟨?_, fun a => ?_, fun j => ?_⟩
  · have h := hM₀ (ξ, η, u) hzK hu hρR
    exact h.trans (mul_le_mul_of_nonneg_right (by linarith [hsum0]) (zpow_pos hρpos d).le)
  · rw [hk]
    have hdec : ((a, 0, 0) : KZ N) = ∑ l : Fin N, a l • symDir (Sum.inl l) := by
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · funext i
        simp [symDir, Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
      · simp [symDir, Prod.snd_sum]
      · simp [symDir, Prod.snd_sum]
    rw [hdec, map_sum]
    have hl : ∀ l : Fin N, |fderiv ℝ A (ξ, η, u) (a l • symDir (Sum.inl l))| ≤
        ‖a‖ * (M (Sum.inl l) * kgauge G u ^ d) := by
      intro l
      have h := hM (Sum.inl l) (ξ, η, u) hzK hu hρR
      have e : d - symWt G (Sum.inl l) = d := by simp [symWt]
      rw [e] at h
      rw [map_smul, smul_eq_mul, abs_mul]
      have hal : |a l| ≤ ‖a‖ := by
        have := norm_le_pi_norm a l
        rwa [Real.norm_eq_abs] at this
      exact mul_le_mul hal h (abs_nonneg _) (norm_nonneg _)
    have hsplit : ∑ l : Fin N, M (Sum.inl l) ≤ Mt := by
      have h1 : ∑ s, M s = ∑ l : Fin N, M (Sum.inl l) +
          (∑ l : Fin N, M (Sum.inr (Sum.inl l)) + ∑ j : Fin N, M (Sum.inr (Sum.inr j))) := by
        rw [Fintype.sum_sum_type, Fintype.sum_sum_type]
      have h2 : 0 ≤ ∑ l : Fin N, M (Sum.inr (Sum.inl l)) :=
        Finset.sum_nonneg (fun l _ => hM0 _)
      have h3 : 0 ≤ ∑ j : Fin N, M (Sum.inr (Sum.inr j)) := Finset.sum_nonneg (fun j _ => hM0 _)
      linarith
    calc |∑ l : Fin N, fderiv ℝ A (ξ, η, u) (a l • symDir (Sum.inl l))|
        ≤ ∑ l : Fin N, |fderiv ℝ A (ξ, η, u) (a l • symDir (Sum.inl l))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ l : Fin N, ‖a‖ * (M (Sum.inl l) * kgauge G u ^ d) := Finset.sum_le_sum (fun l _ => hl l)
      _ = ‖a‖ * kgauge G u ^ d * ∑ l : Fin N, M (Sum.inl l) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun l _ => by ring)
      _ ≤ ‖a‖ * kgauge G u ^ d * Mt :=
          mul_le_mul_of_nonneg_left hsplit (mul_nonneg (norm_nonneg _) (zpow_pos hρpos d).le)
      _ = Mt * kgauge G u ^ d * ‖a‖ := by ring
  · rw [hk]
    have h := hM (Sum.inr (Sum.inr j)) (ξ, η, u) hzK hu hρR
    have e : d - symWt G (Sum.inr (Sum.inr j)) = d - (G.weight j : ℤ) := rfl
    rw [e] at h
    exact h.trans (mul_le_mul_of_nonneg_right (hMs _) (zpow_pos hρpos _).le)

end Basic

end RothschildStein.P1
