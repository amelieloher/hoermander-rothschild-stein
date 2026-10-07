-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib

/-!
# Weighted symbol classes (support file)

Elementary bookkeeping for the radial cutoff construction (BB Lem 11.36, p. 579): a family
`A η u` (parameter `η` in a fixed set `Kc`, point `u` of the punctured gauge ball) belongs to the
class `Sym c k d` when it is smooth in `u`, satisfies `|A η u| ≤ C ν(u)^d` uniformly in `η`, and
(for `k + 1`) every coordinate partial lies in `Sym c k (d - ω_j)`. The classes are closed under
sums, products (degrees add) and under a vector field whose coordinates have degree
`ω_j - w`, which then lowers the degree by `w`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set Filter
open scoped Topology
namespace RothschildStein.P2

variable {N : ℕ}

/-- The punctured open gauge ball `{u | 0 < ν u < ρ}`. -/
def punctBall (ν : (Fin N → ℝ) → ℝ) (ρ : ℝ) : Set (Fin N → ℝ) :=
  {u | 0 < ν u ∧ ν u < ρ}

theorem isOpen_punctBall {ν : (Fin N → ℝ) → ℝ} (hν : Continuous ν) (ρ : ℝ) :
    IsOpen (punctBall ν ρ) :=
  (isOpen_lt continuous_const hν).inter (isOpen_lt hν continuous_const)

/-- The coordinate partial derivative `∂_j f`. -/
def pdv (j : Fin N) (f : (Fin N → ℝ) → ℝ) : (Fin N → ℝ) → ℝ :=
  fun u => fderiv ℝ f u (Pi.single j 1)

/-- The data of a symbol class: coordinate weights, the gauge, the parameter set and the
radius of the punctured ball. -/
structure SymCtx (N : ℕ) where
  /-- Coordinate weights. -/
  ω : Fin N → ℕ
  /-- The gauge. -/
  ν : (Fin N → ℝ) → ℝ
  /-- The parameter set. -/
  Kc : Set (Fin N → ℝ)
  /-- The radius. -/
  ρ : ℝ

/-- The punctured ball of a symbol context. -/
def SymCtx.P (c : SymCtx N) : Set (Fin N → ℝ) := punctBall c.ν c.ρ

/-- A context is good when the gauge is continuous and the radius lies in `(0, 1]`. -/
structure SymCtx.Good (c : SymCtx N) : Prop where
  cont : Continuous c.ν
  ρ_pos : 0 < c.ρ
  ρ_le : c.ρ ≤ 1

theorem SymCtx.Good.isOpen {c : SymCtx N} (h : c.Good) : IsOpen c.P :=
  isOpen_punctBall h.cont c.ρ

theorem SymCtx.Good.ν_pos {c : SymCtx N} {u : Fin N → ℝ} (hu : u ∈ c.P) : 0 < c.ν u := hu.1

theorem SymCtx.Good.ν_lt_one {c : SymCtx N} (h : c.Good) {u : Fin N → ℝ} (hu : u ∈ c.P) :
    c.ν u < 1 := hu.2.trans_le h.ρ_le

/-- The weighted symbol class of degree `d` with `k` further derivatives. -/
def Sym (c : SymCtx N) : ℕ → ℤ → ((Fin N → ℝ) → (Fin N → ℝ) → ℝ) → Prop
  | 0, d, A => (∀ η ∈ c.Kc, ContDiffOn ℝ (⊤ : ℕ∞) (A η) c.P) ∧
      ∃ C : ℝ, ∀ η ∈ c.Kc, ∀ u ∈ c.P, |A η u| ≤ C * c.ν u ^ d
  | k + 1, d, A => Sym c 0 d A ∧ ∀ j : Fin N, Sym c k (d - c.ω j) (fun η => pdv j (A η))

variable (c : SymCtx N)

theorem Sym.zero_iff {d : ℤ} {A : (Fin N → ℝ) → (Fin N → ℝ) → ℝ} :
    Sym c 0 d A ↔ ((∀ η ∈ c.Kc, ContDiffOn ℝ (⊤ : ℕ∞) (A η) c.P) ∧
      ∃ C : ℝ, ∀ η ∈ c.Kc, ∀ u ∈ c.P, |A η u| ≤ C * c.ν u ^ d) := by
  rw [Sym.eq_1]

theorem Sym.succ_iff {k : ℕ} {d : ℤ} {A : (Fin N → ℝ) → (Fin N → ℝ) → ℝ} :
    Sym c (k + 1) d A ↔
      (Sym c 0 d A ∧ ∀ j : Fin N, Sym c k (d - c.ω j) (fun η => pdv j (A η))) := by
  rw [Sym.eq_2]

theorem Sym.intro_zero {d : ℤ} {A : (Fin N → ℝ) → (Fin N → ℝ) → ℝ}
    (hs : ∀ η ∈ c.Kc, ContDiffOn ℝ (⊤ : ℕ∞) (A η) c.P)
    (hb : ∃ C : ℝ, ∀ η ∈ c.Kc, ∀ u ∈ c.P, |A η u| ≤ C * c.ν u ^ d) : Sym c 0 d A :=
  (Sym.zero_iff c).2 ⟨hs, hb⟩

theorem Sym.intro_succ {k : ℕ} {d : ℤ} {A : (Fin N → ℝ) → (Fin N → ℝ) → ℝ}
    (h0 : Sym c 0 d A) (hj : ∀ j : Fin N, Sym c k (d - c.ω j) (fun η => pdv j (A η))) :
    Sym c (k + 1) d A :=
  (Sym.succ_iff c).2 ⟨h0, hj⟩

theorem Sym.zero_part {k : ℕ} {d : ℤ} {A : (Fin N → ℝ) → (Fin N → ℝ) → ℝ}
    (h : Sym c k d A) : Sym c 0 d A := by
  cases k with
  | zero => exact h
  | succ k => exact ((Sym.succ_iff c).1 h).1

theorem Sym.smooth {k : ℕ} {d : ℤ} {A : (Fin N → ℝ) → (Fin N → ℝ) → ℝ}
    (h : Sym c k d A) {η : Fin N → ℝ} (hη : η ∈ c.Kc) :
    ContDiffOn ℝ (⊤ : ℕ∞) (A η) c.P :=
  ((Sym.zero_iff c).1 (h.zero_part c)).1 η hη

theorem Sym.bound {k : ℕ} {d : ℤ} {A : (Fin N → ℝ) → (Fin N → ℝ) → ℝ}
    (h : Sym c k d A) : ∃ C : ℝ, ∀ η ∈ c.Kc, ∀ u ∈ c.P, |A η u| ≤ C * c.ν u ^ d :=
  ((Sym.zero_iff c).1 (h.zero_part c)).2

theorem Sym.pd {k : ℕ} {d : ℤ} {A : (Fin N → ℝ) → (Fin N → ℝ) → ℝ}
    (h : Sym c (k + 1) d A) (j : Fin N) :
    Sym c k (d - c.ω j) (fun η => pdv j (A η)) :=
  ((Sym.succ_iff c).1 h).2 j

theorem Sym.mono_k {k k' : ℕ} (hk : k' ≤ k) :
    ∀ {d : ℤ} {A : (Fin N → ℝ) → (Fin N → ℝ) → ℝ}, Sym c k d A → Sym c k' d A := by
  induction k generalizing k' with
  | zero =>
    intro d A h
    obtain rfl : k' = 0 := Nat.le_zero.mp hk
    exact h
  | succ k ih =>
    intro d A h
    cases k' with
    | zero => exact h.zero_part c
    | succ k' =>
      exact Sym.intro_succ c (h.zero_part c)
        (fun j => ih (Nat.le_of_succ_le_succ hk) (h.pd c j))

theorem Sym.diff (hc : c.Good) {k : ℕ} {d : ℤ} {A : (Fin N → ℝ) → (Fin N → ℝ) → ℝ}
    (h : Sym c k d A) {η : Fin N → ℝ} (hη : η ∈ c.Kc) {u : Fin N → ℝ} (hu : u ∈ c.P) :
    DifferentiableAt ℝ (A η) u :=
  ((h.smooth c hη).contDiffAt (hc.isOpen.mem_nhds hu)).differentiableAt (by simp)

theorem Sym.congr_zero {d : ℤ} {A B : (Fin N → ℝ) → (Fin N → ℝ) → ℝ}
    (hAB : ∀ η ∈ c.Kc, ∀ u ∈ c.P, B η u = A η u) (hA : Sym c 0 d A) : Sym c 0 d B := by
  refine Sym.intro_zero c (fun η hη => (hA.smooth c hη).congr (fun u hu => hAB η hη u hu)) ?_
  obtain ⟨C, hC⟩ := hA.bound c
  exact ⟨C, fun η hη u hu => by rw [hAB η hη u hu]; exact hC η hη u hu⟩

theorem Sym.pdv_congr (hc : c.Good) {A B : (Fin N → ℝ) → (Fin N → ℝ) → ℝ}
    (hAB : ∀ η ∈ c.Kc, ∀ u ∈ c.P, B η u = A η u) (j : Fin N) :
    ∀ η ∈ c.Kc, ∀ u ∈ c.P, pdv j (B η) u = pdv j (A η) u := by
  intro η hη u hu
  have h : B η =ᶠ[𝓝 u] A η :=
    Filter.eventuallyEq_of_mem (hc.isOpen.mem_nhds hu) (fun v hv => hAB η hη v hv)
  simp only [pdv, h.fderiv_eq]

theorem Sym.congr (hc : c.Good) :
    ∀ {k : ℕ} {d : ℤ} {A B : (Fin N → ℝ) → (Fin N → ℝ) → ℝ},
      (∀ η ∈ c.Kc, ∀ u ∈ c.P, B η u = A η u) → Sym c k d A → Sym c k d B := by
  intro k
  induction k with
  | zero => intro d A B hAB hA; exact Sym.congr_zero c hAB hA
  | succ k ih =>
    intro d A B hAB hA
    exact Sym.intro_succ c (Sym.congr_zero c hAB (hA.zero_part c))
      (fun j => ih (Sym.pdv_congr c hc hAB j) (hA.pd c j))

theorem Sym.zero :
    ∀ {k : ℕ} {d : ℤ}, Sym c k d (fun _ _ => (0 : ℝ)) := by
  intro k
  induction k with
  | zero =>
    intro d
    exact Sym.intro_zero c (fun _ _ => contDiffOn_const) ⟨0, fun η _ u _ => by simp⟩
  | succ k ih =>
    intro d
    refine Sym.intro_succ c (Sym.intro_zero c (fun _ _ => contDiffOn_const)
      ⟨0, fun η _ u _ => by simp⟩) (fun j => ?_)
    have h : (fun (η : Fin N → ℝ) => pdv j ((fun (_ : Fin N → ℝ) (_ : Fin N → ℝ) => (0 : ℝ)) η)) =
        fun _ _ => (0 : ℝ) := by
      funext η u
      simp [pdv]
    rw [h]
    exact ih

theorem Sym.add_zero_part {d : ℤ} {A B : (Fin N → ℝ) → (Fin N → ℝ) → ℝ}
    (hA : Sym c 0 d A) (hB : Sym c 0 d B) : Sym c 0 d (fun η u => A η u + B η u) := by
  refine Sym.intro_zero c (fun η hη => (hA.smooth c hη).add (hB.smooth c hη)) ?_
  obtain ⟨C₁, h₁⟩ := hA.bound c
  obtain ⟨C₂, h₂⟩ := hB.bound c
  refine ⟨C₁ + C₂, fun η hη u hu => ?_⟩
  calc |A η u + B η u| ≤ |A η u| + |B η u| := abs_add_le _ _
    _ ≤ C₁ * c.ν u ^ d + C₂ * c.ν u ^ d := add_le_add (h₁ η hη u hu) (h₂ η hη u hu)
    _ = (C₁ + C₂) * c.ν u ^ d := by ring

theorem Sym.mul_zero_part {d e : ℤ} {A B : (Fin N → ℝ) → (Fin N → ℝ) → ℝ}
    (hA : Sym c 0 d A) (hB : Sym c 0 e B) : Sym c 0 (d + e) (fun η u => A η u * B η u) := by
  refine Sym.intro_zero c (fun η hη => (hA.smooth c hη).mul (hB.smooth c hη)) ?_
  obtain ⟨C₁, h₁⟩ := hA.bound c
  obtain ⟨C₂, h₂⟩ := hB.bound c
  refine ⟨C₁ * C₂, fun η hη u hu => ?_⟩
  have hν : c.ν u ≠ 0 := (SymCtx.Good.ν_pos hu).ne'
  have ha := h₁ η hη u hu
  have hb := h₂ η hη u hu
  rw [abs_mul, zpow_add₀ hν]
  calc |A η u| * |B η u| ≤ (C₁ * c.ν u ^ d) * (C₂ * c.ν u ^ e) :=
        mul_le_mul ha hb (abs_nonneg _) ((abs_nonneg _).trans ha)
    _ = C₁ * C₂ * (c.ν u ^ d * c.ν u ^ e) := by ring

theorem Sym.mono_d_zero (hc : c.Good) {d d' : ℤ} {A : (Fin N → ℝ) → (Fin N → ℝ) → ℝ}
    (hd : d' ≤ d) (hA : Sym c 0 d A) : Sym c 0 d' A := by
  refine Sym.intro_zero c (fun η hη => hA.smooth c hη) ?_
  obtain ⟨C, hC⟩ := hA.bound c
  refine ⟨|C|, fun η hη u hu => ?_⟩
  have hν := SymCtx.Good.ν_pos hu
  have hpow : c.ν u ^ d ≤ c.ν u ^ d' :=
    zpow_le_zpow_right_of_le_one₀ hν (SymCtx.Good.ν_lt_one hc hu).le hd
  calc |A η u| ≤ C * c.ν u ^ d := hC η hη u hu
    _ ≤ |C| * c.ν u ^ d := mul_le_mul_of_nonneg_right (le_abs_self C) (zpow_pos hν d).le
    _ ≤ |C| * c.ν u ^ d' := mul_le_mul_of_nonneg_left hpow (abs_nonneg C)

theorem Sym.add (hc : c.Good) :
    ∀ {k : ℕ} {d : ℤ} {A B : (Fin N → ℝ) → (Fin N → ℝ) → ℝ},
      Sym c k d A → Sym c k d B → Sym c k d (fun η u => A η u + B η u) := by
  intro k
  induction k with
  | zero => intro d A B hA hB; exact Sym.add_zero_part c hA hB
  | succ k ih =>
    intro d A B hA hB
    refine Sym.intro_succ c (Sym.add_zero_part c (hA.zero_part c) (hB.zero_part c))
      (fun j => ?_)
    have h := ih (hA.pd c j) (hB.pd c j)
    refine Sym.congr c hc ?_ h
    intro η hη u hu
    have hAd := Sym.diff c hc hA hη hu
    have hBd := Sym.diff c hc hB hη hu
    simp only [pdv]
    rw [(hAd.hasFDerivAt.fun_add hBd.hasFDerivAt).fderiv]
    rfl

theorem Sym.sum (hc : c.Good) {ι : Type*} {k : ℕ} {d : ℤ} (s : Finset ι)
    (A : ι → (Fin N → ℝ) → (Fin N → ℝ) → ℝ) (h : ∀ i ∈ s, Sym c k d (A i)) :
    Sym c k d (fun η u => ∑ i ∈ s, A i η u) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have e : (fun (η u : Fin N → ℝ) => ∑ i ∈ (∅ : Finset ι), A i η u) = fun _ _ => (0 : ℝ) := by
      funext η u; simp
    rw [e]
    exact Sym.zero c
  | insert a s ha ih =>
    have e : (fun (η u : Fin N → ℝ) => ∑ i ∈ insert a s, A i η u) =
        fun η u => A a η u + ∑ i ∈ s, A i η u := by
      funext η u; rw [Finset.sum_insert ha]
    rw [e]
    exact Sym.add c hc (h a (Finset.mem_insert_self a s))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

theorem Sym.mul (hc : c.Good) :
    ∀ {k : ℕ} {d e : ℤ} {A B : (Fin N → ℝ) → (Fin N → ℝ) → ℝ},
      Sym c k d A → Sym c k e B → Sym c k (d + e) (fun η u => A η u * B η u) := by
  intro k
  induction k with
  | zero => intro d e A B hA hB; exact Sym.mul_zero_part c hA hB
  | succ k ih =>
    intro d e A B hA hB
    refine Sym.intro_succ c (Sym.mul_zero_part c (hA.zero_part c) (hB.zero_part c))
      (fun j => ?_)
    have h1 := ih (hA.pd c j) (Sym.mono_k c (Nat.le_succ k) hB)
    have h2 := ih (Sym.mono_k c (Nat.le_succ k) hA) (hB.pd c j)
    rw [show d - c.ω j + e = d + e - c.ω j by ring] at h1
    rw [show d + (e - c.ω j) = d + e - c.ω j by ring] at h2
    have h3 := Sym.add c hc h1 h2
    refine Sym.congr c hc ?_ h3
    intro η hη u hu
    have hAd := Sym.diff c hc hA hη hu
    have hBd := Sym.diff c hc hB hη hu
    simp only [pdv]
    rw [(hAd.hasFDerivAt.fun_mul hBd.hasFDerivAt).fderiv]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring

theorem Sym.mono_d (hc : c.Good) :
    ∀ {k : ℕ} {d d' : ℤ} {A : (Fin N → ℝ) → (Fin N → ℝ) → ℝ},
      d' ≤ d → Sym c k d A → Sym c k d' A := by
  intro k
  induction k with
  | zero => intro d d' A hd hA; exact Sym.mono_d_zero c hc hd hA
  | succ k ih =>
    intro d d' A hd hA
    exact Sym.intro_succ c (Sym.mono_d_zero c hc hd (hA.zero_part c))
      (fun j => ih (by linarith) (hA.pd c j))

/-- A derivative along a vector is the coordinate-weighted sum of partial derivatives. -/
theorem fderiv_apply_eq_sum (f : (Fin N → ℝ) → ℝ) (u v : Fin N → ℝ) :
    fderiv ℝ f u v = ∑ j, v j * pdv j f u := by
  have hv : v = ∑ j, v j • (Pi.single j (1 : ℝ) : Fin N → ℝ) := by
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  simp [map_sum, pdv]

/-- A vector field whose coordinates have degree `ω_j - w` lowers symbol degrees by `w`. -/
theorem Sym.fieldDeriv (hc : c.Good) {Z : (Fin N → ℝ) → (Fin N → ℝ) → (Fin N → ℝ)} {w : ℤ}
    (hZ : ∀ (j : Fin N) (k : ℕ), Sym c k ((c.ω j : ℤ) - w) (fun η u => Z η u j))
    {k : ℕ} {d : ℤ} {A : (Fin N → ℝ) → (Fin N → ℝ) → ℝ} (hA : Sym c (k + 1) d A) :
    Sym c k (d - w) (fun η u => fderiv ℝ (A η) u (Z η u)) := by
  have h : Sym c k (d - w) (fun η u => ∑ j, Z η u j * pdv j (A η) u) := by
    refine Sym.sum c hc Finset.univ _ (fun j _ => ?_)
    have h1 := Sym.mul c hc (hZ j k) (hA.pd c j)
    rw [show (c.ω j : ℤ) - w + (d - c.ω j) = d - w by ring] at h1
    exact h1
  refine Sym.congr c hc ?_ h
  intro η hη u hu
  exact fderiv_apply_eq_sum (A η) u (Z η u)

end RothschildStein.P2
