-- Copyright (c) 2026 Scott Armstrong and Amélie Loher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Mathlib.Analysis.Distribution.TestFunction
public import RothschildStein.Definitions.HomogeneousGroup
public import RothschildStein.Definitions.SmoothDifferentialOperator.IsHomogeneous
public import RothschildStein.Definitions.SmoothDifferentialOperator.apply

/-!
# Type-`λ` kernels and operators

The kernel frame fixes the model group `G`, the two-point map `Θ`, the open cutoff region `V`,
the two fundamental kernels `Γ, Γ*` and the smooth symmetric gauge `‖·‖` used for the type-0
truncation `ρ(ξ, η) = ‖Θ(η, ξ)‖`. A frame carries no hypotheses; consumers add the lifted-chart
and kernel hypotheses they use.

A type-`λ` kernel has, for every regularity budget `m`, a finite decomposition into
principal terms `a(ξ) b(η) (D^{ξ,η} Γ_ε)(Θ(η, ξ))`, with `a, b ∈ C_c^∞(V)`, `D^{ξ,η}` homogeneous
of degree at most `2 - λ` with coefficients jointly smooth in `(ξ, η, u)`, plus a regular
remainder that is jointly `C^m` with compact support in `V × V`. Equality is required off the
diagonal only, so the values of `Γ, Γ*` at zero never matter. Type-0 operators act by the
`ρ`-truncated principal value plus a smooth multiplier `μ ∈ C_c^∞(V)` (with an enlarged multiplier
convention); positive types act by the absolute integral.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

@[expose] public section
noncomputable section
open Set MeasureTheory TopologicalSpace Filter
open scoped Topology
namespace RothschildStein.P1

/-- The fixed kernel frame of P1 §Standing data: model group, two-point map, cutoff
region, the poles `Γ, Γ*` and the smooth symmetric gauge (BB pp. 543–545). -/
structure KernelFrame (N : ℕ) where
  /-- The homogeneous model group. -/
  G : HomogeneousGroup N
  /-- The two-point map; kernels are evaluated at `Θ η ξ`. -/
  Θ : (Fin N → ℝ) → (Fin N → ℝ) → (Fin N → ℝ)
  /-- The open cutoff region `V`. -/
  V : Opens (Fin N → ℝ)
  /-- The fundamental kernel `Γ` of `𝓛 = ∑ Yᵢ² + Y₀`. -/
  Γ : (Fin N → ℝ) → ℝ
  /-- The fundamental kernel `Γ*` of `𝓛* = ∑ Yᵢ² - Y₀`. -/
  Γs : (Fin N → ℝ) → ℝ
  /-- The smooth symmetric homogeneous gauge. -/
  gauge : (Fin N → ℝ) → ℝ

namespace KernelFrame

variable {N : ℕ} (F : KernelFrame N)

/-- The symmetric truncation distance `ρ(ξ, η) = ‖Θ(η, ξ)‖` of the principal value. -/
def rho (ξ η : Fin N → ℝ) : ℝ := F.gauge (F.Θ η ξ)

/-- The pole selected by a principal term: `Γ` for `false`, `Γ*` for `true`. -/
def pole (star : Bool) : (Fin N → ℝ) → ℝ := bif star then F.Γs else F.Γ

end KernelFrame

/-- A principal term of a type decomposition: `a(ξ) b(η) (D^{ξ,η} Γ_ε)(Θ(η, ξ))`. The operator family
has fixed multi-indices, coefficients jointly smooth in `(ξ, η, u)`, and every `D^{ξ,η}` is
homogeneous of the integer degree `degree` (BB p. 543, Def 11.7; Rem 11.9). -/
structure PrincipalTerm {N : ℕ} (F : KernelFrame N) where
  /-- The output cutoff `a ∈ C_c^∞(V)`. -/
  a : TestFunction F.V ℝ (⊤ : ℕ∞)
  /-- The input cutoff `b ∈ C_c^∞(V)`. -/
  b : TestFunction F.V ℝ (⊤ : ℕ∞)
  /-- The parameter-dependent homogeneous differential operator `D^{ξ,η}`. -/
  D : (Fin N → ℝ) → (Fin N → ℝ) → SmoothDifferentialOperator N
  /-- The common multi-indices of the family. -/
  indices : Finset (Fin N → ℕ)
  indices_eq : ∀ ξ η, (D ξ η).indices = indices
  coefficient_smooth : ∀ α ∈ indices, ContDiff ℝ (⊤ : ℕ∞)
    (fun z : (Fin N → ℝ) × (Fin N → ℝ) × (Fin N → ℝ) => (D z.1 z.2.1).coefficient α z.2.2)
  /-- The homogeneous degree of every `D^{ξ,η}`. -/
  degree : ℤ
  homogeneous : ∀ ξ η, (D ξ η).IsHomogeneous F.G degree
  /-- The pole: `Γ` for `false`, `Γ*` for `true`. -/
  star : Bool

namespace PrincipalTerm

variable {N : ℕ} {F : KernelFrame N}

/-- The kernel `a(ξ) b(η) (D^{ξ,η} Γ_ε)(Θ(η, ξ))` of a principal term. -/
def kernel (t : PrincipalTerm F) (ξ η : Fin N → ℝ) : ℝ :=
  t.a ξ * t.b η * (t.D ξ η).apply (F.pole t.star) (F.Θ η ξ)

end PrincipalTerm

/-- A regular remainder of budget `m`: jointly `C^m`, compactly supported in `V × V`
(BB p. 543, Def 11.7, with the remainder regularity made explicit). -/
def IsRegularKernel {N : ℕ} (F : KernelFrame N) (m : ℕ) (r : (Fin N → ℝ) → (Fin N → ℝ) → ℝ) :
    Prop :=
  ContDiff ℝ m (fun z : (Fin N → ℝ) × (Fin N → ℝ) => r z.1 z.2) ∧
  HasCompactSupport (fun z : (Fin N → ℝ) × (Fin N → ℝ) => r z.1 z.2) ∧
  tsupport (fun z : (Fin N → ℝ) × (Fin N → ℝ) => r z.1 z.2) ⊆
    (F.V : Set (Fin N → ℝ)) ×ˢ (F.V : Set (Fin N → ℝ))

/-- A decomposition of `k` witnessing type `lam` at regularity budget `m`:
finitely many principal terms with `D` of degree at most `2 - lam`, plus a regular remainder,
with equality off the diagonal (BB p. 543, Def 11.7). -/
structure TypeDecomposition {N : ℕ} (F : KernelFrame N) (lam m : ℕ)
    (k : (Fin N → ℝ) → (Fin N → ℝ) → ℝ) where
  /-- The principal terms. -/
  principal : List (PrincipalTerm F)
  principal_degree : ∀ t ∈ principal, t.degree ≤ 2 - (lam : ℤ)
  /-- The regular remainder. -/
  regular : (Fin N → ℝ) → (Fin N → ℝ) → ℝ
  regular_isRegular : IsRegularKernel F m regular
  eq_off_diagonal : ∀ ξ η, ξ ≠ η →
    k ξ η = (principal.map (fun t => t.kernel ξ η)).sum + regular ξ η

/-- `k` is a kernel of type `lam`: a decomposition exists for every regularity
budget (BB p. 543, Def 11.7). -/
def IsTypeKernel {N : ℕ} (F : KernelFrame N) (lam : ℕ)
    (k : (Fin N → ℝ) → (Fin N → ℝ) → ℝ) : Prop :=
  ∀ m : ℕ, Nonempty (TypeDecomposition F lam m k)

/-- An operator of type `lam`: a type-`lam` kernel and a multiplier `μ ∈ C_c^∞(V)`,
which vanishes at positive type (BB p. 545, Def 11.11, enlarged multiplier convention). -/
structure TypeOperator {N : ℕ} (F : KernelFrame N) (lam : ℕ) where
  /-- The kernel. -/
  kernel : (Fin N → ℝ) → (Fin N → ℝ) → ℝ
  isType : IsTypeKernel F lam kernel
  /-- The multiplier `μ`. -/
  mult : TestFunction F.V ℝ (⊤ : ℕ∞)
  mult_eq_zero : lam ≠ 0 → (mult : (Fin N → ℝ) → ℝ) = 0

namespace TypeOperator

variable {N : ℕ} {F : KernelFrame N} {lam : ℕ}

/-- The `ε`-truncated integral `∫_{ρ(ξ,η) > ε} k(ξ, η) f(η) dη` of the principal value. -/
def truncated (T : TypeOperator F lam) (f : (Fin N → ℝ) → ℝ) (ε : ℝ) (ξ : Fin N → ℝ) : ℝ :=
  ∫ η in {η | ε < F.rho ξ η}, T.kernel ξ η * f η

/-- `T f (ξ) = value` in the principal-value sense: the truncations are integrable and
converge as `ε ↓ 0` to `value - μ(ξ) f(ξ)`. -/
def HasValue (T : TypeOperator F lam) (f : (Fin N → ℝ) → ℝ) (ξ : Fin N → ℝ) (value : ℝ) :
    Prop :=
  (∀ ε : ℝ, 0 < ε →
    IntegrableOn (fun η => T.kernel ξ η * f η) {η | ε < F.rho ξ η} volume) ∧
  Tendsto (fun ε => T.truncated f ε ξ) (𝓝[>] (0 : ℝ)) (𝓝 (value - T.mult ξ * f ξ))

/-- The action of a type operator: at type 0 the truncated principal value plus `μ f`; at positive
type the absolute integral `∫ k(ξ, η) f(η) dη` (BB pp. 543–545). -/
def apply (T : TypeOperator F lam) (f : (Fin N → ℝ) → ℝ) (ξ : Fin N → ℝ) : ℝ :=
  if lam = 0 then limUnder (𝓝[>] (0 : ℝ)) (fun ε => T.truncated f ε ξ) + T.mult ξ * f ξ
  else ∫ η, T.kernel ξ η * f η

end TypeOperator

end RothschildStein.P1
