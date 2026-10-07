# Hörmander's theorem and the Rothschild–Stein theory, formalized in Lean 4

[![Build](https://github.com/amelieloher/hoermander-rothschild-stein/actions/workflows/build.yml/badge.svg?branch=main)](https://github.com/amelieloher/hoermander-rothschild-stein/actions/workflows/build.yml)
[![Comparator](https://github.com/amelieloher/hoermander-rothschild-stein/actions/workflows/comparator.yml/badge.svg?branch=main)](https://github.com/amelieloher/hoermander-rothschild-stein/actions/workflows/comparator.yml)

A **Lean 4 / Mathlib** formalization of the regularity theory of Hörmander operators

```math
L=\sum_{i=1}^{q}X_i^2+X_0+c,
```

where $`X_0,X_1,\dots,X_q`$ are real smooth vector fields on an open set $`\Omega\subseteq\mathbb R^n`$ whose iterated commutators span $`\mathbb R^n`$ at every point. Hörmander's theorem allows a drift $`X_0`$ and a smooth zeroth-order coefficient $`c`$. In the Rothschild–Stein estimates $`c=0`$, and the drift is either absent or present with weight two. The main results are:

- **Hörmander's hypoellipticity theorem.** A locally integrable weak solution of $`Lu=g`$ with smooth $`g`$ agrees almost everywhere with a smooth function. The Sobolev-space steps of the proof are also stated separately: the subelliptic estimate, local regularity, and the embeddings $`L^1\subseteq H^{-m}`$ and $`\bigcap_sH^s\subseteq C^\infty`$.
- **The Rothschild–Stein estimates.** A distributional solution of $`\sum_iX_i^2T=f`$ with $`f`$ in $`W^{k,p}_X`$ or $`C^{k,\alpha}_X`$ is a function in $`W^{k+2,p}_{X,\mathrm{loc}}`$ or $`C^{k+2,\alpha}_{X,\mathrm{loc}}`$, for every $`k\ge0`$, with interior estimates. With a drift, the same holds for $`k=0`$.
- **Homogeneous groups and lifting.** Hörmander fields lift to free fields in more variables, which are approximated by the generators of a free nilpotent homogeneous group. On homogeneous groups, the homogeneous fundamental solution has the kernel bounds and representation formulas used in the parametrix, and global and local $`L^p`$ and Hölder estimates hold.
- **Geometry of Hörmander vector fields.** The formal Baker–Campbell–Hausdorff theorem, Chow–Rashevskii connectivity, and the Nagel–Stein–Wainger ball-box, volume, doubling and distance-comparison theorems, uniformly over compact sets and compact families of fields.

The constants in the interior estimates depend only on the fields, the nested domains, the order and the exponents. The library contains no `sorry` and uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Results formalized

The following lists the results covered from each source. The detailed formulations and Lean declarations appear below.

- **Lars Hörmander, “Hypoelliptic second order differential equations”, Acta Mathematica 119 (1967), 147–171** ([DOI](https://doi.org/10.1007/BF02392081)).

  - Theorem 1.1, for operators $`X_0+\sum_{i=1}^kX_i^2+c`$ with real smooth coefficients on an open subset of $`\mathbb R^N`$. The formal statement concerns locally integrable weak solutions with smooth right-hand side, and concludes almost-everywhere equality with a smooth function. The original theorem concerns distributions; the library also proves the distributional form as a step of the Rothschild–Stein proofs, but it is not among the compared statements.
  - The proof follows the subelliptic-estimate method of Kohn and of Oleĭnik–Radkevič, as presented by Bramanti–Brandolini, Chapter 5, not Hörmander's original argument.

- **Linda Preiss Rothschild and Elias M. Stein, “Hypoelliptic differential operators and nilpotent groups”, Acta Mathematica 137 (1976), 247–320** ([DOI](https://doi.org/10.1007/BF02392419)).

  - Theorems 4 and 5, the lifting to free vector fields and the approximation by left-invariant fields of a free nilpotent group, in the form of Bramanti–Brandolini, Theorems 10.6–10.7, with and without a drift of weight two.
  - The Sobolev regularity of Theorem 16(d) and its drift analogue in Theorem 18, in the form of Bramanti–Brandolini, Theorems 11.1(a) and 11.2(a): the solution is an arbitrary distribution, as the paper remarks is possible after Theorem 16. With a drift only $`k=0`$ is covered.
  - The Hölder estimates are those of Bramanti–Brandolini, Theorems 11.1(b) and 11.2(b), in the Hölder spaces of the control distance. The rest of the paper is not formalized, including Part I, the $`\Lambda_\alpha`$ and $`L^p_\alpha`$ scales of Section 16 and the estimates for $`\Box_b`$ of Section 19.

- **Alexander Nagel, Elias M. Stein and Stephen Wainger, “Balls and metrics defined by vector fields I: Basic properties”, Acta Mathematica 155 (1985), 103–147** ([DOI](https://doi.org/10.1007/BF02392539)).

  - Theorem 7, the structure of the balls through exponential charts on weighted boxes; Theorem 1, the volume of the balls, with local doubling; and Theorems 2–4, the local equivalence of the control distance with the distance defined by all brackets of bounded weight.
  - These are stated uniformly for base points in a compact set $`K`$ and over a compact family of jointly smooth fields, under Hörmander's condition with a fixed step on a neighbourhood of $`K`$; control balls are taken in the whole domain. The kernel estimates of Chapter 3 are not formalized.

- **Marco Bramanti and Luca Brandolini, *Hörmander Operators*, World Scientific (2023)** ([DOI](https://doi.org/10.1142/13006)), cited as BB. This is the primary source for the proofs.

  - Chapter 5: Proposition 5.16(iii), Proposition 5.17, Theorem 5.54 (stated with the ordinary length of bracket words) and Theorem 5.64.
  - Theorem 1.45(1)–(2) and Proposition 1.28 (connectivity); Theorems 9.1, 9.6 and 9.11 (volumes of balls, equivalent distances, structure of balls); Theorems 9.18 and 9.68 (formal Baker–Campbell–Hausdorff).
  - Theorems 10.6 and 10.7 (lifting and approximation). Theorem 10.6(3) prints $`\Theta(\eta,\xi)^{-1}=-\Theta(\xi,\eta)`$; with the group inverse $`u^{-1}=-u`$ the correct identity, used here and stated on p. 512, is $`\Theta(\xi,\eta)=-\Theta(\eta,\xi)`$.
  - Theorems 11.1 (all $`k\ge0`$), 11.2 ($`k=0`$, as stated there) and 11.5, and the estimates of Sections 8.4–8.6 on homogeneous groups. Theorem 11.4, the lower-order terms of Remark 11.3, and Chapter 12 are not formalized.

- **Wei-Liang Chow, “Über Systeme von linearen partiellen Differentialgleichungen erster Ordnung”, Mathematische Annalen 117 (1940), 98–105** ([DOI](https://doi.org/10.1007/BF01450011)), and **P. K. Rashevskii, “Any two points of a totally nonholonomic space may be connected by an admissible line” (in Russian), Uchenye Zapiski Ped. Inst. im. Liebknechta, Ser. Phys. Math. 2 (1938), 83–94**.

  - The connectivity theorem, in the form of BB Theorem 1.45 and Proposition 1.28: connection by finite chains of integral arcs of the fields, finiteness of every weighted control distance, and constancy of $`C^1`$ functions annihilated by the fields.

## Sources

The proofs follow BB. The following sources were consulted as cross-checks of particular steps; their full collections of results are outside the scope listed above.

- J. J. Kohn, *Hypoellipticity and loss of derivatives* (with an appendix by M. Derridj and D. S. Tartakoff), Annals of Mathematics **162** (2005), 943–986, **Sections 1–2** ([DOI](https://doi.org/10.4007/annals.2005.162.943)). The subelliptic-estimate route to Hörmander's theorem.
- Bernard Helffer and Francis Nier, *Hypoelliptic Estimates and Spectral Theory for Fokker–Planck Operators and Witten Laplacians*, Lecture Notes in Mathematics 1862, Springer (2005), **Chapter 2** ([DOI](https://doi.org/10.1007/b104762)). Subelliptic estimates with a drift.
- Yves Colin de Verdière, Luc Hillairet and Emmanuel Trélat, *Small-time asymptotics of hypoelliptic heat kernels near the diagonal, nilpotentization and related results* (2020), **Appendix B.1.1** ([arXiv:2004.06461](https://arxiv.org/abs/2004.06461)). The subelliptic estimate with drift and potential.
- Fulvio Ricci, *Sub-Laplacians on nilpotent Lie groups*, lecture notes, academic year 2002–2003, **Appendix, Sections 6–8**. Local $`L^2`$ regularization and the Sobolev bootstrap.
- Marco Bramanti, *On the proof of Hörmander's hypoellipticity theorem*, Le Matematiche **75** (2020), 3–26 ([DOI](https://doi.org/10.4418/2020.75.1.1)). A comparison of the proofs of Hörmander's theorem.
- G. B. Folland, *Subelliptic estimates and function spaces on nilpotent Lie groups*, Arkiv för Matematik **13** (1975), 161–207 ([DOI](https://doi.org/10.1007/BF02386204)). Homogeneous groups and homogeneous fundamental solutions.
- Marco Bramanti, Luca Brandolini and Marco Pedroni, *On the lifting and approximation theorem for nonsmooth vector fields*, Indiana University Mathematics Journal **59** (2010), 2093–2138 ([arXiv:1002.1331](https://arxiv.org/abs/1002.1331); [DOI](https://doi.org/10.1512/iumj.2010.59.4298)). The lifting and approximation theorem.
- Michael Müger, *Notes on the theorem of Baker–Campbell–Hausdorff–Dynkin*, lecture notes, April 22, 2020 ([author's notes](https://www.math.ru.nl/~mueger/PDF/BCHD.pdf)). The formal Baker–Campbell–Hausdorff theorem over fields of characteristic zero.

Where BB omit steps or contain misprints, the omitted arguments and corrections are supplied in the formalization. The source relationships are recorded in [`formalization.yaml`](formalization.yaml).

## Vector fields, distances and function spaces

Points of $`\mathbb R^n`$ are functions `Fin n → ℝ` with Lebesgue measure. A vector field is a map $`X:\mathbb R^n\to\mathbb R^n`$, acting on functions by $`Xf(x)=Df(x)\,X(x)`$, and $`[X,Y]`$ is the commutator of vector fields (Mathlib's `VectorField.lieBracket`). For a word $`I=(i_1,\dots,i_\ell)`$ write

```math
X_{[I]}=[X_{i_1},[X_{i_2},\dots,[X_{i_{\ell-1}},X_{i_\ell}]\dots]],\qquad X_I=X_{i_1}X_{i_2}\cdots X_{i_\ell},\qquad |I|_w=\sum_{j=1}^{\ell}w_{i_j}.
```

Each field has a positive integer weight $`w_i`$. Without drift every weight is $`1`$ (`noDriftWeight`); with a drift, $`X_0`$ has weight $`2`$ and $`X_1,\dots,X_q`$ weight $`1`$ (`driftWeight`). The empty word has bracket $`0`$ and weight $`0`$. *Hörmander's condition* on $`\Omega`$ (`bracketSpansOn`) says that the brackets $`X_{[I]}(x)`$ of nonempty words span $`\mathbb R^n`$ at every $`x\in\Omega`$; the condition *at step* $`s`$ (`bracketStepOn`, `StepSpansAt`) restricts to $`|I|_w\le s`$. For Hörmander's theorem the condition is stated with arbitrary iterated Lie words (`Hormander.Interface.LieAlgebraSpansOn`); the two forms span the same space.

The weighted control distance in $`\Omega`$ is

```math
d(x,y)=\inf\Bigl\{\delta\gt0:\ \exists\,\gamma:[0,1]\to\Omega\text{ absolutely continuous},\ \gamma(0)=x,\ \gamma(1)=y,\ \gamma'(t)=\sum_ia_i(t)X_i(\gamma(t)),\ |a_i(t)|\le\delta^{w_i}\text{ a.e.}\Bigr\}\in[0,\infty],
```

with $`\inf\varnothing=\infty`$, and $`B(x,r)=\{y\in\Omega:d(x,y)\lt r\}`$ (`rsBall`).

A distribution $`T`$ on $`\Omega`$ solves $`\sum_iX_i^2T=f`$, for $`f\in L^1_{\mathrm{loc}}(\Omega)`$, if $`T\bigl(\sum_iX_i^{\mathsf T}X_i^{\mathsf T}\varphi\bigr)=\int_\Omega f\varphi`$ for every test function $`\varphi`$, where $`X^{\mathsf T}\varphi=-\mathrm{div}\,(\varphi X)`$; with a drift the test operator is $`X_0^{\mathsf T}\varphi+\sum_{i\ge1}X_i^{\mathsf T}X_i^{\mathsf T}\varphi`$. Distributions are Mathlib's real distributions on an open set.

*Sobolev spaces.* $`g`$ is the weak derivative $`X_If`$ on $`V`$ if $`\int_Vg\varphi=\int_Vf\,X_I^{\mathsf T}\varphi`$ for all test functions, with $`X_I^{\mathsf T}=X_{i_\ell}^{\mathsf T}\cdots X_{i_1}^{\mathsf T}`$. Then

```math
\|f\|_{W^{k,p}_X(V)}=\sum_{|I|_w\le k}\|X_If\|_{L^p(V)}\in[0,\infty],
```

where the sum includes the empty word ($`\|f\|_{L^p(V)}`$), and $`\|X_If\|_{L^p(V)}`$ is the infimum over weak derivatives, $`\infty`$ if there is none. $`f\in W^{k,p}_X(V)`$ means that $`f`$ and all these weak derivatives exist and lie in $`L^p(V)`$; $`f\in W^{k,p}_{X,\mathrm{loc}}(\Omega)`$ means $`f\in W^{k,p}_X(V)`$ for every open $`V`$ with compact closure in $`\Omega`$.

*Hölder spaces.* The intrinsic derivative $`Xf(x)`$ is the derivative of $`f\circ\gamma`$ at $`0`$ along local integral curves $`\gamma`$ of $`X`$ through $`x`$ in $`V`$; at least one curve must exist, and every such curve gives the same value. Intrinsic derivatives along words are iterated. With respect to the control distance $`d`$,

```math
[f]_{\alpha,V}=\inf\bigl\{C\lt\infty:\ |f(x)-f(y)|\le C\,d(x,y)^\alpha\ \text{for }x,y\in V,\ d(x,y)\lt\infty\bigr\},\qquad \|f\|_{C^{k,\alpha}_X(V)}=\sum_{|I|_w\le k}\Bigl(\sup_V|X_If|+[X_If]_{\alpha,V}\Bigr),
```

each term taken as an infimum over intrinsic derivatives. Again all norms take values in $`[0,\infty]`$ (`ℝ≥0∞` in Lean), and $`C^{k,\alpha}_{X,\mathrm{loc}}(\Omega)`$ is defined as for Sobolev spaces.

The definitions are in [`RothschildStein/Definitions/`](RothschildStein/Definitions/), one per file, and in [`Hormander/Interface/`](Hormander/Interface/) and [`Hormander/Defs/`](Hormander/Defs/):

| Module | Lean definitions |
| --- | --- |
| Hörmander's equation (namespace `Hormander.Interface`) | [`LieWord`](Hormander/Interface/LieWord.lean), [`LieWord.eval`](Hormander/Interface/LieWordEval.lean), [`LieAlgebraSpansOn`](Hormander/Interface/LieAlgebraSpansOn.lean), [`basisVec`](Hormander/Interface/BasisVec.lean), [`euclideanDivergence`](Hormander/Interface/EuclideanDivergence.lean), [`hormanderAdjointTest`](Hormander/Interface/HormanderAdjointTest.lean), [`HasWeakHormanderEquation`](Hormander/Interface/HasWeakHormanderEquation.lean) |
| Operators on $`\mathcal S'(\mathbb R^N)`$ (namespace `Hormander`) | [`lieWordLength`](Hormander/Defs/LieWordLength.lean), [`lieWordEval`](Hormander/Defs/LieWordEval.lean), [`vectorFieldOp`](Hormander/Defs/VectorFieldOp.lean), [`hormanderOp`](Hormander/Defs/HormanderOp.lean) |
| Words and brackets (namespace `RothschildStein`, as below) | [`wordBracket`](RothschildStein/Definitions/wordBracket.lean), [`wordWeight`](RothschildStein/Definitions/wordWeight.lean), [`wordFamily`](RothschildStein/Definitions/wordFamily.lean), [`noDriftWeight`](RothschildStein/Definitions/noDriftWeight.lean), [`driftWeight`](RothschildStein/Definitions/driftWeight.lean), [`bracketSpansOn`](RothschildStein/Definitions/bracketSpansOn.lean), [`bracketStepOn`](RothschildStein/Definitions/bracketStepOn.lean), [`StepSpansAt`](RothschildStein/Definitions/StepSpansAt.lean) |
| Control distance | [`isControlledCurve`](RothschildStein/Definitions/isControlledCurve.lean), [`controlDistance`](RothschildStein/Definitions/controlDistance.lean), [`rsBall`](RothschildStein/Definitions/rsBall.lean), [`absoluteJacobian`](RothschildStein/Definitions/absoluteJacobian.lean) |
| Distributional equations | [`fieldTranspose`](RothschildStein/Definitions/fieldTranspose.lean), [`wordTranspose`](RothschildStein/Definitions/wordTranspose.lean), [`testMultiplierOn`](RothschildStein/Definitions/testMultiplierOn.lean), [`fieldTransposeTest`](RothschildStein/Definitions/fieldTransposeTest.lean), [`wordTransposeTest`](RothschildStein/Definitions/wordTransposeTest.lean), [`sumSquaresTransposeTest`](RothschildStein/Definitions/sumSquaresTransposeTest.lean), [`sumSquaresWithDriftTransposeTest`](RothschildStein/Definitions/sumSquaresWithDriftTransposeTest.lean), [`hasDistributionEquation`](RothschildStein/Definitions/hasDistributionEquation.lean), [`hasDistributionEquationWithDrift`](RothschildStein/Definitions/hasDistributionEquationWithDrift.lean), [`representsDistribution`](RothschildStein/Definitions/representsDistribution.lean) |
| Sobolev spaces | [`hasWeakWordDeriv`](RothschildStein/Definitions/hasWeakWordDeriv.lean), [`weakWordENorm`](RothschildStein/Definitions/weakWordENorm.lean), [`sobolevXENorm`](RothschildStein/Definitions/sobolevXENorm.lean), [`memSobolevX`](RothschildStein/Definitions/memSobolevX.lean), [`memSobolevXLoc`](RothschildStein/Definitions/memSobolevXLoc.lean), [`memSobolevXZero`](RothschildStein/Definitions/memSobolevXZero.lean) |
| Hölder spaces | [`hasIntrinsicDeriv`](RothschildStein/Definitions/hasIntrinsicDeriv.lean), [`hasIntrinsicWordDeriv`](RothschildStein/Definitions/hasIntrinsicWordDeriv.lean), [`holderSeminorm`](RothschildStein/Definitions/holderSeminorm.lean), [`holderENorm`](RothschildStein/Definitions/holderENorm.lean), [`intrinsicWordENorm`](RothschildStein/Definitions/intrinsicWordENorm.lean), [`holderXENorm`](RothschildStein/Definitions/holderXENorm.lean), [`memHolderX`](RothschildStein/Definitions/memHolderX.lean), [`memHolderXLoc`](RothschildStein/Definitions/memHolderXLoc.lean), [`memHolderXCompact`](RothschildStein/Definitions/memHolderXCompact.lean) |
| Homogeneous groups | [`polynomialProduct`](RothschildStein/Definitions/polynomialProduct.lean), [`coordinateDilation`](RothschildStein/Definitions/coordinateDilation.lean), [`HomogeneousGroup`](RothschildStein/Definitions/HomogeneousGroup.lean), and in [`HomogeneousGroup/`](RothschildStein/Definitions/HomogeneousGroup/): `mul`, `inv`, `dilate`, `homogeneousDimension`, `canonicalField`, `horizontalFields`, `driftFields`, `IsHomogeneousGauge`, `HasHomogeneousDistribution`, `potential`, `HasPrincipalValue` |
| Operators and fundamental solutions | [`fieldDerivative`](RothschildStein/Definitions/fieldDerivative.lean), [`wordDerivative`](RothschildStein/Definitions/wordDerivative.lean), [`sumSquares`](RothschildStein/Definitions/sumSquares.lean), [`sumSquaresTranspose`](RothschildStein/Definitions/sumSquaresTranspose.lean), [`sumSquaresWithDrift`](RothschildStein/Definitions/sumSquaresWithDrift.lean), [`sumSquaresWithDriftTranspose`](RothschildStein/Definitions/sumSquaresWithDriftTranspose.lean), [`euclideanPartial`](RothschildStein/Definitions/euclideanPartial.lean), [`SmoothDifferentialOperator`](RothschildStein/Definitions/SmoothDifferentialOperator.lean) (with `apply` and `IsHomogeneous`), [`isFundamentalDistribution`](RothschildStein/Definitions/isFundamentalDistribution.lean) |
| Free nilpotent algebras and lifting | [`BoundedWord`](RothschildStein/Definitions/BoundedWord.lean), [`boundedWordList`](RothschildStein/Definitions/boundedWordList.lean), [`WordCoefficients`](RothschildStein/Definitions/WordCoefficients.lean), [`wordConvolution`](RothschildStein/Definitions/wordConvolution.lean), [`formalBracket`](RothschildStein/Definitions/formalBracket.lean), [`truncatedBracket`](RothschildStein/Definitions/truncatedBracket.lean), [`formalSpan`](RothschildStein/Definitions/formalSpan.lean), [`freeDimension`](RothschildStein/Definitions/freeDimension.lean), [`FormalRelation`](RothschildStein/Definitions/FormalRelation.lean), [`FreeAt`](RothschildStein/Definitions/FreeAt.lean), [`rsPartial`](RothschildStein/Definitions/rsPartial.lean), [`WeightedJet`](RothschildStein/Definitions/WeightedJet.lean), [`basePoint`](RothschildStein/Definitions/basePoint.lean), [`joinPoint`](RothschildStein/Definitions/joinPoint.lean), [`triangularLift`](RothschildStein/Definitions/triangularLift.lean), [`rsGauge`](RothschildStein/Definitions/rsGauge.lean), [`fiberVolume`](RothschildStein/Definitions/fiberVolume.lean) |

## Hörmander's theorem

**Hypoellipticity.** Let $`\Omega\subseteq\mathbb R^N`$ be open, let $`X_0,\dots,X_k`$ be smooth on $`\Omega`$ with all iterated Lie brackets spanning $`\mathbb R^N`$ at every point of $`\Omega`$, and let $`c`$ be smooth on $`\Omega`$. If $`u\in L^1_{\mathrm{loc}}(\Omega)`$ and $`g\in C^\infty(\Omega)`$ satisfy, for every $`\varphi\in C_c^\infty`$ with support in $`\Omega`$,

```math
\int_\Omega u\,L^*\varphi=\int_\Omega g\,\varphi,\qquad L^*\varphi=-\mathrm{div}\,(\varphi X_0)+\sum_{i=1}^k\mathrm{div}\,\bigl(\mathrm{div}\,(\varphi X_i)\,X_i\bigr)+c\varphi,
```

then there is $`f\in C^\infty(\Omega)`$ with $`u=f`$ almost everywhere in $`\Omega`$.

Lean: [`Hormander.Interface.exists_smooth_aeRepresentative`](Hormander/Interface.lean). Here $`L^*`$ is the formal adjoint of $`X_0+\sum_iX_i^2+c`$ (`hormanderAdjointTest`) and the weak equation is `HasWeakHormanderEquation`. Coefficients, $`u`$ and $`g`$ are real-valued; smoothness means `ContDiffOn ℝ ⊤`, that is, of every finite order on $`\Omega`$. The cases $`k=0`$, $`N=0`$ and $`\Omega=\varnothing`$ are included.

The proof passes through statements on $`\mathbb R^N`$ (as `EuclideanSpace ℝ (Fin N)`) for operators with compactly supported coefficients, acting on complex tempered distributions through `hormanderOp`. Here $`H^s`$ is Mathlib's Sobolev space `TemperedDistribution.MemSobolev s 2`, and $`\widehat u`$ is Mathlib's Fourier transform $`\widehat u(\xi)=\int e^{-2\pi i\langle x,\xi\rangle}u(x)\,dx`$.

**Subelliptic estimate.** Let $`X_0,\dots,X_k`$ and $`c`$ be smooth with compact support, $`K`$ compact inside an open $`U`$, $`s\ge1`$, and suppose $`N`$ Lie words of length at most $`s`$ are linearly independent at every point of $`U`$. Then there is $`C`$ such that for every Schwartz function $`u`$ supported in $`K`$,

```math
\int_{\mathbb R^N}(1+|\xi|^2)^{2/4^s}\,|\widehat u(\xi)|^2\,d\xi\le C\bigl(\|Lu\|_{L^2}^2+\|u\|_{L^2}^2\bigr),\qquad Lu=\sum_{i=1}^kX_i^2u+X_0u+cu.
```

Lean: [`Hormander.subelliptic_estimate`](Hormander/Statements/SubellipticEstimate.lean). This is BB Theorem 5.54 with gain $`\varepsilon=2/4^s`$; the length of a word counts every letter once (`lieWordLength`), including the drift.

**Local regularity.** In the same setting, let $`\zeta,\zeta'`$ be smooth with $`\zeta'=1`$ near the support of $`\zeta`$ and $`\mathrm{supp}\,\zeta'\subseteq K`$. If $`u`$ is a tempered distribution, $`\zeta'Lu`$ is a Schwartz function and $`\zeta'u\in H^{-m}`$, then $`\zeta u\in H^t`$ for every $`t\in\mathbb R`$. Lean: [`Hormander.forall_memSobolev_of_localized`](Hormander/Statements/LocalRegularity.lean), BB Theorem 5.64.

**Sobolev embeddings.** An integrable function on $`\mathbb R^N`$ lies in $`H^{-m}`$ for every $`m\gt N/2`$, and a tempered distribution lying in every $`H^s`$ is given by a smooth function $`f`$, in the sense that $`T(\varphi)=\int\varphi f`$ for every Schwartz function $`\varphi`$. Lean: [`Hormander.memSobolev_neg_of_integrable`](Hormander/Statements/MemSobolevOfIntegrable.lean) and [`Hormander.exists_contDiff_of_forall_memSobolev`](Hormander/Statements/ExistsContDiffOfMemSobolev.lean), BB Propositions 5.17 and 5.16(iii).

## Interior estimates of Rothschild and Stein

Fix $`n,q\ge1`$, open sets $`V,W,\Omega\subseteq\mathbb R^n`$ with $`\overline V`$ compact in $`W`$ and $`\overline W`$ compact in $`\Omega`$, and fields $`X_1,\dots,X_q`$ smooth on $`\Omega`$ satisfying Hörmander's condition on $`\Omega`$. Let $`d`$ be their control distance in $`\Omega`$.

**Sobolev estimate.** For every $`k\ge0`$ and $`1\lt p\lt\infty`$ there is $`C\gt0`$ such that, for every distribution $`T`$ on $`\Omega`$ and every $`f\in W^{k,p}_X(\Omega)`$ with $`\sum_iX_i^2T=f`$, the distribution $`T`$ is given by a function $`u\in L^1_{\mathrm{loc}}(\Omega)`$ with $`u\in W^{k+2,p}_{X,\mathrm{loc}}(\Omega)`$ and

```math
\|u\|_{W^{k+2,p}_X(V)}\le C\bigl(\|f\|_{W^{k,p}_X(W)}+\|u\|_{L^p(W)}\bigr).
```

Lean: [`RothschildStein.rs3_no_drift_sobolev`](RothschildStein/Statements/rs3_no_drift_sobolev.lean). This is BB Theorem 11.1(a). The constant depends on $`n,q,\Omega,V,W,X,k,p`$ and not on $`T`$ or $`f`$. The inequality is in $`[0,\infty]`$; $`p`$ is an extended real (`ℝ≥0∞`) with $`1\lt p\lt\infty`$.

**Hölder estimate.** For every $`k\ge0`$ and $`0\lt\alpha\lt1`$ there is $`C\gt0`$ such that, for every distribution $`T`$ and every $`f\in C^{k,\alpha}_X(\Omega)`$ with $`\sum_iX_i^2T=f`$, the distribution $`T`$ is given by a function $`u`$, continuous on $`\Omega`$, with $`u\in C^{k+2,\alpha}_{X,\mathrm{loc}}(\Omega)`$,

```math
\|u\|_{C^{k+2,\alpha}_X(V)}\le C\bigl(\|f\|_{C^{k,\alpha}_X(W)}+\|u\|_{L^\infty(W)}\bigr),
```

and $`\sum_iX_iX_iu=f`$ at every point of $`\Omega`$, with intrinsic derivatives. Lean: [`RothschildStein.rs3_no_drift_holder`](RothschildStein/Statements/rs3_no_drift_holder.lean). This is BB Theorem 11.1(b). All Hölder norms use the control distance $`d`$ of $`X`$ in $`\Omega`$, and $`\|u\|_{L^\infty(W)}`$ is the essential supremum.

**Estimates with drift.** Let $`X_0,X_1,\dots,X_q`$ be smooth on $`\Omega`$ and satisfy Hörmander's condition there, with $`X_0`$ of weight two. For $`T`$ with $`X_0T+\sum_{i\ge1}X_i^2T=f`$ the same conclusions hold at $`k=0`$: if $`f\in L^p(\Omega)`$ then $`u\in W^{2,p}_{X,\mathrm{loc}}(\Omega)`$, and if $`f\in C^{0,\alpha}_X(\Omega)`$ then $`u\in C^{2,\alpha}_{X,\mathrm{loc}}(\Omega)`$ and $`X_0u+\sum_{i\ge1}X_iX_iu=f`$ pointwise, with

```math
\|u\|_{W^{2,p}_X(V)}\le C\bigl(\|f\|_{L^p(W)}+\|u\|_{L^p(W)}\bigr),\qquad \|u\|_{C^{2,\alpha}_X(V)}\le C\bigl(\|f\|_{C^{\alpha}_X(W)}+\|u\|_{L^\infty(W)}\bigr).
```

Lean: [`RothschildStein.rs3_drift_sobolev`](RothschildStein/Statements/rs3_drift_sobolev.lean) and [`RothschildStein.rs3_drift_holder`](RothschildStein/Statements/rs3_drift_holder.lean). This is BB Theorem 11.2, which also treats only $`k=0`$. The norms are weighted: $`\|u\|_{W^{2,p}_X}`$ contains $`\|X_0u\|_{L^p}`$ and $`\|X_iX_ju\|_{L^p}`$ for $`i,j\ge1`$, and $`d`$ is the control distance with $`X_0`$ of weight two. The bracket condition counts $`X_0`$ like any other generator.

## Homogeneous groups and lifting

A homogeneous group on $`\mathbb R^N`$ (`HomogeneousGroup`, BB Chapter 3) has a polynomial group law $`x\circ y`$ with identity $`0`$ and polynomial inverse, and dilations $`D_t(x)=(t^{\omega_j}x_j)_j`$, with positive nondecreasing integer weights $`\omega_j`$, that are group automorphisms. Its homogeneous dimension is $`Q=\sum_j\omega_j`$. The canonical field $`Z_j`$ is the left-invariant field equal to $`\partial_j`$ at the origin. A homogeneous norm $`\nu`$ (`IsHomogeneousGauge`) is continuous and nonnegative, vanishes only at $`0`$ and satisfies $`\nu(D_tx)=t\,\nu(x)`$. Convolution is $`(f*K)(v)=\int f(u)\,K(u^{-1}\circ v)\,du`$.

**Homogeneous fundamental solution.** Let the first $`q\ge1`$ canonical fields $`Y_i=Z_i`$ have weight one and satisfy Hörmander's condition on $`\mathbb R^N`$, let $`Q\ge3`$, and let $`\nu`$ be any homogeneous norm. Then $`L=\sum_iY_i^2`$ has a fundamental solution $`\Gamma`$ (in the sense $`\Gamma(L^{\mathsf T}\varphi)=\varphi(0)`$), unique among distributions homogeneous of degree $`2-Q`$, which is smooth off the origin and satisfies $`\Gamma(D_tx)=t^{2-Q}\Gamma(x)`$,

```math
|\Gamma|\le C\nu^{2-Q},\quad |Y_i\Gamma|\le C\nu^{1-Q},\quad |Y_iY_j\Gamma|\le C\nu^{-Q},\qquad
Y_iY_j\varphi(v)=\mathrm{p.v.}\!\int_{\mathbb R^N}L\varphi(u)\,Y_iY_j\Gamma(u^{-1}\circ v)\,du+a_{ij}\,L\varphi(v),
```

together with $`L(\varphi*\Gamma)=\varphi`$, $`\varphi=L\varphi*\Gamma`$ and $`Y_j\varphi=L\varphi*Y_j\Gamma`$ for every test function $`\varphi`$. The same holds for the transpose with $`\Gamma^*(x)=\Gamma(x^{-1})`$, and here $`\Gamma^*=\Gamma`$.

Lean: [`RothschildStein.rs2a_noDrift`](RothschildStein/Statements/rs2a_noDrift.lean), and with the drift $`Y_0=Z_{q+1}`$ of weight two and $`L=Y_0+\sum_{i=1}^qY_i^2`$, [`RothschildStein.rs2a_drift`](RothschildStein/Statements/rs2a_drift.lean), where the second-order bound reads $`|Y_iY_j\Gamma|+|Y_0\Gamma|\le C\nu^{-Q}`$. This is BB Theorem 11.5, via Chapter 6. The statements add two properties: $`|D\Gamma|\le C\nu^{2-Q-m}`$ for every differential operator $`D`$ with smooth coefficients homogeneous of degree $`m`$; and $`\int_{r\lt\nu\lt R}D\Gamma\,\Phi(\nu)=0`$ for every $`D`$ homogeneous of degree two and every $`\Phi`$ continuous on $`[r,R]`$. The principal value is the limit of integrals over $`\nu(u^{-1}\circ v)\gt\varepsilon`$, each absolutely convergent. The canonical fields are smooth: [`RothschildStein.HomogeneousGroup.horizontalFields_contDiff`](RothschildStein/Definitions/HomogeneousGroup/horizontalFields_contDiff.lean) and [`RothschildStein.HomogeneousGroup.driftFields_contDiff`](RothschildStein/Definitions/HomogeneousGroup/driftFields_contDiff.lean).

**Estimates on homogeneous groups.** In the same setting, with a homogeneous norm that is moreover smooth off the origin and symmetric, $`L`$ satisfies ten estimates: the global $`L^p`$ estimate, the global Hölder estimate and its version for supports in a ball, the scale-invariant local $`L^p`$ estimate on gauge balls, local $`L^p`$ and Hölder regularity of distributional solutions, interior $`L^p`$ and Hölder estimates, and solvability with $`W^{2,p}`$ and $`C^{2,\alpha}`$ bounds on domains in a ball. The global estimates read

```math
\sum_{|I|_w=2}\|X_Iu\|_{L^p(\mathbb R^N)}\le C\,\|Lu\|_{L^p(\mathbb R^N)},\qquad \sum_{|I|_w=2}[X_Iu]_{\alpha,\mathbb R^N}\le C\,[Lu]_{\alpha,\mathbb R^N},
```

for $`u,Lu\in L^p`$, respectively for compactly supported $`u\in C^{2,\alpha}_X`$. Lean: [`RothschildStein.rs2b_noDrift`](RothschildStein/Statements/rs2b_noDrift.lean) and [`RothschildStein.rs2b_drift`](RothschildStein/Statements/rs2b_drift.lean), BB Sections 8.4–8.6. Here $`Lu`$ is meant in the sense of distributions and $`X`$ are the canonical fields.

**Lifting and approximation.** Let $`n,q\ge1`$ and $`X_1,\dots,X_q`$ be smooth on an open $`\Omega\subseteq\mathbb R^n`$, satisfying Hörmander's condition at step $`s\ge2`$ at a point $`x_0`$. Let $`n+m`$ be the dimension of the free nilpotent Lie algebra of step $`s`$ on $`q`$ generators. Then there are polynomials $`P_{i\ell}`$, depending only on $`x`$ and $`t_1,\dots,t_{\ell-1}`$, such that the lifted fields

```math
\widetilde X_i(x,t)=\bigl(X_i(x),P_{i1}(x,t),\dots,P_{im}(x,t)\bigr)
```

are free up to step $`s`$ and bracket-generating on a neighbourhood $`U`$ of $`(x_0,0)`$. There is also a homogeneous group with inverse $`u^{-1}=-u`$ whose left-invariant generators $`Y_i`$ are free of step $`s`$, and smooth maps $`\Theta(\eta,\xi)`$ with $`\Theta(\xi,\eta)=-\Theta(\eta,\xi)`$ such that for every bracket word

```math
D_\xi\Theta(\eta,\xi)\,\widetilde X_{[I]}(\xi)=Y_{[I]}\bigl(\Theta(\eta,\xi)\bigr)+R_{I,\eta}\bigl(\Theta(\eta,\xi)\bigr),
```

with remainders $`R_{I,\eta}`$ of local weight at least $`1-|I|`$. The Jacobians of $`\Theta`$ are controlled, the gauge $`|\Theta(\eta,\xi)|`$ is comparable to the control distance of $`\widetilde X`$, and lifted balls have volume comparable to $`r^Q`$. Lifted balls project into the original balls, and their fibres have measure at most a constant times $`|\widetilde B|/|B|`$, and at least a constant times it over a smaller concentric ball.

Lean: [`RothschildStein.exists_lift_approximation_noDrift`](RothschildStein/Statements/exists_lift_approximation_noDrift.lean) and, with a drift $`X_0`$ of weight two, [`RothschildStein.exists_lift_approximation_drift`](RothschildStein/Statements/exists_lift_approximation_drift.lean). These are BB Theorems 10.6 and 10.7, with the sign of Theorem 10.6(3) corrected as noted above. The theorem also gives the integration over the fibres as a continuous map from test functions on $`U`$ to test functions on $`\Omega`$. It makes no claim that $`Q\ge3`$.

## Geometry of Hörmander vector fields

**Baker–Campbell–Hausdorff.** In the free associative algebra $`\mathbb Q\langle x,y\rangle`$ with augmentation ideal $`\mathfrak m`$, there are Lie polynomials $`C_n`$, each a rational combination of right-nested brackets of $`n`$ letters, such that $`C_1=x+y`$, $`C_2=\tfrac12[x,y]`$ and, for every $`N`$,

```math
e^{x}e^{y}=\exp\Bigl(\sum_{n=1}^{N}C_n\Bigr)\quad\text{in }\mathbb Q\langle x,y\rangle/\mathfrak m^{N+1}.
```

Lean: [`RothschildStein.exists_bch_lie_series`](RothschildStein/Statements/exists_bch_lie_series.lean), BB Theorems 9.18 and 9.68. The $`C_n`$ lie in Mathlib's free Lie algebra and are mapped into $`\mathbb Q\langle x,y\rangle`$ through the universal enveloping algebra. Each image is homogeneous of degree $`n`$, and any homogeneous series $`(S_n)`$ with $`S_0=0`$ satisfying the same identities for all $`N`$ coincides with it.

**Chow–Rashevskii.** Let $`\Omega`$ be open and connected and $`X_1,\dots,X_m`$ smooth on $`\Omega`$ satisfying Hörmander's condition. Then any two points of $`\Omega`$, and any two points of a small neighbourhood $`U\subseteq W`$ of each point inside any open $`W\subseteq\Omega`$, are joined by a finite chain of $`C^1`$ arcs, each an integral curve of one field $`cX_i`$ staying in $`\Omega`$, respectively $`W`$. Moreover

```math
d_w(x,y)\lt\infty\quad\text{for all }x,y\in\Omega\text{ and all weights }w,
```

and a $`C^1`$ function on $`\Omega`$ with $`X_if=0`$ for all $`i`$ is constant. Lean: [`RothschildStein.chow_rashevskii`](RothschildStein/Statements/chow_rashevskii.lean), BB Theorem 1.45(1)–(2) and Proposition 1.28. Chains are expressed by the equivalence relation generated by single arcs; $`\Omega`$ is only required to be preconnected, so the empty set is allowed.

The Nagel–Stein–Wainger theorems share one setting. Let $`K\subseteq V\subseteq\Omega`$ with $`K`$ compact and $`V,\Omega`$ open. Let $`X_\sigma=(X_{\sigma,0},\dots,X_{\sigma,k})`$, $`\sigma\in\Sigma`$, be fields smooth on $`\Omega`$, with weights $`w_i\le s`$, indexed by a compact space $`\Sigma`$. All derivatives must be jointly continuous in $`(\sigma,x)`$, and each $`X_\sigma`$ must satisfy Hörmander's condition at step $`s`$ on $`V`$. Balls are control balls in $`\Omega`$. For $`n`$ words $`B=(B_1,\dots,B_n)`$ of weight at most $`s`$, write $`\lambda_B(x)=\det\bigl(X_{[B_1]}(x),\dots,X_{[B_n]}(x)\bigr)`$ and $`|B|=\sum_j|B_j|_w`$.

**Ball-box theorem.** For every $`\theta\in(0,1)`$ there are $`a,b,C,r_0\gt0`$ such that, for every $`\sigma`$, $`x\in K`$ and $`0\lt r\le r_0`$, and every $`B`$ with $`|\lambda_B(x)|r^{|B|}\ge\theta\,|\lambda_{B'}(x)|r^{|B'|}`$ for all $`B'`$, the map $`F(u)=\exp\bigl(\sum_ju_jX_{[B_j]}\bigr)(x)`$ is smooth and injective on the box $`Q=\{|u_j|\lt(ar)^{|B_j|_w}\}`$, and

```math
B(x,br)\subseteq F(Q)\subseteq B(x,Cr),\qquad \tfrac14|\lambda_B(x)|\le|\det DF(u)|\le4\,|\lambda_B(x)|\quad(u\in Q).
```

Lean: [`RothschildStein.exists_ball_box_compact_family`](RothschildStein/Statements/exists_ball_box_compact_family.lean), BB Theorem 9.11 and NSW Theorem 7. The exponential is expressed by an integral curve in $`\Omega`$ from $`x`$ at time $`0`$ to $`F(u)`$ at time $`1`$.

**Volume and doubling.** There are $`c,C,L,r_0\gt0`$ such that, for every $`\sigma`$, $`x\in K`$ and $`0\lt r\le r_0`$, and for $`A\ge1`$ with $`Ar\le r_0`$,

```math
c\,\Lambda(x,r)\le|B(x,r)|\le C\,\Lambda(x,r),\qquad \Lambda(x,r)=\sum_B|\lambda_B(x)|\,r^{|B|}\gt0,\qquad |B(x,Ar)|\le L\,A^{ns}\,|B(x,r)|.
```

Lean: [`RothschildStein.exists_ball_volume_doubling_compact_family`](RothschildStein/Statements/exists_ball_volume_doubling_compact_family.lean), BB Theorem 9.1 and NSW Theorem 1. The sum runs over all $`n`$-tuples of words of weight at most $`s`$, and volumes are Lebesgue measures in `ℝ≥0∞`.

**Comparison of distances.** Let $`d^*`$ be the control distance in $`\Omega`$ of the family of all brackets $`X_{[I]}`$ with $`|I|_w\le s`$, each with weight $`|I|_w`$. There are $`C,\varepsilon\gt0`$ such that, for every $`\sigma`$, $`x\in K`$ and $`y\in\mathbb R^n`$ with $`d^*(x,y)\lt\varepsilon`$,

```math
d^*(x,y)\le d(x,y)\le C\,d^*(x,y).
```

Lean: [`RothschildStein.exists_distance_comparison_compact_family`](RothschildStein/Statements/exists_distance_comparison_compact_family.lean), BB Theorem 9.6 and Remark 9.5, and NSW Theorems 2–4. The family includes the empty word, whose bracket is the zero field; it is given weight one and does not affect $`d^*`$.

## Proof route

Hörmander's theorem follows Kohn's method in BB Chapter 5. The Fourier transform, the Sobolev scale $`H^s`$, Bessel potentials and mollifiers come first. Then comes a calculus of operators of order $`m`$ on Schwartz space, closed under commutators and transposes, with fractional Sobolev multipliers and Peetre's inequality. The basic subelliptic estimate is proved by induction over bracket words, including the drift, with gain $`2/4^s`$ (BB Section 5.5). The localized estimate (Section 5.6) and a finite bootstrap of mollified solutions (Section 5.7) put a localized distributional solution in every $`H^s`$. The theorem on $`\Omega`$ is assembled by cutting off the coefficients near each point, transporting the weak equation to `EuclideanSpace`, taking the local smooth representatives, and gluing them over a countable cover. Hörmander's original argument through flows and the Campbell–Hausdorff formula is not used.

The Rothschild–Stein theory follows BB Chapters 1–3 and 6–11. The geometric part develops flows, weighted brackets and the control distance (Chapter 1), and the formal BCH theorem and the free nilpotent model (Sections 9.3 and 9.8). Suboptimal bases, the structure of balls, volumes and the equivalence of $`d`$ and $`d^*`$ follow (Sections 9.4–9.6), and then lifting, the map $`\Theta`$, its remainders and Jacobians, and the volumes of fibres (Chapter 10). The function spaces $`W^{k,p}_X`$ and $`C^{k,\alpha}_X`$ (Chapter 2) relate weak and intrinsic derivatives. On homogeneous groups (Chapter 3), the homogeneous fundamental solution is built in Chapter 6. Its smoothness uses Hörmander's theorem for distributional solutions, derived from the Chapter 5 library above by localization. Singular and fractional integrals on locally doubling metric spaces, maximal functions, Calderón–Zygmund decompositions and the Campanato characterization of Hölder continuity (Chapter 7) give the estimates on groups (Chapter 8).

For general fields, BB Sections 11.2–11.4 develop operators of type $`\lambda`$ on the lifted space, left and right parametrices built from $`\Gamma\circ\Theta`$, representation formulas for first and second derivatives, and their continuity on $`L^p`$ and Hölder spaces. Sections 11.5–11.6 give the a priori estimates, the transfer from lifted to original variables through the fibre-volume estimates, and the smoothing of distributional solutions. When the lifted group has homogeneous dimension $`Q\le2`$, the proof first adds auxiliary variables and the operator $`\sum\partial_{t_j}^2`$, lifts $`T`$ to $`T\otimes1`$, and descends on bounded product cylinders. The higher estimates for $`k\ge1`$ without drift iterate the representation formulas on shrinking balls. Where BB omit steps, the formalization supplies the arguments.

## Build and verify

Install [Lean's elan toolchain manager](https://github.com/leanprover/elan). From a fresh checkout, run:

```sh
lake exe cache get
lake build
```

The toolchain is **`leanprover/lean4:v4.35.0-rc2`**. Mathlib is **`v4.35.0-rc2`**, resolved in `lake-manifest.json` to **`065356127b1dc0016f66b7283ce0ce2c4055aa55`**. The manifest pins all dependencies. `lake build` builds the library and the comparator files; with the Mathlib cache, a clean build takes about an hour on an 8-core machine.

To print the axioms of a main theorem:

```sh
echo 'import RothschildStein.Statements.rs3_no_drift_sobolev
#print axioms RothschildStein.rs3_no_drift_sobolev' > /tmp/Axioms.lean
lake env lean /tmp/Axioms.lean
```

Two comparator configurations restate the main theorems using only Mathlib, with every definition written out:

| Configuration | Theorems |
| --- | --- |
| [`comparators/Hormander`](comparators/Hormander/) | Hörmander's theorem and its four companions, Baker–Campbell–Hausdorff, Chow–Rashevskii, the three Nagel–Stein–Wainger theorems, and lifting and approximation with and without drift (12 theorems) |
| [`comparators/RothschildStein`](comparators/RothschildStein/) | The four Rothschild–Stein interior estimates, the homogeneous fundamental solution and the estimates on homogeneous groups with and without drift, and three supporting smoothness facts (11 theorems) |

Each `Challenge.lean` states the definitions independently and leaves the main theorem bodies as intentional `sorry` placeholders. The matching `Solution.lean` has the same statements and proves each one from the library. Lean's [comparator](https://github.com/leanprover/comparator), configured by each `comparator.json`, checks that Challenge and Solution state the same theorems over the same definitions and that the Solution uses only the permitted axioms. It also replays the Solution through Lean's kernel and the independent kernel checkers NanoDa and con-ron. To run it as the [Palomar registry](https://submit.palomar-registry.org/) does, install [bubblewrap](https://github.com/containers/bubblewrap) (`bwrap`) and run:

```sh
scripts/verify-comparator.sh
```

The script uses the `lake comparator` and the kernel checkers bundled with the pinned toolchain, so no checker is built separately. It judges every `comparators/*/comparator.json`, or the configurations given as arguments; set `SKIP_CACHE_GET=1` when the Mathlib build is already present. [`scripts/check-lean-sources.py`](scripts/check-lean-sources.py) checks the source requirements: every Lean file is a regular UTF-8 file, starts with the `module` header of Lean's module system, and has at most 10,000 lines.

Continuous integration runs on every push to `main` and on every pull request. The [build workflow](.github/workflows/build.yml) runs the source check, rejects unfinished proofs and axiom declarations outside the Challenge files, and builds everything. It then prints the axioms of all 45 theorems: the 22 library theorems named above and the 23 comparator theorems. Each must depend on exactly `propext`, `Classical.choice` and `Quot.sound`. The [comparator workflow](.github/workflows/comparator.yml) installs bubblewrap and runs `scripts/verify-comparator.sh`.

## Library map

Each main statement has its own short file in [`Hormander/Statements/`](Hormander/Statements/) or [`RothschildStein/Statements/`](RothschildStein/Statements/) (Hörmander's theorem is in [`Hormander/Interface.lean`](Hormander/Interface.lean)). Its proof is assembled in the corresponding `Provider/` directory. The library has about 3,600 Lean files and 289,000 lines, all in Lean's module system and none longer than 1,500 lines.

| Directory | Content |
| --- | --- |
| [`Hormander/Interface`](Hormander/Interface/), [`Hormander/Defs`](Hormander/Defs/) | Lie words, the bracket condition, the weak equation and its adjoint; vector-field operators on tempered distributions |
| [`Hormander/Statements`](Hormander/Statements/), [`Hormander/Provider`](Hormander/Provider/) | The four companion statements, and the proofs of all five Hörmander statements from the library |
| [`Hormander/A`](Hormander/A/) | Fourier transform, the Sobolev scale $`H^s`$ and Bessel potentials, mollifiers, $`L^1\subseteq H^{-m}`$ and smooth representatives |
| [`Hormander/B`](Hormander/B/) | Operators of order $`m`$ on Schwartz space: commutators, transposes, fractional multipliers, Peetre's inequality and extension to tempered distributions |
| [`Hormander/C`](Hormander/C/) | The basic subelliptic estimate: frames of bracket words, the energy estimate and the induction over words with drift |
| [`Hormander/D`](Hormander/D/) | The localized subelliptic estimate: nested cutoffs, commutator expansions and off-diagonal smoothing |
| [`Hormander/E`](Hormander/E/) | Regularization by mollifiers and the finite bootstrap to every $`H^s`$ |
| [`Hormander/F`](Hormander/F/) | Assembly on $`\Omega`$: localization of the weak equation, transport to `EuclideanSpace`, local representatives, countable gluing and edge cases |
| [`RothschildStein/Definitions`](RothschildStein/Definitions/), [`RothschildStein/Statements`](RothschildStein/Statements/), [`RothschildStein/Provider`](RothschildStein/Provider/) | The definitions used in the statements, the fifteen statements, and their proofs from the library |
| [`RothschildStein/G1`](RothschildStein/G1/) | Bracket algebra, local flows and charts, controlled curves, the control distance, Chow connectivity and compact-parameter estimates |
| [`RothschildStein/G2`](RothschildStein/G2/) | Homogeneous groups: group law, dilations, invariant fields, invariance of Lebesgue measure, homogeneous norms, convolution and mollifiers |
| [`RothschildStein/G3`](RothschildStein/G3/) | The formal Baker–Campbell–Hausdorff theorem, the free nilpotent model, exponential maps and Taylor expansions of flows |
| [`RothschildStein/G4`](RothschildStein/G4/) | Suboptimal bases, exponential charts, the ball-box theorem, volumes, local doubling and equivalent distances |
| [`RothschildStein/S`](RothschildStein/S/) | The spaces $`W^{k,p}_X`$ and $`C^{k,\alpha}_X`$: weak and intrinsic derivatives, products, approximation and cutoffs |
| [`RothschildStein/L1`](RothschildStein/L1/) | Triangular lifting, the map $`\Theta`$, remainders, Jacobians, gauge comparison and fibre volumes |
| [`RothschildStein/H1`](RothschildStein/H1/) | The homogeneous fundamental solution, its kernel bounds, cancellation and representation formulas |
| [`RothschildStein/H2`](RothschildStein/H2/) | Singular and fractional integrals in locally doubling spaces: maximal functions, Calderón–Zygmund theory and Campanato spaces |
| [`RothschildStein/H3`](RothschildStein/H3/) | Global and local Sobolev and Hölder estimates and solvability on homogeneous groups |
| [`RothschildStein/P1`](RothschildStein/P1/) | Operators of type $`\lambda`$ on the lifted space, parametrices, representation formulas and their continuity |
| [`RothschildStein/P2`](RothschildStein/P2/) | Interior a priori estimates, transfer from lifted variables, higher-order iteration and smoothing of distributional solutions |
| [`RothschildStein/Distribution`](RothschildStein/Distribution/) | Distributions on open sets: localization, and Hörmander's theorem for distributional solutions |
| [`RothschildStein/Geometry`](RothschildStein/Geometry/) | Chow–Rashevskii and the Nagel–Stein–Wainger theorems over compact families |
| [`comparators`](comparators/) | The two Mathlib-only comparator configurations |

## How this was built

The Lean code was written with AI coding agents under the authors' supervision. The authors approved every exact Lean definition and theorem statement before its proof was developed, and Lean checks the proofs against those statements. The models and tools are recorded in [`formalization.yaml`](formalization.yaml).

## Authors and citation

The Lean development is by

- **Scott Armstrong** — CNRS and Laboratoire Jacques-Louis Lions, Sorbonne Université; Courant Institute School of Mathematics, Computing, and Data Science, New York University
- **Amélie Loher** — All Souls College, University of Oxford

If you use this formalization, please cite it using the metadata in [`CITATION.cff`](CITATION.cff).

## Acknowledgements

Scott Armstrong was supported by the European Research Council (ERC) under the European Union's Horizon Europe research and innovation programme, grant agreement No. 101200828.
Amélie Loher acknowledges support from the Fondation Sciences Mathématiques de Paris.

## License

The Lean code in this repository is licensed under the **Apache License 2.0** (see [`LICENSE`](LICENSE)).
