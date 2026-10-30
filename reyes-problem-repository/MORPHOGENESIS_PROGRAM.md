# WCT Morphogenesis: A Four-Stage Unified Research Problem

**Status:** cross-cutting research candidate; **not a verified open problem, completed theorem, or new numbered GC entry**.  
**Issue:** [#76: Unify selection, saturation, stability and propagation](https://github.com/rickyjreyes/math/issues/76).  
**Prepared:** 2026-10-30.  
**Scope:** mathematical mechanisms that may support the continuing Wave Confinement Theory (WCT) research program. Any claim about nature requires its own physical derivation and experimental tests.

## The central question

**Can the same nonlinear evolution select an initially preferred finite-wavelength mode, regulate its amplitude, organize it into a stable coherent structure, and sustain the propagation or regeneration of that structure across space?**

The four distinct obligations are:

1. **Selection:** which perturbations grow, and does nonlinear competition select a unique mode, a band, or several possible states?
2. **Saturation:** what mechanism limits growing amplitudes without artificial normalization or projection?
3. **Stability:** which resulting patterns or confined states survive perturbations, and in what topology?
4. **Propagation:** can a coherent state move, invade an unstable background, or regenerate its organization at new spatial locations? What selects its speed?

The objective is a **common-equation theorem** (or a mathematically decisive obstruction), not an inference assembled from proofs about different models.

## Relationship to the existing GC catalogue

This is a **cross-cutting synthesis**, retaining the current **300 numbered GC candidates and all existing GC statuses**. It does not create GC301, duplicate a challenge, or alter an earlier result.

| Stage | Principal existing questions | Relevant additional questions |
| --- | --- | --- |
| Selection | [GC11: nonlinear finite-wavelength selection](problems/03-spectral-scattering/GC11.md), [GC35: infinite-domain pattern selection](problems/07-pattern-formation/GC35.md) | [GC31: nonlinear attractors](problems/07-pattern-formation/GC31.md), [GC178: hexagons vs stripes](problems/07-pattern-formation/GC178.md), [GC187: slow ramps](problems/07-pattern-formation/GC187.md) |
| Saturation | [GC257: microscopic origin of cubic–quintic saturation](problems/11-physical-emergence-multiscale/GC257.md), [GC134: large-mass saturation](problems/04-variational-solitons/GC134.md) | [GC03: global evolution](problems/01-wave-dynamics/GC03.md), [GC31](problems/07-pattern-formation/GC31.md) |
| Stability | [GC61: formation and breakdown](problems/01-wave-dynamics/GC61.md), [GC53: confinement and stability thresholds](problems/02-confinement-curvature/GC53.md) | [GC01: orbital stability](problems/01-wave-dynamics/GC01.md), [GC56: bifurcation](problems/01-wave-dynamics/GC56.md), [GC57: stochastic forcing](problems/07-pattern-formation/GC57.md) |
| Propagation | [GC185: fronts between patterns](problems/07-pattern-formation/GC185.md), [GC67: traveling-wave velocities](problems/01-wave-dynamics/GC67.md) | [GC143: dispersive propagation bounds](problems/05-higher-derivative-fields/GC143.md), [GC39: coherent-state interactions](problems/08-topology-multicomponent/GC39.md), [GC51: soliton resolution](problems/01-wave-dynamics/GC51.md) |

**Important distinctions:** GC143 concerns dispersion and signal-speed bounds, not automatically the regeneration of a nonlinear pattern. GC67 concerns localized traveling waves, not automatically invasion fronts. GC61 concerns formation from nonperturbative data, not merely stability of data already near a soliton.

## Track A: an explicitly specified mathematical testbed

To avoid changing models silently between the four stages, begin with the real one-dimensional cubic–quintic Swift–Hohenberg-type flow:

$$
\partial_t u
=
\mu u-a(\partial_x^2+k_\star^2)^2u
+b u^3-c u^5,\qquad x\in\mathbb R,\ t\ge0,
$$

where $u$ is real-valued, $a,b,c,k_\star>0$, and initially restrict

$$
0<\mu<a k_\star^4.
$$

This restriction makes $u=0$ linearly unstable near the preferred nonzero wavenumber while the zero Fourier mode remains linearly damped. It does **not** prove existence, uniqueness, or stability of a nonlinear pattern.

This equation is a **testbed**, not the canonical WCT curvature evolution and not a purported derivation from the S004 action. Results must retain that qualification.

### Linear mode-selection identity

For the linearized equation at $u=0$, a Fourier mode $e^{iqx}$ has growth exponent

$$
\sigma(q)=\mu-a(k_\star^2-q^2)^2.
$$

Consequently $\sigma(\pm k_\star)=\mu>0$, while $\sigma(0)=\mu-a k_\star^4<0$, and sufficiently distant modes decay. This is an exact elementary dispersion calculation; a distinct theorem is required for **nonlinear** selection, and uniqueness of the selected wavelength is not assumed. An interval of admissible or stable wavelengths is an acceptable outcome.

### Nonlinear amplitude regulation and energy

The cubic contribution can amplify a nonzero mode, while the sign of the quintic term is saturating at large amplitude. For a smooth periodic solution, the formal gradient energy is

$$
\mathcal E_L(u)=
\int_0^L
\left[
\frac a2\left|(\partial_x^2+k_\star^2)u\right|^2
-\frac{\mu}{2}u^2-\frac b4u^4+\frac c6u^6
\right]\,dx.
$$

When a sufficient regularity and chain-rule theorem applies,

$$
\frac{d}{dt}\mathcal E_L(u(t))
=-\int_0^L|\partial_tu|^2\,dx\le0.
$$

**This identity is not a proof of uniform $H^2$ control or global existence by itself.** Those require coercivity, control of the negative terms, function-space estimates and continuation. On the entire real line, periodic patterns have infinite unrenormalized energy; an admissible relative/local energy and a separate proof are needed. Do not apply the periodic identity to whole-space fronts without this justification.

### Nonlinear pattern and stability target

Seek a nonzero periodic stationary profile $p_q$ with period $2\pi/q$ satisfying

$$
0=\mu p_q-a(\partial_x^2+k_\star^2)^2p_q+b p_q^3-c p_q^5.
$$

Classify the family of admissible $q$ and its spectral stability under Bloch/Floquet perturbations. Translation produces a neutral phase mode; specify how this symmetry is handled. A theorem about a single periodic domain is **not** yet a theorem about disturbances on the full real line. Nonlinear orbital/diffusive stability, stability boundaries, and the dependence on $q$ are separate milestones.

### Pattern-depositing propagation target

A front leaving a stationary spatial pattern behind is generally **not** adequately represented by a plain traveling profile $u(t,x)=P(x-vt)$: the deposited pattern may remain stationary in laboratory coordinates while the invasion interface moves.

Use a **modulating-front** ansatz

$$
u(t,x)=U(\xi,z),\qquad \xi=x-vt,\qquad z=x,
$$

with $U(\xi,z+L)=U(\xi,z)$ and asymptotic conditions, in a function space and convergence mode to be frozen:

$$
U(\xi,\cdot)\longrightarrow p(\cdot)\quad(\xi\to-\infty),
\qquad
U(\xi,\cdot)\longrightarrow0\quad(\xi\to+\infty).
$$

Its profile equation is

$$
-v\partial_\xi U
=
\mu U
-a\left[(\partial_\xi+\partial_z)^2+k_\star^2\right]^2U
+bU^3-cU^5.
$$

Seek conditions on parameters and initial data under which such a front exists, a speed $v>0$ or speed-selection law is established, the deposited wavelength is characterized, and the solution or front has the stated nonlinear stability. A nonexistence result, multiple admissible speeds, or a front leaving unstable patterns behind is a legitimate classification outcome.

The front profile and its asymptotics are **proposed proof targets**; no existence or convergence theorem is claimed here.

## Five milestones with independent pass/fail criteria

| Milestone | Precise deliverable | Failure or necessary refinement |
| --- | --- | --- |
| **M0: Common model** | Freeze equation, parameter set, well-posedness class, localized initial-data class, patterns, perturbation topology and asymptotic states | Incompatible assumptions between stages; silent model changes |
| **M1: Selection** | Exact linear symbol and nonlinear existence/selection classification for $q$, allowing a band rather than a unique wavelength | Multistability, dependence on initial data, or failed unique selection |
| **M2: Saturation** | Global existence and a quantitative amplitude/energy bound without mass projection, plus a justified descent law where applicable | Blow-up, uncontrolled growth, failure of coercivity |
| **M3: Stability** | Stable periodic or localized states with exact perturbation class, symmetry handling and nonlinear time estimates | Sideband/Eckhaus-type instability or absence of stable branches |
| **M4: Propagation** | A front or wave with proved asymptotics, admissible speed(s), deposited state and stability under a declared initial-data class | No front, front stalling, unstable deposited pattern, or failure of a selection law |
| **M5: Integration** | One theorem/counterexample placing M1–M4 in **one compatible parameter regime** and specifying which initial data realize the entire chain | Separate lemmas about unrelated equations do not satisfy the claim |

**Full resolution standard:** provide a theorem with all quantifiers and exact hypotheses; or an explicit counterexample showing that an intended four-stage assertion fails. A negative result may constrain this testbed without refuting other WCT dynamics. Partial milestones do not complete M5.

## Track B: transfer to the actual curvature-coupled WCT evolution

The testbed is a mathematical laboratory, not the endpoint of the foundational WCT program. A separate, explicitly versioned **canonical WCT evolution** is required before transferring conclusions. The following obligations cannot be skipped:

1. Show how the effective finite-band dynamics arise from, or are consistently embedded in, the specified parent evolution. A phenomenological similarity is not a derivation.
2. Establish local and global well-posedness for the actual nonlinear curvature operator with its corrected complex regularizer, including any required $\varepsilon>0$ and higher-regularity hypotheses.
3. Prove non-artificial mode selection and saturation under the same WCT parameters and dynamics.
4. Prove existence, localization and relevant stability for those **actual** states, not only the independent F01 cubic–quintic system.
5. Establish propagation or front/transport laws without conflating group velocity, signal causality, wave motion, and pattern regeneration.
6. Separately test any proposed correspondence to observed particles, materials, cosmology or biological morphogenesis.

### Existing mathematics to reuse, without exaggerating correspondence

| Existing evidence | What it supports | What it does not yet establish |
| --- | --- | --- |
| [F11 / E16, E59, E62, E13/E14](../lean/README.md) | Exact finite-band and projection mathematics, linear concentration and gradient-flow identities | Unique nonlinear pattern selection in the parent WCT field law |
| [E57 / E58 / E61](../lean/README.md) | Fourth-order spectral operators, semigroups, damping, thresholds | Fully coupled WCT saturation and front propagation |
| [F01: NegativeEnergy, StrictBinding, WholeSpaceMinimizers, CubicQuinticFlow, OrbitalStability](../lean/formalization.yaml) | A separate nonlinear model has whole-space minimizers, global evolution and orbital stability in the proved parameter range | Physical identity with the WCT curvature evolution or spontaneous morphogenesis |
| [E17 / E26 / E68 / E69](../lean/README.md) | Corrected curvature regularization, boundedness conditions, dimension/regularity estimates | Well-posedness of the entire nonlinear curvature PDE or a 3D physical selection theorem |
| [wct-pde](https://github.com/rickyjreyes/wct-pde) and [wct-fem](https://github.com/rickyjreyes/wct-fem) | Numerical checks, mode diagnostics, finite-domain candidate evolution | Continuum front existence, stability, or universal physical significance |

For the canonical WCT chain, see [wct-lean #19](https://github.com/rickyjreyes/wct-lean/issues/19) (well-posedness), [#20](https://github.com/rickyjreyes/wct-lean/issues/20) (free-space confinement), [#21](https://github.com/rickyjreyes/wct-lean/issues/21) (stability), and [math #37](https://github.com/rickyjreyes/math/issues/37) (corrected E18 curvature-energy descent). The S004-to-effective-wave bridge in [geometry_of_resonance #45](https://github.com/rickyjreyes/geometry_of_resonance/issues/45) is a separate necessary parent-model question.

## Initial prior-art leads (not novelty clearance)

Modulating fronts and wavenumber selection in Swift–Hohenberg-type systems already have substantial mathematical literature. In particular:

- A. Scheel and J. Weinburd (2018), *Wavenumber selection via spatial parameter jump*, DOI [10.1098/rsta.2017.0191](https://doi.org/10.1098/rsta.2017.0191). Proves patterned interfaces with a constrained stripe-wavenumber band for a **spatially inhomogeneous** Swift–Hohenberg equation.
- *Modulating traveling fronts for the Swift–Hohenberg equation in the case of an additional conservation law* (2020), DOI [10.1016/j.jde.2020.03.033](https://doi.org/10.1016/j.jde.2020.03.033). Constructs pattern-invasion modulating fronts in a **coupled** system near a Turing instability.

These works make **blanket novelty claims about fronts or wavelength selection inappropriate**. They do not automatically resolve the exact testbed defined above, and neither establishes WCT's parent-theory or physical claims. Before calling M1–M5 new or open, freeze all hypotheses and perform a model-by-model literature comparison, including any existing constant-coefficient Swift–Hohenberg front results.

## Falsification and scope checks

Explicitly test: zero and constant states; finite-band versus genuinely unique $q$; unstable sideband modes; multiple stable wavelengths; finite-box artefacts; loss of coercivity; dependence on $b/c$ and $\mu$; the $\mu\downarrow0$ onset; fronts without stable deposited patterns; $v=0$ and multiple speeds; one versus higher spatial dimensions; and the singular $\varepsilon\downarrow0$ limit on the canonical WCT route.

If only M1–M3 pass, **stable patterns are not yet a propagation algorithm**. If M4 passes for a different equation, that is a separate model result. A measured interference or persistent signal would need dedicated experimental controls before it could be attributed to the proposed mechanism.

## Status and next action

- **Catalog status:** cross-cutting candidate, not one of the 300 numbered GC entries.
- **Existing GC statuses:** unchanged; none are closed by this synthesis.
- **Lean status:** no new verified theorem claimed by this document.
- **First decisive research move:** freeze M0, then test M2–M4 in the same testbed; in parallel identify the exact canonical WCT evolution and determine whether a mathematically valid bridge exists.
- **Completion evidence:** cite exact theorem declarations and the checked Git revision, preserve failed cases, compare the frozen manuscript against its Lean proof and record what remains outside the theorem.

[Research issue #76](https://github.com/rickyjreyes/math/issues/76) · [300-problem roadmap](ROADMAP_300.md) · [Formalization registry](../lean/formalization.yaml) · [Research workflow](WORKFLOW.md)
