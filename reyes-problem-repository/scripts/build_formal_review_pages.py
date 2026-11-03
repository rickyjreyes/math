#!/usr/bin/env python3
"""Build the 300-source Reyes formal-review catalogue without changing source questions.

Each page preserves its source mathematical target, supplies a structured research
review and explicit prior-art leads, and marks outstanding per-problem verification.
The generated material is NOT an independent literature review or a Lean proof.
"""
from __future__ import annotations

import argparse
import json
import re
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "formal-reviews"

# Sources have been individually verified at the initial subject-literature level.
# They are NOT asserted to prove or disprove every problem in each group.
PRIOR_ART = {
 "01-wave-dynamics": [
  ("Grillakis, Shatah & Strauss (1987), stability theory for solitary waves",
   "https://doi.org/10.1016/0022-1236(87)90044-9",
   "Abstract Hamiltonian orbital stability; does not classify all fourth-order excited states."),
  ("Gang & Weinstein (2008), nonlinear neutral-mode mass transfer",
   "https://arxiv.org/abs/0811.0261",
   "Nonlinear Fermi-golden-rule damping in related NLS/GP systems, not automatically this dispersion."),
  ("Castéras & Földes (2026), fourth-order mixed-dispersion traveling waves",
   "https://doi.org/10.1007/s00208-026-03399-4",
   "Related fourth-order traveling-wave existence under different hypotheses.")],
 "02-confinement-curvature": [
  ("Lions (1984), concentration–compactness I",
   "https://doi.org/10.1016/S0294-1449(16)30428-0",
   "Known strict-subadditivity/compactness machinery; not automatic for a new curvature operator."),
  ("Bonheure et al. (2018), mixed-dispersion standing waves",
   "https://doi.org/10.1137/17M1154138",
   "Related fourth-order variational existence and stability, different precise nonlinearity.")],
 "03-spectral-scattering": [
  ("Li, Soffer & Yao (2023), fourth-order Schrödinger decay in two dimensions",
   "https://doi.org/10.1016/j.jfa.2022.109816",
   "Threshold expansions for Δ²+V; the ring-degenerate (Δ+1)² threshold differs."),
  ("Feng, Soffer & Yao (2018), fourth-order resolvent and decay",
   "https://doi.org/10.1016/j.jfa.2017.10.014",
   "Related dispersive estimates under specified spectral assumptions.")],
 "04-variational-solitons": [
  ("Lions (1984), concentration–compactness I",
   "https://doi.org/10.1016/S0294-1449(16)30428-0",
   "Compactness and splitting are classical tools; mass-dependent application is model-specific."),
  ("Bonheure et al. (2018), orbitally stable mixed-dispersion waves",
   "https://doi.org/10.1137/17M1154138",
   "Existing related variational results must be separated from new parameter classifications.")],
 "05-higher-derivative-fields": [
  ("Motohashi et al. (2016), healthy degenerate higher-derivative theories",
   "https://doi.org/10.1088/1475-7516/2016/07/033",
   "Constraint degeneracy can remove ghost degrees in specified mechanics classes."),
  ("Motohashi & Suyama (2020), quantum Ostrogradsky theorem",
   "https://doi.org/10.1007/JHEP09(2020)032",
   "Nondegenerate higher-time-derivative obstructions are prior art.")],
 "06-inverse-observation-control": [
  ("Classical rank/implicit function and constant-rank theorems",
   "https://encyclopediaofmath.org/wiki/Constant_rank_theorem",
   "Local rank defects and regular fibers are classical; inspect the exact clipped sensor map."),
  ("Existing Reyes 31-to-11 observation-map Lean formalization",
   "../VERIFIED_LEAN_RESULTS.md",
   "A frozen v18 point and local fiber are already proved; neighboring/global strata need separate review.")],
 "07-pattern-formation": [
  ("Swift–Hohenberg model and classical Eckhaus/zigzag stability boundaries",
   "https://doi.org/10.1016/S0375-9601(98)00502-7",
   "Classical pattern sideband theory precedes the GC catalogue; verify model-specific Bloch assumptions."),
  ("Knobloch, Uecker & Wetzel (2019), localized Swift–Hohenberg patterns",
   "https://doi.org/10.1103/PhysRevE.100.012204",
   "Related nonlinear localized patterns; not automatically the frozen GC equation.")],
 "08-topology-multicomponent": [
  ("Hatcher (2002), Algebraic Topology, homotopy groups and Hopf invariant",
   "https://pi.math.cornell.edu/~hatcher/AT/ATchapters.html",
   "Equal Hopf invariants already imply unrestricted homotopy; path restrictions need stating."),
  ("Ward (2004), Skyrmions and Faddeev–Hopf solitons",
   "https://doi.org/10.1103/PhysRevD.70.061701",
   "Energy/topology examples exist; a new stability or sharp bound must differ."),
  ("Guerra, Lamy & Zemas (2026), Hopf map minimality in Faddeev–Skyrme",
   "https://doi.org/10.1007/s00220-026-05702-5",
   "Recent model-specific minimization result relevant to energy classification.")],
 "09-computability-complexity": [
  ("Cook (2004), universality in elementary cellular automata",
   "https://doi.org/10.25088/ComplexSystems.15.1.1",
   "Rule 110 universality is established; new complexity requires a frozen different encoding."),
  ("Existing Reyes/PVNP model-relative computation formalizations",
   "https://github.com/rickyjreyes/PVNP",
   "The resource/model qualifiers must be preserved, without implying P versus NP.")],
 "10-lean-certified-analysis": [
  ("Mathlib4 mathematical library and theorem API",
   "https://leanprover-community.github.io/mathlib4_docs/",
   "Analytic theorems may already exist formally or classically; novel Lean deliverables need exact signatures."),
  ("Reyes selected formally checked theorem inventory",
   "../VERIFIED_LEAN_RESULTS.md",
   "Check existing theorem files and names before claiming a missing formalization.")],
 "11-physical-emergence-multiscale": [
  ("Hong & Yang (2019), discrete NLS continuum limit",
   "https://doi.org/10.1137/18M120703X",
   "Existing uniform convergence methods for specified lattice models, not automatic for new symbols."),
  ("Li, Soffer & Yao (2023), 2D fourth-order spectral decay",
   "https://doi.org/10.1016/j.jfa.2022.109816",
   "A reference dispersion analysis; does not by itself justify a microscopic limit.")],
 "12-photonic-wave-computing": [
  ("Knill, Laflamme & Milburn (2001), linear optical quantum computation",
   "https://doi.org/10.1038/35051009",
   "Measurement-induced quantum computation is distinct from passive classical coherent amplitude maps."),
  ("Original GC278 finite-model NAND proof and GC300 half-adder margins",
   "../scoped/GC278.md",
   "Idealized optical logic may be algebraically settled without hardware realization or universality.")]
}
TESTS = {
 "01-wave-dynamics": [
  "Prove a nonzero reference profile (or its nonexistence) at one explicitly fixed frequency and regularity class.",
  "Analyze one finite-dimensional discrete spectral subspace or a single exactly specified perturbation channel.",
  "Derive one necessary stability, resonance or conservation estimate before claiming long-time dynamics."],
 "02-confinement-curvature": [
  "Prove or refute one coercivity/continuity estimate at a fixed mass and regularizer.",
  "Test a Gaussian or compactly supported nonzero trial family for vanishing, splitting and scaling.",
  "Establish a single exact bound or explicit counterexample in the specified symmetry quotient."],
 "03-spectral-scattering": [
  "Compute the free Fourier symbol and locate the relevant continuum threshold.",
  "For one explicit potential or source, establish the operator domain and one resolvent or spectral bound.",
  "Calculate a concrete resonance or nonresonance witness before a universal classification."],
 "04-variational-solitons": [
  "Compute a nontrivial explicit fixed-mass trial energy and its scaling dependence.",
  "Establish a one-mass existence or nonattainment criterion, including translations and phase.",
  "Prove or refute a strict splitting, symmetry or Hessian inequality in a restricted class."],
 "05-higher-derivative-fields": [
  "Write the canonical Hessian and constraint matrix for one finite-dimensional sector.",
  "Verify whether one proposed degeneracy generates the required primary and secondary constraints.",
  "Give one explicit negative-energy direction or bounded reduced Hamiltonian under frozen assumptions."],
 "06-inverse-observation-control": [
  "Calculate a Jacobian and rank at the exact frozen observation point.",
  "Construct a local equal-output pair or prove injectivity under a specified prior and clipping cell.",
  "Quantify one local noise amplification modulus before asserting global recovery."],
 "07-pattern-formation": [
  "Construct or rule out one nonconstant stationary periodic pattern at a fixed parameter.",
  "Compute the linearized operator and its neutral modes at that pattern.",
  "Check one explicit Bloch sideband or finite-box instability without claiming all-wavenumber stability."],
 "08-topology-multicomponent": [
  "Compute the exact winding/Hopf charge of one admissible explicit field.",
  "Compare one pair of maps under the specified regularity and admissible homotopies.",
  "Prove a restricted energy or path obstruction, or give a counterexample, before inferring dynamics."],
 "09-computability-complexity": [
  "Prove the correctness of the exact transition rule and its input/output encoding.",
  "Calculate the claimed resource or communication cost for one fixed finite input size.",
  "Give a uniform reduction or adversarial example for one restricted size family."],
 "10-lean-certified-analysis": [
  "Identify the intended Lean declaration, precise types and all imported hypotheses.",
  "Complete one nontrivial auxiliary lemma with an exact-head kernel check and axiom audit.",
  "Compare the Lean theorem quantifiers to the original analytic claim and correct any mismatch."],
 "11-physical-emergence-multiscale": [
  "Derive the exact microscopic linear Fourier symbol and its lowest-order expansion.",
  "Prove one finite-time uniform bound for a fixed smooth initial-data class.",
  "Quantify a one-regime interpolation error, or exhibit a resonance preventing the proposed limit."],
 "12-photonic-wave-computing": [
  "Verify the exact noise-free truth table or transfer equation for all allowed encoded inputs.",
  "Calculate one worst-case detector margin with independently specified perturbation bounds.",
  "Account for one energy, fanout or reset resource and identify which operations are nonlinear."]
}
SPECIAL = {
 "GC66": ("Refined draft", "The published scope-v1 constraint 0<ν<1 is not the true spectral gap. "
  "For u=e^{iλt}φ in the W equation, a nonzero real L² stationary profile requires 0<λ<1/4; "
  "a positive isolated internal-mode frequency must satisfy 0<ν<λ. The existence of φ and the mode "
  "must be established before an open perturbation basin or Fermi-golden-rule damping is asserted."),
 "GC124": ("Refined draft", "Compare localized and stripe states on the SAME fixed torus with finite mass; a "
  "nonzero whole-plane periodic stripe cannot be an L² mass-m competitor."),
 "GC143": ("Refined draft", "A fourth-order dispersive propagator need not have finite propagation speed. "
  "Separate the classical instantaneous-spreading statement from new sharp off-support estimates."),
 "GC165": ("Refined draft", "The v18 local-rank result is already established at a frozen clipping cell. "
  "The new target must study different strata or boundaries, not re-prove the existing point."),
 "GC177": ("Refined draft", "The continuous Bloch sideband limit belongs to an infinite periodic medium, "
  "not a single finite-box discrete set of perturbations."),
 "GC197": ("Refined draft", "Equal Hopf invariants already imply unrestricted homotopy. "
  "The regular-value-at-every-time restriction is the new feature; distinct preimage-link isotopy "
  "types obstruct such a homotopy by isotopy extension."),
 "GC200": ("Withdraw / merge existing theorem", "The displayed flat-torus harmonic representative "
  "already minimizes Dirichlet energy in its winding class. Preserve its exact proof as an elementary "
  "benchmark; do not advertise it as an independently open research problem."),
 "GC212": ("Withdraw / merge existing theorem", "Pathwise continuous maps S³→S² automatically preserve "
  "Hopf charge. Only a rigorously specified stochastic PDE first-zero or regularity-loss question "
  "could constitute a distinct extension."),
 "GC235": ("Merge with Lean formalization backlog", "Fourier–Plancherel and the Laplacian multiplier "
  "identity are classical; compare existing Lean Fourier modules before calling the proposed "
  "declaration missing."),
 "GC247": ("Merge with Lean formalization backlog", "Scattering unitarity under complete wave-operator "
  "hypotheses is classical; isolate the exact missing Lean correspondence."),
 "GC248": ("Merge with Lean formalization backlog", "Homotopy invariance of winding is classical. "
  "A new PDE statement must prove continuity/nonvanishing for its actual flow."),
 "GC250": ("Merge with Lean formalization backlog", "A negative exact rational evaluation refutes "
  "universal real polynomial nonnegativity by the rational-to-real embedding; the task is a "
  "trusted Lean checker, not a new mathematical conjecture."),
 "GC252": ("Merge with Lean formalization backlog", "LaSalle-type Lyapunov convergence is classical "
  "under suitable invariance and compactness; specialize to a nontrivial PDE flow."),
 "GC278": ("Withdraw / record finite-model resolution", "The existing dossier already gives an "
  "algebraic NAND obstruction without a reference and a construction with a powered optical "
  "reference plus threshold detection. Do not call this unresolved or pass off the ideal model "
  "as experimental optical hardware."),
 "GC286": ("Withdraw / record accounting identity", "The stated energy break-even iff criterion is "
  "an accounting identity. A genuinely new physical question needs measurements and matched "
  "workload, error budget, clock, cooling and reset overhead."),
 "GC300": ("Refined draft", "The given carry-intensity product is an assumed nonlinear primitive. "
  "A verified finite noise-margin proof does not imply a passive all-optical half-adder or "
  "fabricated-hardware certification.")
}


def read(rel: str) -> str:
    return (ROOT / rel).read_text(encoding="utf-8")


def legacy_statements() -> dict[str, str]:
    formal = read("FORMAL_PROBLEMS.md")
    heads = list(re.finditer(r"^#{2,3} (GC\d{2}): ([^\n]+)$", formal, re.M))
    if len(heads) != 65:
        raise ValueError(f"Expected 65 original formal statement sections, got {len(heads)}")
    out = {}
    for pos, match in enumerate(heads):
        end = heads[pos + 1].start() if pos + 1 < len(heads) else len(formal)
        body = formal[match.end():end]
        # Remove the thematic header between two GC statements, never equation text.
        body = re.sub(r"\n## (?:New foundational candidates GC51–GC65|"
                      r"Nonlinear wave dynamics.*|Confinement and curvature geometry.*|"
                      r"Spectral theory and scattering.*|Variational analysis and solitons.*|"
                      r"Higher-derivative field theory.*|Inverse problems.*|"
                      r"Pattern formation and disorder.*|Topology and multicomponent fields.*|"
                      r"Computability and complexity.*|Lean formalization and certified analysis.*|"
                      r"Mandatory qualification before claiming an open problem)"
                      r"[\s\S]*$", "", body)
        body = body.strip()
        if "**Problem.**" not in body:
            raise ValueError("Original problem missing for "+match.group(1))
        out[match.group(1)] = body
    return out


def pick_scoped(text: str) -> tuple[str, str]:
    sections = list(re.finditer(r"^## (.+)$", text, flags=re.M))
    if not sections:
        raise ValueError("Scoped file has no section")
    first = sections[0]
    end = sections[1].start() if len(sections)>1 else len(text)
    target = text[first.end():end].strip()
    next_header = sections[1].group(1) if len(sections)>1 else "Source verification"
    next_end = sections[2].start() if len(sections)>2 else len(text)
    second = text[sections[1].end():next_end].strip() if len(sections)>1 else ""
    if not target or len(target) < 60:
        raise ValueError("Empty/short canonical target")
    return target, "**"+next_header+".** "+second


def source_model_note(n: int, area: str, target: str) -> str:
    if n <= 65:
        return ("This is the original GC01–GC65 mathematical problem statement; "
                "the explicit parameters and spaces in the original text are authoritative. "
                "Any remaining words such as generic, admissible, or sharp require a further "
                "model-specific freeze before a theorem can be claimed.")
    models = []
    if re.search(r"(?<![A-Za-z])W(?![A-Za-z])|F_\\omega|\\mathcal A_\\phi|W flow", target):
        models.append("W: i∂ₜu=(Δ+1)²u−|u|²u+|u|⁴u on ℝ², initial H².")
    if re.search(r"(?<![A-Za-z])K(?![A-Za-z])|K_\\varepsilon|E_\{\\alpha|phase curvature", target):
        models.append("K: K_ε(u)=div(Im(conj(u)∇u)/(ε+|u|²)), ε>0, u∈H²(ℝ²).")
    if re.search(r"(?<![A-Za-z])S(?![A-Za-z])|H_V|H_0=", target):
        models.append("S: H_V=(Δ+1)²+V with domain H⁴(ℝ²), real bounded V.")
    if models:
        return ("The source target inherits precisely the following frozen shared conventions "
                "from [COMMON_MODELS.md](../scoped/COMMON_MODELS.md): "+ " ".join(models)+
                " Where the target specifies different coefficients or a different domain, "
                "its explicit equation overrides the shared convention. Do not equate "
                "different operators just because their notation is similar.")
    return ("The **source target below** is the model authority and may introduce a separate "
            "discrete, stochastic, geometric, optical or formal system. Do not substitute "
            "the fourth-order NLS merely because it is used elsewhere in this repository. "
            "Any remaining unspecified datum is a review blocker, not a silent assumption.")


def recommendation(e: dict, area: str, n: int) -> tuple[str, str]:
    key=e["id"]
    if key in SPECIAL:
        return SPECIAL[key]
    if key=="GC08":
        return ("Partially resolved (registry)", "An exact curvature-closure nonuniqueness "
                "counterexample is already formalized, but the full closure-classification "
                "question remains unfinished.")
    if n<=65:
        return ("Candidate (formal original statement)", "The source is one of the 65 preserved "
                "formal questions. This label does not certify global novelty, nonvacuity in "
                "all parameter regimes, or full resolution.")
    return ("Refined draft; formal-promotion review required", "The existing v1 scope supplies "
            "a proposed exact target, but a specific nonvacuity/literature audit and any "
            "remaining topology or quantifier choices must pass independent review.")


def scoping_audit() -> dict[str, tuple[str,str]]:
    """Retrieve reviewer cautions directly from the existing October 30 audit."""
    source=read("SCOPING_AUDIT_GC65_GC300_2026-10-30.md")
    matches=re.findall(
        r"^\| \[(GC\d+)\]\([^)]+\) \| ([^|]+) \| ([^|]+) \| ([^|]+) \|$",
        source, re.M)
    audit={name:(priority.strip(),correction.strip())
           for name,_stage,priority,correction in matches}
    if len(audit)!=236:
        raise ValueError(f"Expected 236 GC65–GC300 audit records, got {len(audit)}")
    return audit


def explicit_repair(key: str) -> str:
    """Only verified problem-specific logical repairs, not new blanket theorems."""
    if key=="GC66":
        return (
          "**Proposed corrected nonvacuous benchmark (not substituted into the "
          "historical source):** Fix λ∈(0,1/4) and a nonzero real profile "
          "φ∈H⁴(ℝ²) satisfying\n\n"
          "$\n(\\Delta+1)^2\\phi+\\lambda\\phi-\\phi^3+\\phi^5=0.\n$\n\n"
          "The linearization in real coordinates has blocks "
          "$L_+=(\\Delta+1)^2+\\lambda-3\\phi^2+5\\phi^4$ and "
          "$L_-=(\\Delta+1)^2+\\lambda-\\phi^2+\\phi^4$. Its essential "
          "spectrum is outside the central interval $(-i\\lambda,i\\lambda)$; "
          "an isolated positive internal mode must have $0<\\nu<\\lambda$. "
          "If a sufficiently regular nondegenerate branch and such a mode exist, "
          "ask for decay of its Riesz spectral projection for a rigorously "
          "specified family of small perturbations, with phase/translation "
          "modulation and possible unstable directions accounted for. "
          "The required existence and damping estimates are **not proved here**."
        )
    if key=="GC200":
        return (
          "**Classical exact solution to the frozen Dirichlet problem:** "
          "Writing a fixed-winding representative as "
          "$u=e^{i(2\\pi mx/L_x+2\\pi ny/L_y+f)}$, with periodic "
          "$f\\in H^1(T;\\mathbb R)$ modulo $2\\pi$, the cross term vanishes "
          "by integration over the torus. The energy is\n\n"
          "$\nE(u)=2\\pi^2\\left(\\frac{m^2L_y}{L_x}"
          "+\\frac{n^2L_x}{L_y}\\right)"
          "+\\frac12\\int_T|\\nabla f|^2.\n$\n\n"
          "Thus the affine harmonic phase is minimizing and is unique "
          "up to a constant phase in the stated winding class. "
          "This elementary mathematical target should be recorded as "
          "already settled, not an unsolved conjecture."
        )
    if key=="GC212":
        return (
          "**Classical implication:** For each sample path continuous as a "
          "map $[0,T]\\to C(S^3,S^2)$, the maps at any two times are "
          "homotopic, so the Hopf integer is unchanged. A new problem needs "
          "an explicit random evolution, proven path regularity and a "
          "first singular/zero-hitting event; adding randomness alone does "
          "not evade homotopy invariance."
        )
    if key=="GC278":
        return (
          "**Frozen algebraic decision is already in its source dossier:** "
          "with zero input $(a,b)=(0,0)$ and no reference beam, "
          "a homogeneous linear unitary network outputs zero, contradicting "
          "NAND(0,0)=1 under a nonnegative positive-intensity threshold. "
          "With a powered reference amplitude and nonlinear threshold "
          "readout, the source supplies an explicit NAND construction. "
          "Neither branch certifies a fabricated passive logic gate."
        )
    return ""


def first_target(e:dict) -> str:
    return e.get("first_test") or ("Identify the smallest admissible special case of the exact "
         "source target and prove an example or counterexample.")


def load_standard_v2() -> dict[str, dict]:
    """Specialist source-preserving reviews for individually assessed cases."""
    found: dict[str, dict] = {}
    for file in sorted((ROOT/"problem-standard-v2").glob("priority-*.json")):
        data=json.loads(file.read_text(encoding="utf-8"))
        for key, value in data.items():
            if key in found:
                raise ValueError("Duplicate specialist review "+key)
            if not re.fullmatch(r"GC\d{2,3}",key):
                raise ValueError("Invalid GC key "+key)
            mandatory={"model","canonical","resolution","known","milestones",
                       "notes","status","recommendation"}
            if not mandatory.issubset(value):
                raise ValueError("Missing review fields: "+key)
            if not (2<=len(value["milestones"])<=4):
                raise ValueError("Milestone count outside problem standard: "+key)
            if not value["known"] or any(len(c)!=3 for c in value["known"]):
                raise ValueError("Missing title, link, scope distinctions: "+key)
            found[key]=value
    if len(found)!=23:
        raise ValueError(f"Expected 23 individually reviewed problems, got {len(found)}")
    return found


def create_specialist_page(e: dict, target: str, source: str,
                           review: dict) -> str:
    """Six-part problem-standard page with preserved source and review boundaries."""
    key=e["id"]
    audit=e.get("_audit")
    audit_line=(f"**Existing audit ({audit[0]}):** {audit[1]}" if audit
                else "The original formal problem remains authoritative.")
    known="\n".join(f"- [{title}]({url}): {difference}"
                     for title,url,difference in review["known"])
    milestones="\n".join(f"{i+1}. {v}"
                         for i,v in enumerate(review["milestones"]))
    if len(review["milestones"])==3:
        milestones+=("\n4. Compare the model and theorem quantifiers with the "
                     "closest cited source; document any genuinely missing result "
                     "before novelty or closure is claimed.")
    return "\n".join([
        f"# {key}: {e['title']}",
        "",
        "**Status:** "+review["status"]+".",
        "**Machine registry:** "+e["status"]+" (unchanged). "
        "**Audit type:** individual mathematical scoping review, not "
        "independent peer review or a Lean-checked new result.",
        "**Sources:** "+source+" · [Six-step standard](../PROBLEM_STANDARD.md) "
        "· [Review queue](REVIEW_QUEUE.md)",
        "",
        "## Canonical mathematical statement",
        "",
        "**Model freeze.** "+review["model"],
        "",
        "**Precise mathematical target / proven narrower result.** "
        +review["canonical"],
        "",
        "**Original scope text (preserved for comparison):**",
        "",
        target,
        "",
        "## Resolution criterion",
        "",
        review["resolution"],
        "",
        "**Proof standard:** Give all quantifiers, functional spaces, "
        "parameter ranges, symmetries, boundary conditions, and the "
        "appropriate affirmative proof or explicit admissible negative "
        "witness. Lean 4 verification is valuable when a new exact theorem "
        "or checker is claimed, but is not implied by this editorial page.",
        "",
        "## Closest known results",
        "",
        known,
        "",
        "**Novelty boundary:** The references support the stated classical "
        "or related results, not a globally complete novelty search. "
        "Any new claim needs focused source-to-statement comparison, and "
        "any proposed analytic derivation above needs independent checking.",
        "",
        "## Falsifiable first milestones",
        "",
        milestones,
        "",
        "## Notes / remaining modeling decisions",
        "",
        review["notes"],
        "",
        audit_line,
        "",
        "## Status recommendation",
        "",
        review["recommendation"],
        "",
        "**Do not silently change the registry:** recommendations to "
        "withdraw, merge, promote or record a solved subclaim are not "
        "actual status transitions. Such transitions require source "
        "verification, independent scope correspondence and the "
        "[existing completion contract](../WORKFLOW.md).",
        ""
    ])


def create_page(e: dict, legacy: dict[str,str]) -> str:
    key = e["id"]
    n = int(key[2:])
    area = e["file_path"].split("/")[1]
    if area not in PRIOR_ART or area not in TESTS:
        raise ValueError("Missing area "+area)
    scope_rel="scoped/"+key+".md"
    if n<=64:
        assert key in legacy
        target=legacy[key]
        resolution="The preserved original resolution criterion is authoritative."
        source="[Canonical original statements](../FORMAL_PROBLEMS.md) · [Individual GC page](../"+e["file_path"]+")"
    else:
        scope=read(scope_rel)
        target,resolution=pick_scoped(scope)
        source="[Existing scoped mathematical target](../"+scope_rel+") · [Original GC page](../"+e["file_path"]+")"
    if e.get("_standard_v2"):
        return create_specialist_page(e,target,source,e["_standard_v2"])
    status,why=recommendation(e,area,n)
    literature="\n".join(
      f"- [{title}]({url}): {scope}" for title,url,scope in PRIOR_ART[area]
    )
    if key in {"GC01","GC06","GC16","GC19","GC53","GC66"}:
        literature+=("\n- [Repository's existing minimizer and orbital-stability "
                     "results](../VERIFIED_LEAN_RESULTS.md): model-specific, mass-restricted "
                     "theorems; they do not automatically prove the broader GC statement.")
    tests=TESTS[area]
    special=SPECIAL.get(key,("", ""))[1]
    note=(f"\n**Specific correction/prior-art collision:** {special}\n" if special else "")
    audit=e.get("_audit")
    audit_note=(("**Historical scoping screen ("+audit[0]+"):** "+audit[1])
                if audit else ("**Historical scoping screen:** See the original "+
                "[formal statement](../FORMAL_PROBLEMS.md) and research-method checklist."))
    statusFlag=e["status"]
    if n>=66 and (statusFlag!="candidate" or e["literature"]!="not_reviewed"):
        raise ValueError("Unexpected status "+key)
    if n<=65 and key not in legacy:
        raise ValueError("Missing legacy "+key)
    lines=[
      f"# {key}: {e['title']}",
      "",
      f"**Review recommendation:** {status}.  **Official registry:** {statusFlag}.",
      "**Review layer:** structured literature-aware screening, November 2, 2026; "
      "**not** a comprehensive item-by-item novelty review or a new Lean proof.",
      "**Evidence:** "+source+" · [Difficulty rubric](../DIFFICULTY_RUBRIC.md)",
      "",
      "## Canonical mathematical statement",
      "",
      "**Model freeze / source of exact quantifiers.** "+source_model_note(n,area,target),
      "",
      "**Precise source target, reproduced without changing mathematical quantifiers:**",
      "",
      target,
      "",
      explicit_repair(key),
      "",
      "**Requested decision.** Determine whether the exact quantified claim above "
      "holds for the specified admissible class. If it holds, identify the strongest "
      "necessary and sufficient conditions available in the frozen model; if not, "
      "construct a counterexample or prove an obstruction with explicitly stated "
      "parameters, topology and norm. This restatement does not broaden the source "
      "target or establish its novelty.",
      "",
      "## Resolution criterion",
      "",
      resolution,
      "",
      "A complete answer must give a theorem with all domains, parameters, "
      "quantifiers, function spaces, boundary/initial data and the relevant "
      "topology, plus a proof or an admissible counterexample. Identify known "
      "theorems first; avoid treating a classical consequence as novel. An "
      "exactly corresponding Lean 4 declaration and axiom/CI audit would be "
      "valuable when nontrivial but is not automatically required to state "
      "or prove an ordinary mathematical fact.",
      "",
      "## Closest known results",
      "",
      "**Subject-level prior-art starting points, not an exhaustive verification "
      "of this exact GC statement:**",
      "",
      literature,
      "",
      "**Novelty filter:** The references establish methods or results for "
      "their own stated equations and spaces. Do not infer that they settle "
      "the present model without theorem-to-question comparison. Conversely, "
      "do not claim this question is globally open merely because a direct "
      "result has not yet been documented in the repository.",
      "",
      "## Falsifiable first milestones",
      "",
      f"1. {tests[0]}",
      f"2. {tests[1]}",
      f"3. {tests[2]}",
      "4. Compare the exact source target and the simplest resolved/rejected "
      "subcase with the closest cited theorem; record one explicit hypothesis "
      "difference, counterexample, or overlap.",
      "",
      "## Notes / remaining modeling decisions",
      "",
      "- **Nonvacuity:** Prove that the defined admissible set and any "
      "postulated standing wave, detector, topological class or eigenmode "
      "exist, or state an exact nonexistence obstruction.",
      "- **Precision:** Confirm every source parameter and solution notion; "
      "check symmetry zero modes, boundary traces, norm/time horizon and "
      "endpoint quantifiers as relevant to the cited model.",
      "- **Prior art:** Conduct a focused, source-by-source full-text review "
      "before calling the result novel, unsolved or independently verified.",
      "- **Problem-specific October 30 issue:** "+audit_note,
      f"- **First original test:** {first_target(e)}",
      note.rstrip(),
      "",
      "## Status recommendation",
      "",
      f"**{status}.** {why}",
      "",
      "**Registry policy:** This editorial recommendation does not change "
      "problem_registry.json, completion records, original mathematical "
      "questions, issue statuses, or published theorem claims. A status "
      "transition requires the [review workflow](../METHOD.md) and an exact "
      "scope-to-evidence audit.",
      ""
    ]
    return "\n".join(x for x in lines if x is not None).replace("\n\n\n","\n\n")


def build() -> dict[str,str]:
    registry=json.loads(read("problem_registry.json"))
    entries=registry["entries"]
    expected=[f"GC{n:02d}" for n in range(1,301)]
    assert [e["id"] for e in entries]==expected
    legacy=legacy_statements()
    audit=scoping_audit()
    specialist=load_standard_v2()
    p0={key for key,(priority,_message) in audit.items() if priority=="P0*"}
    if p0-set(specialist):
        raise ValueError("Unreviewed P0 cases: "+repr(sorted(p0-set(specialist))))
    for e in entries:
        if int(e["id"][2:])>=65:
            e["_audit"]=audit.get(e["id"])
            if e["_audit"] is None:
                raise ValueError("Missing scoped audit for "+e["id"])
        if e["id"] in specialist:
            e["_standard_v2"]=specialist[e["id"]]
    pages={e["id"]+".md":create_page(e,legacy) for e in entries}
    assert len(pages)==300
    chunks=["# Reyes Problem Repository: 300 formal-review pages",
     "",
     "**Scope:** Every GC01–GC300 entry now has a separate review page with "
     "its source mathematical target, model and quantifier notes, resolution "
     "criteria, related prior-art leads, subproblem milestones, and explicit "
     "status recommendations. **These are first-pass research reviews, "
     "not 300 individually verified novel open problems or 300 completed proofs.**",
     "",
     "[Main roadmap](../ROADMAP_300.md) · "
     "[Verified exact-scope Lean results](../VERIFIED_LEAN_RESULTS.md) · "
     "[Original formal statements](../FORMAL_PROBLEMS.md) · "
     "[Scoped GC65–GC300 source dossiers](../scoped/README.md) · "
     "[Status registry](../STATUS.md)",
     "",
     "**Problem standard v2:** [23 case-specific revisions](REVIEW_QUEUE.md) "
     "include all 15 original P0 conceptual risks plus eight related cases. "
     "Several contain provisional exact analytic solutions, **not** "
     "Lean-checked new GC completions. [Six-part review contract](../PROBLEM_STANDARD.md).",
     "",
     "## Read the evidence labels carefully",
     "",
     "- **Source target:** the existing question or scope-v1 target is "
     "reproduced as mathematics; a screen cannot silently revise it.",
     "- **Literature leads:** published references verified as subject-related "
     "starting points, **not** a per-problem independent search or novelty certificate.",
     "- **Refined draft:** model, nonvacuity, prior-art or topology decisions "
     "remain before formal promotion.",
     "- **Withdraw/merge recommendation:** the exact finite or classical "
     "question may already be answered and deserves a proof record rather than "
     "an open-problem badge.",
     "- **Registry remains authoritative** and is not modified by this review layer.",
     "",
     "## Review index",
     ""]
    for area, subset in _groups(entries):
        chunks.append("### "+area.replace("-"," ").replace("  "," ").title())
        chunks.append("")
        chunks.append("| ID | Research target | Review recommendation |")
        chunks.append("|:--|:--|:--|")
        for e in subset:
            rec,_=recommendation(e,area,int(e["id"][2:]))
            if e.get("_standard_v2"):
                rec=e["_standard_v2"]["status"]
            chunks.append("| ["+e["id"]+"]("+e["id"]+".md) | "+e["title"].replace("|","/")+
                          " | "+rec+" |")
        chunks.append("")
    pages["README.md"]="\n".join(chunks)+"\n"
    counts=Counter(e["_audit"][0] for e in entries if e.get("_audit"))
    guide=[
        "# Problem standard: research-review completion queue",
        "",
        "**November 2, 2026.** The source corpus has 236 GC65–GC300 "
        "scoping records: **15 P0**, **98 P1***, **123 P1**. "
        "These are triage categories, not proof-progress percentages.",
        "",
        f"**Individual standard-v2 specialist reviews:** {len(specialist)}. "
        "All P0 items are included; the other P1* and P1 items retain "
        "their source-specific October 30 audit objections and original "
        "scope targets. **None is automatically promoted to verified open.**",
        "",
        "[Roadmap](../ROADMAP_300.md) · "
        "[Problem standard](../PROBLEM_STANDARD.md) · "
        "[October 30 audit](../SCOPING_AUDIT_GC65_GC300_2026-10-30.md) · "
        "[Exact Lean evidence](../VERIFIED_LEAN_RESULTS.md)",
        "",
        "## Individual review and evidence gates",
        "",
        "| ID | Audit | Review depth | Required mathematical gate |",
        "|:--|:--:|:--|:--|",
    ]
    for e in entries:
        if not e.get("_audit"):
            continue
        priority,objection=e["_audit"]
        depth=("Case-specific six-part review" if e.get("_standard_v2")
               else "Original scope + specific audit; specialist review pending")
        guide.append(f"| [{e['id']}]({e['id']}.md) | {priority} | {depth} | "
                     + objection.replace("|",r"\|")+" |")
    pages["REVIEW_QUEUE.md"]="\n".join(guide)+"\n"
    return pages


def _groups(entries):
    areas=[]
    for e in entries:
        name=e["file_path"].split("/")[1]
        if name not in areas:
            areas.append(name)
    for name in areas:
        yield name, [e for e in entries if e["file_path"].split("/")[1]==name]


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--write", action="store_true")
    p.add_argument("--check", action="store_true")
    args=p.parse_args()
    pages=build()
    existing={p.name:p.read_text(encoding="utf-8") for p in OUT.glob("*.md")}
    different=[name for name,content in pages.items() if existing.get(name)!=content]
    excess=sorted(set(existing)-set(pages))
    if args.write:
        OUT.mkdir(parents=True,exist_ok=True)
        for name in different:
            (OUT/name).write_text(pages[name],encoding="utf-8")
    print(f"GC research reviews: {len(pages)-2} GC review pages; "
          f"{len(different)} missing/outdated pages; {len(excess)} extra files.")
    if args.check and (different or excess):
        raise SystemExit("ERROR: generated formal-review pages are missing or out of date")
    if excess:
        raise SystemExit("ERROR: unexpected extra formal-review pages")


if __name__=="__main__":
    main()
