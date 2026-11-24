"""Keep the paper and the Lean development aligned.

The single source of truth is the `\\lean{...}` tag printed after each numbered statement of
`paper/main.tex`. This script

  * recomputes the statement numbers (theorem counter shared by all environments, per section);
  * accepts a numbered result without a tag only if it is explicitly marked `\\notformal`;
  * checks that every tagged name is declared in `lean/SOnMCMC/*.lean` and finds its module;
  * writes `lean/formalization.yaml` (schema v0.4, the format proofaudit reads);
  * writes `lean/audit/Axioms.lean`, one `#print axioms` per tagged declaration;
  * with `--check-axioms`, verifies `lean/audit/axioms.txt` (the output of running that file):
    every declaration must depend on `propext`, `Classical.choice`, `Quot.sound` at most.

Run from `papers/son-mcmc`:   python3 tools/alignment.py [--check-axioms]
"""

from __future__ import annotations

import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TEX = ROOT / "paper" / "main.tex"
LEAN = ROOT / "lean"
NUMBERED = {
    "theorem": "Theorem", "proposition": "Proposition", "lemma": "Lemma", "corollary": "Corollary",
    "definition": "Definition", "assumption": "Standing assumptions", "remark": "Remark",
    "example": "Example",
}
FORMAL = {"theorem", "proposition", "lemma", "corollary", "definition"}
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
MAIN_RESULTS = [
    ("dihedral_spectrum", "The eigenvalues of the walk on D_n are exactly a + b cos(2 pi k/n) +- c."),
    ("dihedral_poincare", "Poincare inequality on D_n with constant min(2c, b(1 - cos(2 pi/n)))."),
    ("dihedral_poincare_sharp", "The constant in the Poincare inequality on D_n is attained (n >= 2)."),
    ("gauss_isSpectralGap", "The spectral gap of the SO(2) sampler with N(0, v) proposals is 1 - E[cos theta(a)]."),
    ("gauss_isLeast_contraction", "E[cos theta(a)] is the least L2 contraction coefficient of the SO(2) sampler."),
    ("abs_one_sub_gaussLam_sub_le", "|gap - v/2| <= (3/2) v^2 for the SO(2) sampler."),
    ("markovOp_entry", "Matrix entries are eigenfunctions of conjugation-invariant walks on SO(n), eigenvalue E[tr R]/n."),
    ("gap_le_of_conjInvariant", "Spectral gap <= 1 - E[tr R]/n for conjugation-invariant walks on SO(n), n >= 2."),
    ("sampler_gap_le", "Spectral gap of the tangent-space sampler on SO(n) is at most (n - 1) sigma^2."),
    ("abs_so3CharRatio_le", "SO(3) character ratios: |chi_l|/(2l+1) <= chi_1/3 on rotation angles in [0, pi/2]."),
    ("so2_isSpectralGap", "The spectral gap of the sampler on the matrix group SO(2) is 1 - E[cos theta(a)]."),
    ("exists_principal_iff", "A principal root (orthogonal, skew part A, PSD symmetric part) exists iff 1 + A^2 is PSD."),
    ("tendsto_newtonFrozen", "Newton's iteration with frozen Jacobian converges to the principal root when 1 + A^2 is PSD."),
    ("zhgMove_eq", "One move of the Zappa-Holmes-Cerfon-Goodman sampler on O(n), with reverse check and MH test, is X -> X R(A)."),
    ("gaussSOStep_conjInvariant", "The step law of the Gaussian tangent-space sampler on SO(n) is conjugation invariant."),
    ("gaussSO_gap_le", "Spectral gap of the Gaussian tangent-space sampler on SO(n) is at most (n - 1) sigma^2 (no hypotheses)."),
    ("markovOp_of_mem_harm", "SU(2): the span of k-th powers of linear forms is an eigenspace of every conjugation-invariant walk."),
    ("su2Eig_mul_sin", "SU(2): (k+1) lambda_k sin(alpha) = sin((k+1) alpha) when the trace is 2 cos(alpha) (Weyl character formula)."),
    ("cover_surjective", "The quaternionic map SU(2) -> SO(3) is surjective."),
    ("so3_isSpectralGap", "SO(3): for conjugation-invariant steps with PSD symmetric part the spectral gap is exactly 1 - E[tr R]/3."),
    ("so3_isLeast_contraction", "SO(3): E[tr R]/3 is the least L2 contraction coefficient."),
    ("gaussSO_three_isSpectralGap", "The spectral gap of the Gaussian tangent-space sampler on SO(3) is exactly 1 - E[tr R]/3."),
    ("gap_le_one_sub_minorEig", "SO(n), n >= 3: spectral gap <= 1 - E[R_ii R_jj - R_ij R_ji] (two-by-two minors are eigenfunctions)."),
    ("so4_counterexample", "SO(4): a conjugation-invariant step law with PSD symmetric part whose gap is < 1 - E[tr R]/4."),
    ("abs_cosSumDeriv_le", "Gradient bound on the torus: |d/dtheta_k sum_a w_a prod_l cos(mu_al theta_l)| <= (sum_a w_a mu_ak^2) |sin theta_k| for w >= 0, mu integral."),
    ("gradient_domination", "The pointwise gradient comparison behind gap = 1 - E[tr R]/n on SO(n) for angle-monotone step laws."),
    ("gaussAngleDensity_antitoneOn", "The Haar density of the Gaussian step law on SO(n) is nonincreasing in the rotation angles on [0, pi]^m."),
]


def statements() -> list[dict]:
    text = TEX.read_text()
    body = text[text.index(r"\begin{document}"):]
    out, section, counter = [], 0, 0
    token = re.compile(r"\\section\{|\\begin\{(" + "|".join(NUMBERED) + r")\}(\[[^\]]*\])?")
    pos = 0
    while True:
        m = token.search(body, pos)
        if not m:
            break
        pos = m.end()
        if m.group(0).startswith(r"\section"):
            section += 1
            counter = 0
            continue
        env = m.group(1)
        counter += 1
        end = body.index(rf"\end{{{env}}}", pos)
        block = body[pos:end]
        title = (m.group(2) or "")[1:-1]
        title = re.sub(r"\$\\SO\((\w)\)\$", r"SO(\1)", title)
        title = re.sub(r"\\texorpdfstring\{[^}]*\}\{([^}]*)\}", r"\1", title).replace("$", "")
        label = re.search(r"\\label\{([^}]*)\}", block)
        names = []
        for tag in re.findall(r"\\lean\{([^}]*)\}", block):
            names += [n.strip() for n in tag.split(",") if n.strip()]
        out.append({
            "env": env, "number": f"{section}.{counter}", "title": title,
            "label": label.group(1) if label else None, "names": names,
            "formal": env in FORMAL and "\\notformal" not in block,
            "marked": "\\notformal" in block,
        })
    return out


def declarations() -> dict[str, str]:
    """Declared name -> module, from the Lean sources."""
    decl = re.compile(
        r"^(?:@\[[^\]]*\]\s*)*(?:noncomputable\s+|private\s+|protected\s+)*"
        r"(?:theorem|lemma|def|abbrev|instance|structure)\s+([^\s:(\[{]+)", re.M)
    found: dict[str, str] = {}
    for f in sorted((LEAN / "SOnMCMC").glob("*.lean")):
        module = f"SOnMCMC.{f.stem}"
        for m in decl.finditer(f.read_text()):
            found.setdefault(m.group(1), module)
    return found


def yaml_str(x: str) -> str:
    return '"' + x.replace("\\", "\\\\").replace('"', '\\"') + '"'


def main() -> int:
    stmts = statements()
    decls = declarations()
    problems = []
    for s in stmts:
        if s["formal"] and s["env"] != "definition" and not s["names"]:
            problems.append(f"{NUMBERED[s['env']]} {s['number']} has no \\lean tag and is not marked \\notformal")
        if not s["formal"] and s["names"]:
            problems.append(f"{NUMBERED[s['env']]} {s['number']} is not formalized but has a \\lean tag")
        if s["env"] in ("remark", "example") and not s["marked"]:
            problems.append(f"{NUMBERED[s['env']]} {s['number']} is not marked \\notformal")
        for n in s["names"]:
            if n not in decls:
                problems.append(f"{NUMBERED[s['env']]} {s['number']}: `{n}` is not declared in lean/SOnMCMC")
    for n, _ in MAIN_RESULTS:
        if n not in decls:
            problems.append(f"main result `{n}` is not declared in lean/SOnMCMC")

    tagged = []
    for s in stmts:
        for n in s["names"]:
            if n not in tagged:
                tagged.append(n)

    # ---- audit file
    audit = LEAN / "audit"
    audit.mkdir(exist_ok=True)
    (audit / "Axioms.lean").write_text(
        "import SOnMCMC\n\n/-! Generated by `tools/alignment.py`: one line per declaration cited in the paper. -/\n\n"
        + "".join(f"#print axioms SOnMCMC.{n}\n" for n in tagged))

    # ---- formalization.yaml
    lines = [
        "# yaml-language-server: $schema=https://raw.githubusercontent.com/mathlib-initiative/formalization.yaml/main/schema/formalization.schema.json",
        "# Generated by tools/alignment.py from the \\lean{...} tags of paper/main.tex. Do not edit by hand.",
        'version: "v0.4"',
        "",
        "project:",
        '  name: "SOnMCMC"',
        "  description: >-",
        "    Lean 4 formalization of the numbered statements of the paper \"Markov Chain Monte Carlo",
        "    on SO(n) via Representation Theory\": random walks on finite and compact groups, the",
        "    spectrum of a walk on the dihedral group, the exact spectral gap of the tangent-space",
        "    sampler on SO(2) and SO(3), the construction of the sampler (principal root, Newton",
        "    iteration, conjugation invariance), eigenfunctions and spectral gap bounds on SO(n),",
        "    a counterexample on SO(4), and the gradient bound and angle density behind the exact",
        "    spectral gap on SO(n) (whose proof, via Peter-Weyl, is not formalized).",
        "  authors:",
        '    - "Daniel Kenigsberg"',
        '    - "Avi Ray"',
        "",
        "sources:",
        '  - title: "Markov Chain Monte Carlo on SO(n) via Representation Theory"',
        '    id: "../paper/main.pdf"',
        "    authors:",
        '      - "Daniel Kenigsberg"',
        '      - "Avi Ray"',
        '    type: "article"',
        '    location: "Numbered propositions, lemmas, theorems and corollaries not marked (not formalized)"',
        '    relationship: "formalizes"',
        "",
        "classification:",
        "  msc2020:",
        '    - "60J10"',
        '    - "60B15"',
        '    - "65C05"',
        '    - "22E46"',
        "",
        "status:",
        "  scope: >-",
        "    Every numbered proposition, lemma, theorem and corollary of the paper except "
        + ", ".join(f"{NUMBERED[s['env']]} {s['number']}" for s in stmts
                    if s["env"] in FORMAL and not s["formal"]) + ",",
        "    which are marked \"(not formalized)\" in the paper (their proofs use the Peter-Weyl",
        "    theorem; the lemmas carrying their computations are formalized). Remarks and examples",
        "    marked \"(not formalized)\" are also out of scope. All exceptions are listed in Section 8",
        "    of the paper.",
        "  sorry_count: 0",
        "  sorry_in_definitions: 0",
        "  main_results:",
    ]
    for n, desc in MAIN_RESULTS:
        module = decls.get(n, "SOnMCMC")
        lines += [
            f"    - description: {yaml_str(desc)}",
            f"      declaration: {yaml_str('SOnMCMC.' + n)}",
            f"      file: {yaml_str(module.replace('.', '/') + '.lean')}",
            "      sorry_count: 0",
            "      axioms:",
            '        - "propext"',
            '        - "Classical.choice"',
            '        - "Quot.sound"',
        ]
    lines += [
        "",
        "automation:",
        "  methods:",
        '    - method: "agent"',
        "      models:",
        '        - "Claude"',
        '      framework: "Claude Code"',
        "",
        "review:",
        '  status: "self-assessed"',
        "",
        "alignment:",
        "  namespaces:",
        '    - "SOnMCMC"',
        "  statements:",
    ]
    for s in stmts:
        head = f"{NUMBERED[s['env']]} {s['number']}" + (f" ({s['title']})" if s["title"] else "")
        if not s["formal"]:
            continue
        for n in s["names"]:
            lines += [
                f"    - source: {yaml_str(head)}",
                f"      lean: {yaml_str('SOnMCMC.' + n)}",
                f"      module: {yaml_str(decls.get(n, '?'))}",
                f"      status: {yaml_str('definition' if s['env'] == 'definition' else 'proved')}",
            ]
    lines += [
        "",
        "not_formalized:",
    ]
    for s in stmts:
        if not s["formal"]:
            head = f"{NUMBERED[s['env']]} {s['number']}" + (f" ({s['title']})" if s["title"] else "")
            lines.append(f"  - {yaml_str(head)}")
    (LEAN / "formalization.yaml").write_text("\n".join(lines) + "\n")

    formal = [s for s in stmts if s["formal"] and s["env"] != "definition"]
    unformal = [s for s in stmts if s["env"] in FORMAL and not s["formal"]]
    print(f"{len(formal)} formalized numbered results, {sum(s['env'] == 'definition' for s in stmts)} definitions, "
          f"{len(tagged)} Lean declarations cited, "
          f"{sum(s['env'] in ('remark', 'example') for s in stmts)} remarks/examples (not formalized)")
    for s in unformal:
        print(f"not formalized (marked in the paper): {NUMBERED[s['env']]} {s['number']} ({s['title']})")

    if "--check-axioms" in sys.argv:
        out = audit / "axioms.txt"
        if not out.exists():
            problems.append("lean/audit/axioms.txt is missing: run `lake env lean audit/Axioms.lean > audit/axioms.txt`")
        else:
            text = out.read_text()
            seen = {}
            for m in re.finditer(r"'SOnMCMC\.([^']+)' (depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", text):
                seen[m.group(1)] = {a.strip() for a in (m.group(3) or "").split(",") if a.strip()}
            for n in tagged:
                if n not in seen:
                    problems.append(f"no axiom report for `{n}`")
                elif not seen[n] <= ALLOWED_AXIOMS:
                    problems.append(f"`{n}` depends on {sorted(seen[n] - ALLOWED_AXIOMS)}")
            if re.search(r"error|sorryAx", text):
                problems.append("lean/audit/axioms.txt contains an error or sorryAx")
            print(f"axiom reports: {len(seen)}; all within {sorted(ALLOWED_AXIOMS)}: "
                  f"{all(v <= ALLOWED_AXIOMS for v in seen.values())}")

    for p in problems:
        print("PROBLEM:", p)
    return 1 if problems else 0


if __name__ == "__main__":
    raise SystemExit(main())
