# Antihydra has no semilinear inductive safety invariant

Start at `(8, 0)` in the natural-number state space `(x, c)`, where `c`
is credit. Every successful round replaces `x` by `⌊3x/2⌋`. Even `x`
adds two to the credit. Odd `x` spends one unit if available and halts
otherwise. An inductive safety invariant contains the seed and gives
every member a successful successor in the set.

No semilinear subset of this state space is an inductive safety invariant.
Mathlib expresses semilinearity as a finite union of translates of finitely
generated additive submonoids. The Solution also derives the consequence
for Presburger-definable sets with arbitrary natural-number parameters.
The result concerns certificates in these state coordinates. Whether the
seed halts remains open in this work.

| Comparator configuration | Statement | Proof | Selected declaration |
| --- | --- | --- | --- |
| [comparator.json](comparator.json) | [Challenge.lean](Challenge.lean) | [Solution.lean](Solution.lean) | `AntihydraPalomar.no_semilinear_safety_invariant` |

## Proof

Every horizontal ray `(a + jd, c)` with `d > 0` contains a state that
halts within `c + 3v₂(d) + 1` rounds, including the attempted round
with insufficient credit. Until the stride becomes odd, all members of
the ray have the same parity at each round. Each successful round then
replaces an even stride `2e` by `3e` and adds at most two to the common
credit. Once the stride is odd, the ray contains a value congruent to
one modulo `2^(c' + 1)`, where `c'` is the remaining credit. That value
forces `c' + 1` odd inputs and overspends.

A linear component with a positive horizontal generator contains such a
ray. In each component without one, every generator that increases `x`
also increases credit. Bounding the contributions of those generators and
the base point yields `x ≤ K(c + 1)`, and a finite union preserves that
form of bound. A safety invariant must contain a state after every `t`
rounds, with `c ≤ 2t` and `x ≥ (t + 1)^2`. At `t = 3K + 1` this
contradicts the affine bound.

## Sources and scope

- Shawn Ligocki, *BB(6) is Hard (Antihydra)* (2024), gives the shifted
  recurrence and its tape interpretation. The post is cited for the
  arithmetic model. Its reuse license was unverified.
  [Ligocki's post](https://www.sligocki.com/2024/07/06/bb-6-2-is-hard.html)
- Google LLC's `cryptids` formalization identifies blank-tape halting with
  halting of a symbolic system from `P(0,3,1)`. Bryan Ehrlich's earlier
  `AntihydraSemilinear.lean` developed the arithmetic proof presented here
  and proved the round correspondence from `(x,c)` to `P(c,x-5,1)` for
  `x ≥ 6`, a guard preserved from the seed. This entry uses the bridge as
  context for the arithmetic invariant theorem. The upstream Lean source
  is Apache-2.0.
  [Pinned machine reduction](https://github.com/google-deepmind/cryptids/blob/3647718b5df22e1a61462dec0376bd204526285a/BusyBeaver/BB6/M_1RB1RA_0LC1LE_1LD1LC_1LA0LB_1LF1RE_HHH0RA.lean),
  [upstream license](https://github.com/google-deepmind/cryptids/blob/3647718b5df22e1a61462dec0376bd204526285a/LICENSE)
- The classical Presburger–semilinear characterization is due to Ginsburg
  and Spanier. Mathlib supplies its Lean statement and proof. The dependency
  is Apache-2.0. The paper is cited bibliographically and its reuse license
  was unverified.
  [Mathlib formalization and bibliography](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/ModelTheory/Arithmetic/Presburger/Definability.lean)
- The prior comparison also examined the arithmetic work in
  `Antihydra-Basics` (CC0-1.0). Community context includes the Antihydra
  wiki and Dafny proof (CC BY 4.0) and busycoq (MIT).
  [Antihydra-Basics](https://github.com/rwst/Antihydra-Basics/tree/5dd5aed030d9aed020696ad1d628848f9f9962b7),
  [Antihydra wiki](https://wiki.bbchallenge.org/wiki/Antihydra),
  [busycoq](https://github.com/meithecatte/busycoq)

The reduction literature describes the computation to analyze. The
obstruction gives a limit on how that computation can be certified: even
arbitrary finite unions of affine periodic sets on the natural state
coordinates fail as inductive safety certificates. The quantitative ray
bound explains the failure for all periods and credits, so the theorem
is a candidate for a short note in Busy Beaver research or arithmetic
program verification. The comparison with the pinned DeepMind and
Antihydra-Basics revisions found no matching obstruction. Priority
beyond that bounded comparison remains open.

## Provenance and verification

Bryan Ehrlich is the author and responsible maintainer. The research
assignment credits the Astra reasoning tool for the argument. OpenAI Codex
with GPT-6.2 Sol assisted with the antecedent Lean proof. Codex also prepared
this package. A separate GPT-6.1 Terra agent reviewed the antecedent proof
through Codex.
The package prescreen is a Codex assessment. These checks are automated
and independent human peer review remains outstanding.

## Submission checklist

The file list follows the Palomar composition-algebra entry format. The
structured metadata and attribution follow the Palomar Policy metadata guidance.

| Item | Files and details |
| --- | --- |
| Trusted statement and proved solution | [Challenge.lean](Challenge.lean) states `AntihydraPalomar.no_semilinear_safety_invariant` against Mathlib. [Solution.lean](Solution.lean) proves it. |
| Comparator configuration | [comparator.json](comparator.json) selects that declaration and enables the independent nanoda kernel. |
| Reproducible Lake project | [lakefile.toml](lakefile.toml), [lake-manifest.json](lake-manifest.json), and [lean-toolchain](lean-toolchain) pin Lean `leanprover/lean4:v4.35.0` and Mathlib `v4.35.0` (`56a005855ea17e0b0958f73ec801ae140b0a1679`). |
| Axiom audit | [AxiomAudit.lean](AxiomAudit.lean) checks every imported Solution declaration and prints the three theorem closures. |
| Registry metadata and narrative | [formalization.yaml](formalization.yaml) and this README record the result, authorship, classifications, sources, automation, and scope. |
| License and attribution | Bryan Ehrlich is the author and responsible maintainer. The original Lean and documentation files are Apache-2.0, with attribution in [NOTICE](NOTICE). |

From this directory, build and audit with the pinned dependencies.

```bash
lake build
lake env lean AxiomAudit.lean
```

The single `sorry` in Challenge is the statement placeholder. The
audit enforces the allowlist `propext`, `Classical.choice`, and
`Quot.sound` and checks the exact axiom lists for the ray bound, the main
theorem, and the Presburger corollary.

The local Comparator run exited successfully and printed
`Your solution is okay!`. The log records
`nanoda kernel accepts the solution` and
`Lean default kernel accepts the solution`. Hosted registry intake is pending.

The run used Comparator `575674928e239f5bc452aab72d1dd7b0f1326494`,
lean4export `5a9a355dc6c5fd82b69058d433e2ae2e8dfbf8fe`,
nanoda `68d5ca9db226849b41a6fff59d796ff19d0a8840`, and
landrun `811cfff51ceaf3d9843708aa6d22e9b84ccac8b4`.
