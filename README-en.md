[English](README-en.md) | [Japanese](README.md)

# Formalizing the non-terminating variants of the Bashicu Matrix System

For the rule sets marked as non-terminating in [the classification of the variant rules of the Bashicu Matrix](https://googology.fandom.com/ja/wiki/%E3%83%A6%E3%83%BC%E3%82%B6%E3%83%BC%E3%83%96%E3%83%AD%E3%82%B0:Koteitan/%E3%83%90%E3%82%B7%E3%82%AF%E8%A1%8C%E5%88%97%E3%81%AE%E4%BA%9C%E7%A8%AE%E3%83%AB%E3%83%BC%E3%83%AB%E3%81%AE%E5%88%86%E9%A1%9E) (in Japanese; [English version](https://googology.fandom.com/wiki/User_blog:Koteitan/Categorizing_of_the_rule_sets_for_all_sub_versions_of_bashicu_matrix)), this project proves in Lean 4 that the listed non-terminating examples do not terminate.

## Results

For each example the following is proved.

1. The matrix $`M`$ of the example is standard for the rule set: it is reached from $`(0,\dots,0)(1,\dots,1)`$ by expansions.
2. For every $`n \ge 1`$, the computation $`(M, n) \mapsto (M[f(n)], f(n))`$ starting from $`M[n]`$ never reaches the empty matrix.
3. $`M`$ has an infinite descending sequence of expansions.

| rule set | non-terminating example | source | explanation |
|---|---|---|---|
| BM1 | `(0,0,0)(1,1,1)(2,0,0)(1,1,0)(2,1,0)(3,1,0)` | hyp cos | [doc/BM1/1](doc/BM1/1/README-en.md) |
| BM1 | `(0,0)(1,1)(2,2)(3,0)(2,1)(3,1)(4,1)` | Bubby3 | [doc/BM1/2](doc/BM1/2/README-en.md) |
| rTSS | example 1 of BM1 | (the rules of BM1) | [doc/rTSS](doc/rTSS/README-en.md) |
| BM1.1 | `(0,0,0)(1,1,1)(2,0,0)(1,1,1)` | hyp cos | [doc/BM1.1](doc/BM1.1/README-en.md) |
| BM2.1 | the example of BM1.1 | (the expansion rules of BM1.1) | [doc/BM2.1](doc/BM2.1/README-en.md) |
| Bubby3's fix | the example of BM1.1 | (the rules of BM1.1) | [doc/Bubby3fix](doc/Bubby3fix/README-en.md) |
| BM2 | `(0,0,0,0)(1,1,1,1)(2,2,1,1)(3,3,1,1)(4,2,0,0)(5,1,1,1)(6,2,1,1)(7,3,1,1)` | Bubby3 | [doc/BM2](doc/BM2/README-en.md) |
| BM3 | `(0,0,0)(1,1,1)(2,1,1)(1,1,1)` | Alemagno12 | [doc/BM3](doc/BM3/README-en.md) |

- Common definitions, the proof framework and the sources: [doc/README-en.md](doc/README-en.md)
- How the rules of the classification page are defined in Lean: [doc/rules-en.md](doc/rules-en.md)

The following rule sets are not covered.

- The page only says "considered broken" or "expected not to terminate": BM3.1, BM3.2, BM3.1.1.
- The page does not say they do not terminate: BM4, BM2.3, BM2.2.

## Approach

For each example, a family $`S`$ of matrices containing $`M`$ is constructed, and the following is shown.

```math
\forall X \in S,\ \forall n \ge 1,\ \exists Y \in S,\ Y \sqsubseteq X[n]
```

($`\sqsubseteq`$ is the prefix order.)

An expansion keeps every column except the last one. So the computation either returns exactly to $`Y`$, or keeps $`Y`$ as a proper prefix forever. Non-termination follows ([doc/README-en.md](doc/README-en.md)).

The definitions are checked to match the intent of the page in two ways.

- The expansion traces written in the sources are reproduced by `decide`.
- For BM1.1 and BM2, 144 expansions agree with the output of [yaBMS](https://github.com/koteitan/yaBMS).

## Build

Install Lean 4 (v4.33.1) with [elan](https://github.com/leanprover/elan), then run the following. Mathlib is not used.

```sh
cd lean
lake build
```

`lake build` checks all the theorems and the tests (the traces of the sources and the comparison with yaBMS). The axioms used by the main theorems can be printed by `lean/Test/Axioms.lean`; they are only `propext`, `Classical.choice` and `Quot.sound`.

## Directory structure

```
lean/
  Common/            common definitions and lemmas
    Matrix.lean        matrices, lowest nonzero row, Δ, appending zero rows
    BadRoot.lean       bad root search (left-adjacent method, Upper-Branch-Ignoring Model)
    Ascend.lean        bad part ascension (all branches, BM2, BM3)
    Expand.lean        expansion, computation, halting, standard form
    Rules.lean         the seven rule sets
    Loop.lean          general lemma: a looping family implies non-termination
    Lemmas.lean        lemmas for computing expansions
    Ubim.lean          lemmas on parents and ancestors of the Upper-Branch-Ignoring Model
    Pad.lean           appending zero rows does not change expansions
  BM1/1/ BM1/2/ BM1.1/ BM2/ BM3/
    Standard.lean      the standardness path
    Loop.lean          the looping family
    Trace.lean         the traces of the source
    Main.lean          the main theorem
  rTSS/ BM2.1/ Bubby3fix/
    Main.lean          corollaries
  Test/              comparison with yaBMS, check of axioms
  Explore/           #eval scripts for exploration (not built)
doc/                 explanations of the proofs (Japanese README.md, English README-en.md)
tools/               generator of the yaBMS comparison test
```
