# A covering system with minimum modulus 44 — Lean 4 proof

This repository contains a machine-checked proof, in Lean 4, that there is a **covering system of the integers with
pairwise distinct moduli whose least modulus is 44**.

```lean
theorem UC85.minimumModulus44 : UC85.MinimumModulusN 44
```

`MinimumModulusN n := ∃ cs, IsCoveringSystem cs ∧ HasSmallestModulus cs n`. It unfolds (by `Iff.rfl`) to the plain
statement: there is a finite list of congruence classes `a mod m` over `ℤ` such that every integer lies in at least
one of them, the moduli are pairwise distinct, every modulus is greater than 1, and the least modulus is exactly 44.
For `n = 42` it is definitionally the statement `Modulus42.MinimumModulus42` of
[gr-mk/modulus-40-lean](https://github.com/gr-mk/modulus-40-lean). The expanded form
`UC85.exists_distinct_covering_minimum44` is also proved.

Nielsen (2009) constructed a covering system with least modulus 40, and Owens (2014) extended the method to 42.
This system builds on a variant of Owens's construction. The accompanying paper,
[`paper/covering44.pdf`](paper/covering44.pdf) (LaTeX source: `paper/covering44.tex`), describes the steps to 43 and
44 and how the result was verified.

## Checking the proof

Toolchain and dependencies are pinned: `leanprover/lean4:v4.24.0` and Mathlib `v4.24.0` (`lake-manifest.json`).

```sh
lake exe cache get          # Mathlib build cache
lake build                  # default target Covering44 = UC85.W.U.Main44 and everything it imports
lake env lean Audit44.lean  # axiom audit (#guard_msgs): [propext, Classical.choice, Quot.sound]
```

**Resources.** The proof has 7,963 Lean files, 7,933 of them generated. The reference build took about 250 CPU-hours
(8.8 h wall-clock at 28 parallel jobs on a 32-thread, 125 GB machine).
- Most modules need 1–6 GB of memory.
- The `Rays` module needs about 19 GB.
- The three largest local tables (primes 197, 199 and 211) peak at 24–28 GB each.

Limit Lake's parallelism so that concurrent modules fit in memory.

## What is in the repository

| Path | Contents |
|---|---|
| `Covering44.lean` | Library root; imports the main theorem. |
| `Audit44.lean` | Axiom audit of `minimumModulus44` and `exists_distinct_covering_minimum44`. |
| `Modulus40/` | 21 core modules of gr-mk/modulus-40-lean at commit `188620e`, unchanged: arrows and rays, their semantics, local data, the RUP certificate checkers and the finite reduction. |
| `UC85/FlatDefs.lean`, `FlatSound.lean`, `Flat.lean` | Flat covering checks: a CNF over local atoms whose unsatisfiability implies coverage. |
| `UC85/BitRUP.lean` | Bitmask RUP checker, one theorem per proof step. |
| `UC85/Glue.lean` | Section glue (covering of ℤ assembled from section checks) and box-tree walks (pairwise distinct moduli). |
| `UC85/Walk6.lean` | Box-tree walks with a 6-bit prime field (the system uses 47 primes). |
| `UC85/LocalChunks.lean` | `valid_of_chunks`: chunked verification of local data. It concludes upstream's `LocalData.Valid`. |
| `UC85/ReductionN.lean` | Finite completion for any least modulus `2 ≤ n ≤ 64` and any fresh prime `P`. It truncates rays at a common depth and caps the ray centres with `P`. |
| `UC85/W/` | Generated data and checks for the 44 system. |

The generated data and checks in `UC85/W/` are:
- the atom tables over 47 primes and the 618,413-family pattern table;
- 61 CNF certificates (sections and roots) replayed by `BitRUP`, 22.3 M proof hints in all;
- the box-tree walks for distinct moduli;
- the least-modulus blocks (witness: family #89, modulus 44);
- `U/Main44.lean`, where `n = 44` and the fresh completion prime is `P = 223`.

## Provenance and integrity

- `AUDITED-SHA256SUMS.txt` lists 7,965 files: every Lean source plus `lean-toolchain` and `lake-manifest.json`.
  Each is byte-identical to the build that was compiled and independently audited on 2026-09-27.
  Run `sha256sum -c AUDITED-SHA256SUMS.txt` to check.
- Only three files differ from that build: `lakefile.toml` (package name, default target, and the `Covering44`
  library), `Covering44.lean` and this README.
- **Independent audit.** Every item was confirmed:
  - the build is up to date;
  - the axioms are only `propext`, `Classical.choice` and `Quot.sound`;
  - the statement is equivalent to a from-scratch restatement;
  - the theorem is a closed term: `n = 44` and `P = 223` are instantiated, and primality and freshness are proved inside;
  - no `sorry`, `native_decide`, `axiom`, `unsafe`, `extern` or kernel-skipping options appear anywhere.
- **Kernel re-checks** (lean4checker's replay), all accepted:
  - the audit sample of 130 modules (68,799 declarations), including every check assembly and all glue, main and
    reduction modules;
  - a full replay, paused at 5,380 of 7,962 modules with 0 rejections.
- Before the Lean build, the covering was verified exactly by two independent engines. Both found the global CNF
  unsatisfiable, with proofs checked by drat-trim, an LRAT replay and kissat. Both found no repeated modulus, by box
  sweep and by brute-force expansion of all moduli up to 10¹².

Derived from [gr-mk/modulus-40-lean](https://github.com/gr-mk/modulus-40-lean) (Lean proof of Nielsen's modulus-40
covering), commit `188620ea8278744368f1e86102a0de30d8f9062d`. The search, certification and Lean engineering were done
with the help of Claude (Anthropic).
