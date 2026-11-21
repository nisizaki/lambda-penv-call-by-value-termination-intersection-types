# Call-by-Value Termination of λpenv and its Characterization by Intersection Types

Isabelle/HOL formalization of call-by-value termination for the calculus λpenv and its
characterization by intersection types.

λpenv extends the calculus λenv of first-class environments with *quoted names* `⌜x⌝`,
so that functions and environments can be used interchangeably:

- looking up a variable `x` in a function `λy.M` applies the function to the quoted
  name: `x∘(λy.M) → M∘(⌜x⌝/y·id)`;
- applying an environment to a quoted name looks the name up: `E ⌜x⌝ → x∘E`.

This development combines call-by-value λenv with the name rules of call-by-name
λpenv (see [Related repositories](#related-repositories)).

Authors: Shin-ya Nishizaki and Shogo Murasaki.

## Main result

For every term `M` of λpenv (theory `Main_Results`):

```
theorem main_characterization:    "Typ M ⟷ CFN M"
theorem main_characterization_SN: "Typ M ⟷ CFSN M"
theorem Typ_imp_SN:               "Typ M ⟹ SN_at cbv M"
```

- `Typ M`: `M` has an essential type in the intersection type system with ω,
  environment types and name types `QN x`, in an environment-type context that
  contains no name types. As in call-by-value λenv, the argument of an application
  must have an essential type.
- `CFN M`: `M` reduces to a normal form that is a fireball, i.e. a clash-free
  normal form.
- `CFSN M`: every `→v`-reduction sequence from `M` is finite, and every normal form
  reachable from `M` is a fireball.

### Conservativity

- On sorted λenv terms (terms and environments kept apart, no quoted names), the
  reduction coincides with call-by-value λenv (`sorted_cbv_iff`), and typability
  coincides with call-by-value λenv normalizability (`conservative_Typ`).
- For a pure λ-term, typability coincides with normalization of its readback in
  left-to-right open call-by-value, the fireball calculus (`conservativity`).

## The calculus

Terms: `x | λx.M | M N | id | M/x·N | M∘N | ⌜x⌝` (constructor `Nm x` for `⌜x⌝`).

- **σ-reduction** (all positions), nine rules:
  - the seven λenv rules;
  - `AppConst`: `M ⌜x⌝ → x∘M`;
  - `ConstComp`: `⌜x⌝∘L → ⌜x⌝`.
- **Fireballs**: inert terms (`x`, `I F`, `x∘I`) and values. The values are
  abstractions, closures, `id`, extensions and quoted names.
- **β_v**, with four root rules:
  - `Beta1` and `Beta2`, whose argument must be a fireball;
  - `VarClos`: `x∘((λy.M)∘L) → M∘(⌜x⌝/y·L)`;
  - `VarLam`: `x∘(λy.M) → M∘(⌜x⌝/y·id)`.

  Its congruences are AppL, AppR (when the function part is a fireball) and VarR.
  It is deterministic and left-to-right. Environments are lazy.
- `→v = →σ ∪ →β`. With all congruences this is the reduction of λpenv.

## Theories

The session `LambdaPEnvCBV` (directory `isabelle/`) has 15 theories.

| Theory | Contents | Main results |
| --- | --- | --- |
| `ARS`, `Syntax` | abstract rewriting, terms | |
| `Sigma`, `Sig_Confluence` | σ-reduction, termination, confluence | `sig_SN`, `sig_confluent` |
| `Reduction` | fireballs, β_v, call-by-value reduction | `sig_fb`, `beta_det` |
| `Uniform` | commutation, uniform normalization, forward closure | `CFN_iff_CFSN`, `NF_unique`, `CFN_fwd`, `Nm_fwd` |
| `Typing` | types (incl. name types), subtyping, typing, generation | `narrowing`, `gen_*` |
| `Completeness` | subject expansion with name-free context refinement | `completeness` |
| `Soundness` | realizability interpretation | `soundness` |
| `Main_Results` | main theorems | `main_characterization`, `main_characterization_SN`, `Typ_imp_SN`, `clash_not_Typ` |
| `Examples` | examples | |
| `Sorted`, `Conservative` | sorted terms, the call-by-value λenv fragment | `sorted_cbv_iff`, `conservative_Typ` |
| `Lambda`, `Readback` | open call-by-value, readback | `conservativity_sorted`, `conservativity` |

The theories contain no `sorry`, `oops`, `axiomatization` or `consts`. The session is
built with `quick_and_dirty` and `skip_proofs` disabled. ML blocks in `Main_Results`
and `Readback` fail the build if the main theorems depend on any oracle.

## Building

Requires [Isabelle2025-2](https://isabelle.in.tum.de/).

```bash
isabelle build -d isabelle LambdaPEnvCBV
```

To also produce the theory documents (requires LaTeX):

```bash
isabelle build -o document=pdf -d isabelle LambdaPEnvCBV
```

The output is written to `isabelle/output/`.

## Files

```
isabelle/ROOT              session LambdaPEnvCBV
isabelle/*.thy             the 15 theories
isabelle/document/root.tex LaTeX root of the theory document
docs/document.pdf          theory document: all theories with proofs
docs/outline.pdf           theory document: all theories with proofs omitted
```

## Related repositories

- Lean 4 port of this development (one file per theory, same definitions and theorem
  names, no `sorry`, only Lean's standard axioms):
  [lambda-penv-call-by-value-termination-intersection-types-lean](https://github.com/nisizaki/lambda-penv-call-by-value-termination-intersection-types-lean)
- Call-by-value λenv:
  [lambda-env-call-by-value-termination-intersection-types](https://github.com/nisizaki/lambda-env-call-by-value-termination-intersection-types)
  ([Lean 4](https://github.com/nisizaki/lambda-env-call-by-value-termination-intersection-types-lean))
- Call-by-name λpenv:
  [lambda-penv-weak-head-normalizability-intersection-types](https://github.com/nisizaki/lambda-penv-weak-head-normalizability-intersection-types)
  ([Lean 4](https://github.com/nisizaki/lambda-penv-weak-head-normalizability-intersection-types-lean))
- λpenv and the confluence of its weak reduction:
  [lambda-penv-confluence-public](https://github.com/nisizaki/lambda-penv-confluence-public)
- Call-by-name λenv:
  [lambda-env-weak-head-normalizability-intersection-types](https://github.com/nisizaki/lambda-env-weak-head-normalizability-intersection-types)

## How to cite

Shin-ya Nishizaki and Shogo Murasaki.
*Call-by-Value Termination of λpenv, a Calculus Mixing Functions and Environments, and
its Characterization by Intersection Types, Formalized in Isabelle/HOL.*
