<!---
This file was generated from `meta.yml`, please do not edit manually.
Follow the instructions on https://github.com/coq-community/templates to regenerate.
--->
# Tarjan and Kosaraju

[![Docker CI][docker-action-shield]][docker-action-link]
[![Contributing][contributing-shield]][contributing-link]
[![Code of Conduct][conduct-shield]][conduct-link]
[![Zulip][zulip-shield]][zulip-link]

[docker-action-shield]: https://github.com/math-comp/tarjan/workflows/Docker%20CI/badge.svg?branch=master
[docker-action-link]: https://github.com/math-comp/tarjan/actions?query=workflow:"Docker%20CI"

[contributing-shield]: https://img.shields.io/badge/contributions-welcome-%23f7931e.svg
[contributing-link]: https://github.com/coq-community/manifesto/blob/master/CONTRIBUTING.md

[conduct-shield]: https://img.shields.io/badge/%E2%9D%A4-code%20of%20conduct-%23f15a24.svg
[conduct-link]: https://github.com/coq-community/manifesto/blob/master/CODE_OF_CONDUCT.md

[zulip-shield]: https://img.shields.io/badge/chat-on%20zulip-%23c1272d.svg
[zulip-link]: https://coq.zulipchat.com/#narrow/stream/237663-coq-community-devs.20.26.20users



This development contains formalizations and correctness proofs, using Coq and the Mathematical
Components library, of algorithms originally due to Kosaraju and Tarjan for finding strongly
connected components in finite graphs. It also contains a verified implementation of topological
sorting with extended guarantees for acyclic graphs.

## Meta

- Author(s):
  - Cyril Cohen (initial)
  - Jean-Jacques Lévy (initial)
  - Karl Palmskog
  - Laurent Théry (initial)
- Coq-community maintainer(s):
  - Cyril Cohen ([**@CohenCyril**](https://github.com/CohenCyril))
  - Karl Palmskog ([**@palmskog**](https://github.com/palmskog))
- License: [CeCILL-B](CeCILL-B)
- Compatible Coq versions: 8.16 or later
- Additional dependencies:
  - [MathComp ssreflect 2.0 or later](https://math-comp.github.io)
  - [MathComp fingroup](https://math-comp.github.io)
- Coq namespace: `mathcomp.tarjan`
- Related publication(s):
  - [Formal Proofs of Tarjan's Strongly Connected Components Algorithm in Why3, Coq and Isabelle](https://hal.inria.fr/hal-01906155) doi:[10.4230/LIPIcs.ITP.2019.13](https://doi.org/10.4230/LIPIcs.ITP.2019.13)
  - [Formally-Proven Kosaraju's algorithm](https://hal.inria.fr/hal-01095533) 

## Building and installation instructions

The easiest way to install the latest released version of Tarjan and Kosaraju
is via [OPAM](https://opam.ocaml.org/doc/Install.html):

```shell
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq-mathcomp-tarjan
```

To instead build and install manually, do:

``` shell
git clone https://github.com/math-comp/tarjan.git
cd tarjan
make   # or make -j <number-of-cores-on-your-machine> 
make install
```


## Main files

### Extra library files
* `bigmin.v`: extra library to deal with `\min(i in A) F i`
* `extra.v`: naive definitions of strongly connected components and various basic extentions of mathcomp libraries on paths and fintypes
* `acyclic.v`: definition of acyclic graphs and proof that acyclicity can be determined by knowing strongly connected components

### Proof of Kosaraju strongly connected component algorithm
* `kosaraju.v`: proof of topological sorting and Kosaraju connected component algorithm
* `acyclic_tsorted.v`: properties of topological sorting in acyclic graphs

### Proofs of Tarjan strongly connected component algorithm (independent from each other)
* `tarjan_rank.v`: proof with rank
* `tarjan_rank_bigmin.v`: same proof but with a `\min_` instead of multiple inequalities on the output rank
* `tarjan_num.v`: same proof as `tarjan_rank_bigmin.v` but with serial numbers instead of ranks
* `tarjan_nocolor.v`: new proof, with ranks and without colors, less fields in environement and less invariants, preconditions and postconditions.
* `tarjan_nocolor_optim.v`: same proof as `tarjan_nocolor.v`, but with the serial number field of the environement restored, and passing around stack extensions as sets
