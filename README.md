Tarjan and Kosaraju
-------------------

# Main files (independent from each other)

## Proofs of Tarjan strongly connected component algorithm
* tarjan_rank.v (751 sloc): proof with rank
* tarjan_rank_bigmin.v (806 sloc): same proof but with a `\min_` instead of multiple inequalities on the output rank
* tarjan_num.v (1029 sloc): same proof as `tarjan_rank_bigmin.v` but with serial numbers instead of ranks
* tarjan_nocolor.v (548 sloc): new proof, with ranks and without colors, less fields in environement and less invariants, preconditions and postconditions.

## Proof of Kosaraju strongly connected component algorithm
* Kosaraju.v: proof of Kosaraju connected component algorithm

# Authors:

Cyril Cohen, Jean-Jacques Lévy and Laurent Théry
