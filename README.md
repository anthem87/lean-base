# lean-base

Common Lean 4 / Mathlib definitions and lemmas on the primes, shared by the formalizations of
A. Mennillo's papers (namespace `LeanBase`). Lean v4.36.0-rc2, Mathlib
`3e1821461a4bc54072a3bd970e5a2ea5d9fd9713`.

| Module | Content |
|---|---|
| `LeanBase.PrimeSums` | `p m` (the `(m+1)`-st prime), `S(x) = 1 + Σ_{q ≤ x} q`, Bertrand, the step `log S_{p_{m+1}} − log S_{p_m}`, `PNTcons` |
| `LeanBase.SubsetSum` | `IsSubsetSum`, Brown's gap-filling criterion |
| `LeanBase.Classical.*` | `Li_k(x)`, Landau's theorem for Dirichlet series with non-negative coefficients and its use: one-sided bounds `Σ_{p≤x} p^k − Li_k(x) = O(x^{k+1/2+ε})` imply RH (`prop30_two_imp_RH`, `prop30_three_imp_RH`) |
| `LeanBase.Hypotheses` | published theorems as explicit hypotheses: `RosserSchoenfeld`, `VonKochPi` (RH ⇒ `π(x) − Li(x) = O(√x log x)`, `x ≥ 2`), `VonKochPsi` (RH ⇒ `ψ(x) = x + O(√x log² x)`) |

Published theorems enter as `Prop`-valued definitions, never as axioms. No `sorry`; only the axioms
`propext`, `Classical.choice`, `Quot.sound`. Extracted from
[arcs-algo](https://github.com/anthem87/arcs-algo).

## License

AGPL-3.0-or-later. The file `LICENSE` is the text of the GNU Affero General Public License,
version 3; you may use this work under version 3 or any later version.
