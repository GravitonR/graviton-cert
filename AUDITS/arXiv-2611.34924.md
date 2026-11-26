# Independent Lean 4 & Epistemic-Boundary Audit of `arXiv:2611.34924`

**Paper audited:** Venkatesa Chandrasekaran, *"An algebraic quantization of gravity from the null cone"*, [arXiv:2611.34924](https://arxiv.org/abs/2611.34924) (submitted 25 Nov 2026; co-developed with ~400M tokens of GPT-6 Astra).
**Auditor:** Graviton Research Foundation (`graviton-cert`, Lean 4.36.0 kernel — zero `sorryAx`, zero custom axioms).
**Source formalization:** [`GravitonCert/Studies/NullConeGravity.lean`](../GravitonCert/Studies/NullConeGravity.lean)

---

## Executive Summary

`arXiv:2611.34924` is a remarkably ambitious attempt at a background-independent, nonperturbative algebraic quantization of 4D Lorentzian vacuum general relativity on intersecting null cones—claiming a Type I factor, finite-dimensional causal-diamond Hilbert spaces, a discrete area spectrum, Bekenstein–Hawking entropy with Sen's 1-loop log correction, an algebraic ER = EPR realization, and 1-loop semiclassical Einstein equations.

Because the paper addresses 50-year-old open problems in quantum gravity and explicitly credits ~400M tokens of AI-assisted reasoning, we ran an independent **Lean 4 kernel & epistemic-boundary audit** separating:
1. **The algebraic and analytic cores that genuinely hold** (5 theorems machine-checked universally in Lean 4: `NC-01`–`NC-05`), from
2. **The four exact structural gates** where the headline physical conclusions still live or die (`NC-GATE-01`–`NC-GATE-04`).

---

## 1. What Passed Lean 4 Kernel Verification (`NC-01`–`NC-05`)

All 5 theorems compile in Lean 4.36.0 with **0 `sorryAx`** and **0 custom axioms**:

| Claim ID | Paper Reference | Machine-Checked Statement |
| :--- | :--- | :--- |
| **`NC-01`** | Eqs. `5.21a–d` | From $\bar{u}_* \ge (1-\epsilon)\mathscr{A}/\mathsf{a}$, Cauchy–Schwarz $\mathsf{a}^2 \le 4\pi \mathscr{A}$, and $\bar{u}_* \le \ell$, the corner area is strictly bounded above: $\mathscr{A} \le 4\pi\ell^2/(1-\epsilon)^2$. |
| **`NC-02`** | Eq. `5.29` | Writing $r = e^\eta > 0$, the boosted freely-falling vacuum correlator ratio obeys $1 - \frac{4r}{(1+r)^2} = \left(\frac{r-1}{r+1}\right)^2 = \tanh^2(\eta/2)$, strictly positive iff $r \ne 1$. |
| **`NC-03`** | Eqs. `5.30c, 5.32, 5.37–5.38` | Chandrasekaran's cycle-grouping trick (Fig. 29) genuinely suppresses normalized area variance by $\Delta^2 + s_*^2 / ((r-1)m_{\min})$ and forces every finite cycle projection to satisfy $Z_P[X] \le 0 < Z[X]$. |
| **`NC-04`** | Eqs. `5.44–5.45` | If thermal weights $\sum w_i$ diverge and $p v_{a_0} > 0$, adding finite subsets $J \times \{a_0\}$ drives Eq. (5.44) arbitrarily negative, ruling out unordered convergence to `0`. |
| **`NC-05`** | Eqs. `4.33–4.34` | Proves simultaneously: (a) uniform 1D radial convergence $\sum_{k=1}^N 1/k^2 < 2$ for all $N$, (b) unbounded perturbative $G_N^3$ harmonic divergence $\sum_{k=1}^{2^m} 1/k \ge 1 + m/2$, and (c) exact 4D angular-harmonic multiplicity $\sum_{\ell=0}^L (2\ell+1) = (L+1)^2$. |

---

## 2. The Four Open Gates Where the Headline Claims Live or Die

The algebraic steps above are valid—**conditional on four major structural assumptions** that are *not* proved by those inequalities alone:

### `NC-GATE-01` — Unconditional Cut-Gluing Convergence (Eqs. `4.29`, `5.38`, `5.44`)
Both the finite-dimensional causal-diamond proof (`Eq. 5.38`, cycle permutation `V`) and the AdS thermal trace proof (`Eq. 5.44`, arbitrary finite subsets `F`) **critically require that infinite intermediate-state sums converge unconditionally (independent of rearrangement or cycle grouping)**. In standard infinite-dimensional Lorentzian QFT/path integrals, trace sums are not rearrangement-invariant unless trace-class convergence or a UV regulator is already built in. Proving Eq. (4.29) without circularity is the single sharpest mathematical fulcrum of Section 5.

### `NC-GATE-02` — Pure Gaussian Extension → Type I Factor by Construction (Sec. `4.2`)
Extending a fixed-area Gaussian Fock state as a **pure state** to the full algebra automatically produces an irreducible GNS representation—and hence a Type I factor (`B(H)`)—by elementary C\*-algebra theory. The real physics question is not whether a Type I representation exists, but whether changing the countable basis `(q_j, p_j)` or Gaussian variances `Δq_k` yields a **unitarily equivalent** representation that preserves full 4D diffeomorphism invariance without hiding a UV cutoff.

### `NC-GATE-03` — 1D Radial Mode Sum vs. Full 4D UV Finiteness & 2-Loop Goroff–Sagnotti (Eqs. `4.33–4.34`, Sec. `6`)
Eqs. (4.32)–(4.34) explicitly fix **one polarization and one real angular harmonic** and sum only over radial mode $k \ge 1$ (giving $\sum 1/k^2 < 2$, analogous to a 1D string worldsheet sum). On a 4D null cone ($S^2 \times \mathbb{R}$), angular harmonics up to $L$ carry quadratic multiplicity $(L+1)^2$ (proved in `NC-05`). Moreover, pure 4D GR is famously 1-loop on-shell finite; the defining test of perturbative nonrenormalizability is the **2-loop Goroff–Sagnotti $R^3$ divergence** at $O(G_N^2)$, which neither Eq. (4.34) nor the 1-loop semiclassical limit in Section 6 yet settles.

### `NC-GATE-04` — Caustic-Free Truncation (`v = ε > 0`) & Unbounded Operator Domains (Secs. `5.1–5.3`)
The clock operator $\widehat{\bar{u}}_*$ is defined by truncating the null cone at $v = \epsilon > 0$ *before* null generators hit caustics. In nonlinear 4D GR, generic gravitational waves focus and generate caustics; removing the $\epsilon$-truncation and proving strong commutativity (commuting spectral projections on a common dense domain) for unbounded $(\widehat{\bar{u}}_*, \widehat{\mathscr{A}})$ remains open.

---

## Reproducing This Audit Locally

```bash
git clone https://github.com/GravitonR/graviton-cert.git
cd graviton-cert
lake build && lake exe graviton-cert
```
