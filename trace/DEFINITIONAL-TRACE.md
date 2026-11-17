# Definitional trace of the formal statements of Erdős Problem #671

**For:** a mathematician willing to spend thirty to forty-five minutes, not a day, deciding whether the Lean statement
`erdos_671` in the two claimants' files says what Erdős asked in Problem #671. There is no third-party formal statement
of this problem (the problem page lists "Formalised statement? No"), so the claimants' own statement is compared directly
with the problem as posed. That comparison is the one question no machine settles. Nothing else in this record has
been checked yet either: neither Lean file has been built by anyone independent (gap EG1).

**What this is.** The problem as posed, the formal statement verbatim, every definition it depends on down to Mathlib
with file and line, a plain-language rendering of each piece, worked examples written for Lean, the places where the
formal statement differs from the blackboard, and a sign-off checklist. The renderings are the reading of the operating
agent (Claude Code, for Nervous Machine) on 17 November 2026. They are an aid, not a check.

**What this is not.** Not an independent human semantic review, and it changes no standing. Gap EG2 stays open until a
person who is not an author signs the checklist at the end. It is not a build: nothing here says either file compiles
(EG1). It says nothing about either written argument (EG3).

**Sources, pinned.**

- Problem page: https://www.erdosproblems.com/671 as read on 2026-11-17 (page last edited 23 January 2026).
- QuietMethod's Lean file: `Erdos671_square_samples.lean` at the URL in `claim.yaml`, re-fetched 2026-11-17; sha256
  `98375fe58e68a2392bfc6d24e4177e70634f9cd449d7d8bf633fd6fe313c8a00`, 125059 bytes, matching `claim.yaml`.
- Price's Lean text. The "External link to formalisation" on the proof-claims thread is a live.lean-lang.org `#codez=`
  link cut at exactly 2048 characters (sha256 of the link `b5f4d060…ad4798`); it decodes to the module docstring only,
  with no end-of-stream marker. A comment on the claim (Boris Alexeev, 16 July 2026) says the site truncates at 2048
  characters and the full link is over 60000. The full link is in Price's own comment of 15 July 2026 on the claim
  (`/forum/proof-claims/61/comments`, post 7705) and in his 22 June 2026 post in the problem's discussion thread
  (post 7142); the two are identical: 60947 characters, sha256 of the link
  `548e62861f2edfca7ac1f52fd44144a4bf2d22d4ce628e58ee00340be16383b2`. The fragment is lz-string `compressToBase64`
  output, percent-encoded. It was decoded offline with `cycles/trace-1/lzdecode.py` (a re-implementation of lz-string's
  decompressor; no claimant code was run) to a 125059-byte Lean file that ends with the end-of-stream marker; sha256 of
  the decoded text `3854ae85aca322b5ad2c65fb9c7bae5ca19ed939ceca99521365d8690b8d8923`. The decoded text is not
  republished here; anyone can reproduce it from the link and the hash.
- Mathlib: tag `v4.33.0-rc1`, commit `79d0395a1825a6264ad5d269e35e60537518955e` (2026-07-16). Neither file names a
  Mathlib revision. QuietMethod reports checking with Lean 4.33.0-rc1 and Mathlib, and this tag is Mathlib's release
  for that toolchain. Price's file was posted on 22 June 2026 to the live editor, whose Mathlib at that date is not
  recorded; `Mathlib/LinearAlgebra/Lagrange.lean`, the one non-foundational file the definitions rest on, is
  byte-identical at `914b89d9` (the last Mathlib commit before 2026-06-22) and at the tag.
- Worked examples: `cycles/trace-1/Trace.lean`, **written but not run**. No Lean, lake or claimant code was executed in
  this cycle; Part D states what each example would show and claims no result.
- Pre-registration for this trace: `prereg_trace.yaml`.

---

## 0. Conventions a reviewer has to know

| convention | where | what it means here |
|---|---|---|
| `Interval` is the claimants' own abbreviation | claimant file l.64: `abbrev Interval := Set.Icc (-1 : ℝ) 1` | the closed interval $[-1,1]$ as a subtype of ℝ. Not Mathlib's root-level `Interval α` type; inside `namespace Erdos671` the local name is the one used. |
| `Set.Icc a b = {x | a ≤ x ∧ x ≤ b}` | `Mathlib/Order/Interval/Set/Defs.lean` l.76 | closed interval |
| `C(X, Y)` is `ContinuousMap X Y` | `Mathlib/Topology/ContinuousMap/Defs.lean` l.33, notation l.40 | a function with a proof that it is continuous; on `Interval` the topology is the subspace topology from ℝ |
| `ι ↪ β` is `Function.Embedding` | `Mathlib/Logic/Embedding/Basic.lean` l.25: `toFun` with `inj' : Injective toFun` | an injective map; this is where distinctness of the nodes comes from |
| `Fintype.card α = univ.card` | `Mathlib/Data/Fintype/Card.lean` l.40 | the number of elements of a finite type |
| `Finset.map f s` | `Mathlib/Data/Finset/Image.lean` l.55 | the image of a finite set under an embedding (no collapsing) |
| `|a| = a ⊔ -a` | `Mathlib/Algebra/Order/Group/Unbundled/Abs.lean` l.38–39 (additive form of `mabs`) | the usual absolute value on ℝ |
| `Tendsto u l₁ l₂ := l₁.map u ≤ l₂` | `Mathlib/Order/Filter/Defs.lean` l.321 | with `l₁ = atTop` on ℕ and `l₂ = 𝓝 y`: the ordinary limit $u_n \to y$ |
| `atTop := ⨅ a, 𝓟 (Ici a)` | `Mathlib/Order/Filter/AtTopBot/Defs.lean` l.39 | "for all large n" |
| `𝓝 y` | `Mathlib/Topology/Defs/Filter.lean` l.130 | neighbourhood filter of y in ℝ |
| `Lagrange.basisDivisor x y = C (x - y)⁻¹ * (X - C y)` | `Mathlib/LinearAlgebra/Lagrange.lean` l.147 | the linear polynomial $(t - y)/(x - y)$; Lean's `(0)⁻¹ = 0`, which never arises for distinct nodes |
| `Lagrange.basis s v i = ∏ j ∈ s.erase i, basisDivisor (v i) (v j)` | same file l.199 | the Lagrange basis polynomial $\prod_{j \ne i} (t - v_j)/(v_i - v_j)$; equals 1 at $v_i$ (l.227) and 0 at $v_j$, $j \ne i$ (l.236), of degree $\#s - 1$ when $v$ is injective (l.241) |
| Row sizes are shifted by one | claimant file l.2813: `X : ∀ n : ℕ, Row (n + 1)` | Lean's `X n` is the page's row with $n+1$ nodes; `X 0` is the one-node row |

---

## Part A. The problem as posed

**A1. The problem page**, verbatim (erdosproblems.com/671, citing [Er82e], [Er97f], [Va99, 2.40]; a $250 problem):

> Given $a_{i}^n\in [-1,1]$ for all $1\leq i\leq n<\infty$ we define $p_{i}^n$ as the unique polynomial of degree $n-1$
> such that $p_{i}^n(a_{i}^n)=1$ and $p_{i}^n(a_{i'}^n)=0$ if $1\leq i'\leq n$ with $i\neq i'$. We similarly define
> $\mathcal{L}^nf(x) = \sum_{1\leq i\leq n}f(a_i^n)p_i^n(x)$, the unique polynomial of degree $n-1$ which agrees with $f$
> on $a_i^n$ for $1\leq i\leq n$ (that is, the sequence of Lagrange interpolation polynomials).
>
> Is there such a sequence of $a_i^n$ such that for every continuous $f:[-1,1]\to \mathbb{R}$ there exists some
> $x\in [-1,1]$ where $\limsup_{n\to \infty} \sum_{1\leq i\leq n}\lvert p_{i}^n(x)\rvert=\infty$ and yet
> $\mathcal{L}^nf(x) \to f(x)$? Is there such a sequence such that
> $\limsup_{n\to \infty} \sum_{1\leq i\leq n}\lvert p_{i}^n(x)\rvert=\infty$ for every $x\in [-1,1]$ and yet for every
> continuous $f:[-1,1]\to \mathbb{R}$ there exists $x\in [-1,1]$ with $\mathcal{L}^nf(x) \to f(x)$?

Call these Q1 and Q2. The page adds Bernstein's theorem (for every array the Lebesgue function is unbounded at some
point) and Erdős–Vértesi (for every array some continuous f has $\limsup |\mathcal{L}^n f(x)| = \infty$ for almost
all x).

**A reading point, not a discrepancy.** In both questions the point x is chosen after f. If x had to be one point for
all f, the answer would be no: by the uniform boundedness principle, $\mathcal{L}^n f(x) \to f(x)$ for every continuous
f at a fixed x forces $\sup_n \sum_i |p_i^n(x)| < \infty$ (this is the agent's reading of a standard fact). So the page's
order is the only one under which the questions are open, and it is the order the formal statement uses.

**What the trace does not check.** Whether the page's sentences are faithful to Erdős's 1982 and 1997 papers or to
Vértesi's 1999 survey. The operating agent did not consult them. A reviewer with the sources can sign or refuse
checklist item A0; the rest takes the page as the problem.

---

## Part B. The formal statements, verbatim

**B1. QuietMethod** (`Erdos671_square_samples.lean`, l.2813–2820, inside `namespace Erdos671`, with
`open ContinuousMap Filter Polynomial Set` and `open scoped BigOperators Topology`):

```lean
theorem erdos_671 :
    ∃ X : ∀ n : ℕ, Row (n + 1),
      (∀ n, (nodeSet (X n)).card = n + 1) ∧
      (∀ x : Interval, ∀ A : ℝ, ∀ N : ℕ,
        ∃ n ≥ N, A ≤ lebesgue (X n) x) ∧
      ∀ f : C(Interval, ℝ), ∃ x : Interval,
        Tendsto (fun n ↦ interpolant (X n) f x) atTop (𝓝 (f x)) ∧
        ∀ A : ℝ, ∀ N : ℕ, ∃ n ≥ N, A ≤ lebesgue (X n) x
```

**B2. Price** (decoded text, same name, same lines 2813–2820): character for character the same as B1, and so are the
module header (l.1–43), `Interval`, `Row`, `fundamental`, `interpolant`, `lebesgue` and `nodeSet`. A line diff of the
two files (same length, 125059 bytes, same line count) shows 27 changed hunks, all inside proofs: the pigeonhole lemma
and the stage sample count change from $k^3 + 1$ to $k^2 + 1$, the matching error bounds change, and two proof lines
change from `norm_num [...]` to `change ...`. QuietMethod's project page says the submission is a refinement of Price's
claim, does not claim priority, and links a "transformation script" that reproduces the $k^2$ adaptation (not fetched
or run here). So one reading of B1 covers both claims, and any defect in the statement would be shared by both.

**B3. Definitions the statement uses** (claimant file; identical in both):

```lean
abbrev Interval := Set.Icc (-1 : ℝ) 1                                          -- l.64

structure Row (n : ℕ) where                                                    -- l.371–378
  ι : Type
  fintypeι : Fintype ι
  decidableEqι : DecidableEq ι
  card_ι : Fintype.card ι = n
  node : ι ↪ Interval

private def lagrangeValue {ι : Type*} [Fintype ι] [DecidableEq ι]              -- l.435–437
    (node : ι → ℝ) (i : ι) (x : ℝ) : ℝ :=
  (Lagrange.basis Finset.univ node i).eval x

def fundamental {n : ℕ} (X : Row n) (i : X.ι) (x : ℝ) : ℝ :=                   -- l.446–447
  lagrangeValue (fun j ↦ (X.node j : ℝ)) i x

def interpolant {n : ℕ} (X : Row n) (f : C(Interval, ℝ)) (x : ℝ) : ℝ :=        -- l.450–451
  ∑ i, f (X.node i) * fundamental X i x

def lebesgue {n : ℕ} (X : Row n) (x : ℝ) : ℝ :=                                 -- l.454–455
  ∑ i, |fundamental X i x|

def nodeSet {n : ℕ} (X : Row n) : Finset Interval := Finset.univ.map X.node     -- l.458
```

The file also states, with proofs (not checked here), that `fundamental X i (node j)` is 1 if `i = j` and 0 otherwise
(l.474), that the interpolant equals the evaluation of Mathlib's `Lagrange.interpolate` (l.637) and reproduces every
polynomial of degree below n (l.644), and that `lebesgue X (node i) = 1` (l.489). A text scan of both files finds no
`sorry`, `admit`, `axiom`, `native_decide`, custom notation, macro or `set_option`; the only `attribute` line makes the
two `Row` instance fields instances (l.380). A text scan is not a build.

---

## Part C. Every piece of B1, traced

| piece | Lean meaning, with source | agent's reading |
|---|---|---|
| `∃ X : ∀ n : ℕ, Row (n + 1)` | for each n a `Row (n+1)`: a finite index type of size n+1 and an injective map into `Interval` (B3, §0) | "there is a triangular array: for each m ≥ 1, m distinct nodes $a_1^m, \dots, a_m^m$ in $[-1,1]$" (with m = n + 1) |
| `(∀ n, (nodeSet (X n)).card = n + 1)` | the image of the nodes has n + 1 elements | "row m has exactly m distinct nodes". Already forced by `Row`'s `card_ι` and the embedding (the file proves `card_nodeSet`, l.461); redundant, stated for the reader. |
| `fundamental (X n) i x` | `(Lagrange.basis univ node i).eval x` (§0) | "$p_i^m(x) = \prod_{j \ne i} (x - a_j^m)/(a_i^m - a_j^m)$", the unique polynomial of degree m − 1 that is 1 at $a_i^m$ and 0 at the other nodes, evaluated at x |
| `interpolant (X n) f x` | `∑ i, f (node i) * fundamental (X n) i x` | "$\mathcal{L}^m f(x) = \sum_i f(a_i^m) p_i^m(x)$" |
| `lebesgue (X n) x` | `∑ i, |fundamental (X n) i x|` | "$\lambda_m(x) = \sum_i \lvert p_i^m(x) \rvert$", the Lebesgue function |
| `∀ x : Interval, ∀ A : ℝ, ∀ N : ℕ, ∃ n ≥ N, A ≤ lebesgue (X n) x` | for every bound A and every N some later row exceeds A at x | "$\limsup_m \lambda_m(x) = \infty$ for every $x \in [-1,1]$" (the Q2 hypothesis). For real sequences, "for all A and N there is n ≥ N with $u_n \ge A$" is exactly $\limsup u_n = +\infty$. |
| `∀ f : C(Interval, ℝ), ∃ x : Interval, …` | for every continuous real function on $[-1,1]$ there is a point x, chosen after f | "for every continuous $f : [-1,1] \to \mathbb{R}$ there is $x \in [-1,1]$" |
| `Tendsto (fun n ↦ interpolant (X n) f x) atTop (𝓝 (f x))` | the whole sequence n = 0, 1, 2, … (rows of size 1, 2, 3, …) converges to f(x) | "$\mathcal{L}^m f(x) \to f(x)$ as $m \to \infty$", the full sequence, not a subsequence |
| `∧ ∀ A : ℝ, ∀ N : ℕ, ∃ n ≥ N, A ≤ lebesgue (X n) x` | the same unboundedness at the chosen x | "and $\limsup_m \lambda_m(x) = \infty$ at that x", which is Q1's condition. It also follows from the second conjunct; it is repeated so that Q1 can be read off directly. |

Read together: one array answers both questions. The second and third conjuncts are Q2; the third conjunct alone is Q1.
Both questions ask only for the existence of some array, so a particular construction is what an answer of "yes" has to
supply. The words "square samples" in QuietMethod's file name refer to a proof parameter ($k^2 + 1$ samples per stage),
not to a restriction in the statement.

---

## Part D. Worked examples (written, not run)

The commands are in `cycles/trace-1/Trace.lean`. **They have not been run by Lean.** Each line below says what the
example would show if it checks; until a later cycle runs the file and pins the transcript, none of it is a result.

1. `Erdos671.Interval = Set.Icc (-1 : ℝ) 1` by `rfl`: the statement's `Interval` is $[-1,1]$.
2. A two-node row with nodes −1 and 1: `fundamental` at 0 is 1/2 for the first node, and `lebesgue` at 0 is 1, the
   classical values ($p_1(x) = (1 - x)/2$, $p_2(x) = (1 + x)/2$).
3. A three-node row with nodes −1, 0, 1: `lebesgue` at 1/2 is $1/8 + 3/4 + 3/8 = 5/4$, the classical value.
4. `#check` of the claimants' own sanity lemmas (`fundamental_at_node`, `interpolant_at_node`, `lebesgue_at_node`,
   `interpolant_eq_eval_interpolate`, `interpolant_polynomial`) and Mathlib's `Lagrange.natDegree_basis`.
5. `(∀ A N, ∃ n ≥ N, A ≤ u n) ↔ ∀ A, ∃ᶠ n in atTop, A ≤ u n` for any real sequence u, by `Filter.frequently_atTop`.
6. For `X : ∀ n, Row (n + 1)`, `(nodeSet (X n)).card = n + 1` by `card_nodeSet`: the row sizes are 1, 2, 3, ….
7. `#check @erdos_671`, `#print` of `Row`, `fundamental`, `interpolant`, `lebesgue`, `nodeSet`, `Lagrange.basis`,
   `Lagrange.basisDivisor`, and `#print axioms erdos_671`.

---

## Part E. Discrepancies and observations

| id | observation | kind | effect, in the agent's reading |
|---|---|---|---|
| D1 | Rows are indexed from 0 with `X n : Row (n + 1)`; the page indexes rows by their size n ≥ 1. | indexing | none: `X n` is the page's row of size n + 1, and every size 1, 2, 3, … occurs once. Limits and limsups are unchanged by a shift of one. |
| D2 | Nodes are indexed by an abstract finite type `ι` of size n, not by $1, \dots, n$. | encoding | none: every quantity used is a sum over all nodes, which does not depend on how they are numbered. |
| D3 | `fundamental` is a real function (Mathlib's `Lagrange.basis` evaluated at x), not a polynomial object, and "degree n − 1" is not part of the definition. | encoding | none: with distinct nodes Mathlib's basis polynomial has degree n − 1 (`natDegree_basis`, l.241) and the right values at the nodes (l.227, l.236), so it is the page's unique $p_i^n$. A reviewer should confirm the product formula in §0 is the one they know. |
| D4 | `interpolant` and `lebesgue` take x : ℝ; the statement only evaluates them at x in `Interval`. f is evaluated only at nodes. | domain | none: matches the page, where x ranges over $[-1,1]$. |
| D5 | "$\limsup = \infty$" is written as "for all A and N there is n ≥ N with A ≤ λ". | encoding | none: equivalent for real sequences (example 5 gives the `frequently` form). |
| D6 | One array is asserted to answer both questions, and the Q1 conjunct repeats the unboundedness at the chosen x. | strength | none: stronger than asking for two separate arrays; Q1 and Q2 each follow by dropping conjuncts. |
| D7 | The cardinality conjunct `(nodeSet (X n)).card = n + 1` repeats what `Row` already forces. | redundancy | none. |
| D8 | QuietMethod's Lean file is Price's decoded file with proof-internal edits ($k^3 \to k^2$ and two proof lines); the statement and all definitions are the same text (B2). QuietMethod's project page discloses this as a refinement and links a transformation script. | provenance | none on meaning. It does bear on the record: the two Lean artifacts are not two independent formalisations of the statement, so a defect in B1 would be shared, and a build of one is close to, but not the same as, a build of the other. |
| D9 | The formalisation link listed on the proof-claims thread for Price's claim is truncated at 2048 characters and decodes to the docstring only; the full link is in the claimant's comments (Sources). | pinning | none on meaning; it is why `claim.yaml` could pin only the link. This cycle pins the full link and the decoded text by hash. The Overleaf write-up is still unpinned (EG4). |
| D10 | Neither file names its Mathlib revision; this trace reads Mathlib at tag `v4.33.0-rc1`. | revision | none seen: the Lagrange file is identical at the June 2026 revision and at the tag, and the other definitions cited are foundational. A reviewer reading a different Mathlib should check `Lagrange.basis` is unchanged. |

No discrepancy that changes the meaning was seen by the agent. No anomaly is opened.

---

## Part F. Sign-off checklist

For a reviewer who is prepared to put their name to a reading. Each line is a yes/no. Send it with the **Semantic read**
issue form on this repository (it becomes a `read` cycle under your name), or anywhere public; the ledger records it by
date. Two independent signatures with no refusal close gap EG2; one refusal reopens it.

- [ ] A0 (optional, needs the sources): the page's two questions, with x chosen after f and convergence of the full sequence, are the questions in [Er82e], [Er97f] or [Va99, 2.40].
- [ ] A1: `X : ∀ n : ℕ, Row (n + 1)` with `Row` as in B3 is "a triangular array with, for each m ≥ 1, m distinct nodes in $[-1,1]$" (D1, D2, D7).
- [ ] A2: `fundamental`, `interpolant` and `lebesgue` (B3, via Mathlib's `Lagrange.basis`) are the page's $p_i^n(x)$, $\mathcal{L}^n f(x)$ and $\sum_i \lvert p_i^n(x) \rvert$ (D3, D4).
- [ ] A3: `∀ A N, ∃ n ≥ N, A ≤ lebesgue (X n) x` is "$\limsup_n \sum_i \lvert p_i^n(x) \rvert = \infty$" (D5).
- [ ] A4: the last two conjuncts of B1, `∀ x, …` and `∀ f : C(Interval, ℝ), ∃ x : Interval, Tendsto … ∧ …`, say yes to Q2 and to Q1, with $\mathcal{L}^n f(x) \to f(x)$ along the full sequence (D6).
- [ ] B (optional): Price's decoded statement and QuietMethod's are the same text (B2, D8); a signature on A1–A4 covers both claims.

A reviewer who signs A1 to A4 has closed the semantic question for both claims on this problem. It would say nothing
about whether either Lean file builds (EG1) or whether either argument is right (EG3).
