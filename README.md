# DEBRIEF-math-erdos671

A DEBRIEF mission record (protocol https://github.com/Nervous-Machine/DEBRIEF) for **The claimed solution of Erdős Problem #671 (Lagrange interpolation and the Lebesgue function)**.

This claim is on the public claims board, https://math-board.nervousmachine.com, which shows its stage, who has contributed, and what it needs next.

**Standing.** Certified 0. Accepted 0. Refuted 0. Open gaps 4. The claim and its public artifacts are pinned and the checks still owed are listed. Cycle 1 (2026-11-17) wrote the reading guide for the semantic question and pinned the first claim's full Lean text by hash; the two claims state the same Lean theorem. Nothing has been built or run, and no mathematician has signed anything yet.

## The problem

For each n take n nodes in [-1,1] and interpolate a continuous function f by the polynomial of degree n-1 that agrees with f at those nodes. The Lebesgue function at a point x is the sum of the absolute values of the fundamental polynomials at x; Bernstein showed it is unbounded at some point for every choice of nodes. Erdős asked two things. First: can the nodes be chosen so that for every continuous f there is a point where the Lebesgue function is unbounded and yet the interpolants converge to f? Second: can the nodes be chosen so that the Lebesgue function is unbounded at every point, and yet for every continuous f the interpolants converge to f somewhere?

Source: https://www.erdosproblems.com/671 (posed: Erdős (1982, 1997); a $250 prize problem on erdosproblems.com).

## The claims

**Liam Price**, using GPT Pro and GPT 5.5 (as listed by the claimant), submitted 2026-07-15 at https://www.erdosproblems.com/forum/thread/671/proof-claims.

The claimant states that GPT Pro answered both questions in the affirmative, and that a Lean formalisation of the argument was produced by GPT-5.5 in Codex. The proof-claims thread links an Overleaf read-only document and a Lean snippet in the live Lean web editor; neither is a fixed, hashable file, so this record pins the links and the date only. Attribution of these two links to this claim is by elimination from the thread's link list.

Artifacts, pinned:

- an Overleaf document (read link): https://www.overleaf.com/read/gqmfrhsprtqm#59ac11
- a web page: https://live.lean-lang.org/ (Lean snippet linked from the proof-claims thread; URL carries the code)

**QuietMethod**, using OpenAI Codex (GPT-5) (as listed by the claimant), submitted 2026-07-24 at https://www.erdosproblems.com/forum/thread/671/proof-claims.

A second claim, described by its author as an independent re-derivation and quantitative refinement of the first, not claiming priority for the construction. It builds nested intervals of nodes so that the Lebesgue function exceeds any bound everywhere, while a pigeonhole choice at each stage keeps the interpolation error small for a given f. The author reports a Lean formalisation checked with Lean 4.33.0-rc1 and Mathlib, with no sorry or admit, and with the axioms reported as propext, Classical.choice and Quot.sound.

Artifacts, pinned:

- a Lean development: https://quietmethod-erdos671.gintsuta-kobo.chatgpt.site/Erdos671_square_samples.lean (sha256 98375fe58e68a2392bfc6d24e4177e70634f9cd449d7d8bf633fd6fe313c8a00, 125059 bytes, fetched 2026-11-14)
- a PDF write-up: https://quietmethod-erdos671.gintsuta-kobo.chatgpt.site/erdos-671-square-samples-proof.pdf (sha256 99d19938ec0a0165bbf7a888ae50ba1c4852c8beff30777c9b85950890401cc6, 209054 bytes, fetched 2026-11-14)

Status on the problem page as of 2026-11-14: listed as two proof claims; neither marked accepted by the site.

## What is owed

Each open gap is in `ASKS.md` with what closes it and who could act. In order:

1. **The Lean development has not been built or kernel-checked by anyone outside the claimant** (EG1): A rerun of the Lean build on an independent machine, written down first.
2. **Do the formal statements say what the problem asks?** (EG2): A mathematician who is not an author reads `trace/DEFINITIONAL-TRACE.md` against the Lean statement and the problem page and signs or refuses its four checklist lines. Two independent signatures close this gap for both claims.
3. **No independent mathematician has reported reading the proof, and there is no referee report** (EG3): Someone in the field reads it and says, under their name, what holds and what does not.
4. **The first claim's artifacts are not fixed files** (EG4): the claimant publishes the Lean development and write-up as fixed files or a repository at a commit. (The Lean text is now pinned by hash from the full live-editor link, cycle 1; the Overleaf write-up is not.)

## Contributing

- **Rerun** (if there is a Lean development): copy `prereg_rerun.yaml`, fill in your predictions, register it with `tools/prereg.py register` from the protocol repository and commit it *before* running anything. Run. Report with the **Rerun report** issue form; it becomes a `rerun` cycle under your name.
- **Read**: the reading guide is `trace/DEFINITIONAL-TRACE.md` (cycle 1). It quotes the problem and the Lean statement (the same text in both claimants' files), traces every symbol to its definition, and ends with a four-line checklist. Its worked examples (`cycles/trace-1/Trace.lean`) are written but not yet run by Lean; running them is a welcome contribution. Sign or refuse the checklist with the **Semantic read** issue form; your answers become a `read` cycle under your name. Two independent signatures close gap EG2.
- **Anything else**: open a plain issue.

Rules and templates: https://github.com/Nervous-Machine/DEBRIEF/blob/main/CONTRIBUTING.md. Every contribution is one dated cycle under your own name and goes into `CITATION.cff` and the next release.

## Layout

```
ledger/erdos671.json   the ledger (protocol 0.1.0)
claim.yaml            the pinned claim this record was opened from
SCORECARD.md / ASKS.md  generated from the ledger
prereg_rerun.yaml     a pre-registration template for the first rerun (unregistered)
prereg_trace.yaml     the pre-registration of cycle 1, the reading guide (hashed)
trace/                the reading guide for the semantic question (cycle 1)
cycles/               contributed cycles, one file each
```

## Words

This record never calls the claim proved, verified or a theorem. It records what was claimed, what was checked by whom under what rule, and what is still open. Nothing here has standing until a cycle gives it one.
