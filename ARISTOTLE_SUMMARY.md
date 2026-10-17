# Summary of changes for run 31811596-894c-4261-b6d7-641f77a579cb
I rechecked every citation in the project against the five papers in `papers/`, fixed the errors I found, and removed the split into main and other references. Only comments, docstrings and Markdown files changed; no statement or proof did. `lake build RequestProject` still succeeds, with the same two intended `sorry`s as before: `OIFMCVP_mem_LogDCFL` and `BLTLPastPathChecking_mem_NC`, both in `RequestProject/Statements.lean`.

**Errors found and fixed**
- **Wrong theorem number for [KF09].** In the ICALP 2009 paper, LTL path checking in \(AC^1(\mathrm{logDCFL})\) is Theorem 2. Theorem 1 there just restates the Chakraborty–Datta result. Every `[KF09, Theorem 1]` that referred to the LTL result is now `[KF09, Theorem 2]`.
- **Barrington–Lu–Miltersen–Skyum entry.** Its venue was marked as unchecked. It is now confirmed from three of the papers' reference lists: Proc. 14th IEEE Conference on Computational Complexity (COCO 1999), pp. 24–31. The key is now `[BLMS99]`, matching the author-year style of the other keys. I also noted that Kuhtz's thesis restates the result as its Theorem 1.
- **Misattribution for Theorem 1b.** `RequestProject/CTLTree/Main.lean` and `README.md` said the reduction of CTL tree checking to LTL path checking follows Kuhtz's thesis. It doesn't: [Kuh10, Theorem 10] (Section 5.2) contracts the computation tree directly. The text now says this round algorithm is the project's own and cites Kuhtz for the bound. `docs/CTL_TREE_CHECKING.md` now describes Kuhtz's steps accurately, including the reduction to binary trees in [Kuh10, Lemma 12] and [Kuh10, Corollary 1].
- **Outdated status claims.** `docs/CTL_TREE_CHECKING.md` and `docs/CTLSTAR_PHARDNESS.md` still described Theorems 1a and 1b as depending on the unproved Chakraborty–Datta theorem. Both are now correct.

**Bibliography as a flat list**
- `REFERENCES.md` is now one alphabetical list. The topic headings and the separate summary table are gone. Each entry gives the bibliographic data, which theorems or sections are used, a "Cited in" line naming the files that cite it, and a "Checked" line.
- The "Main references" section of `README.md` is gone. It now cites by key in the text, e.g. 1a is [KF09, Theorem 2] and [KF12, Theorem 1], and 1b is [Kuh10, Theorem 10].
- The notes on how the formalization differs from the cited works moved from `REFERENCES.md` to `docs/DESIGN_NOTES.md`.

**Citations added where results are used**
- In the docstrings in `Statements.lean`, the file overviews of `OIF.lean`, `Strat.lean` and `Logics.lean`, and the `docs/` files.
- [Bus87] and [DS02] were listed but never cited. They are now cited in `Logics.lean` for the \(NC^1\) lower bound.

**What was checked**
- Every key used in the project has an entry in `REFERENCES.md`, and every entry is cited somewhere.
- All theorem, section and proposition numbers for [KF09], [KF12], [Kuh10], [CD06] and [BLMS99] were confirmed in the papers themselves.
- All "ref. N" claims match the papers' reference lists.
- Six entries are still marked **not checked** because none of the provided papers lists them: [EH86], [Jon75], [Sud78], [Ruz81], [Coo85], [AB09]. Their page numbers are from memory and should be verified.

The notes in the Properties table were updated to use the same keys, with statuses unchanged. All changed files are committed, pushed and published.