# IMO Shortlist 2024 problems in Lean

This repository has Lean statements for IMO Shortlist 2024 problems,
originally written before that IMO while chairing the Problem
Selection Committee, along with solutions to C1 and N1 and a partial
solution to A2 (not finished at the time when the final problems for
that IMO were selected); the statements and solutions have only been
minimally updated for newer Lean and mathlib versions since then.
Problems without solutions typically include at least the answer
(separated out into a separate definition) for "determine" problems
rather than leaving that as `sorry`.

The problems do not include those actually used on the IMO (see the
mathlib archive), and do not include the geometry problems since too
many relevant definitions were missing from mathlib at the time these
formal statements were written.  The statements here have not been
carefully checked for correctness, and do not generally follow the
conventions I propose in [IMOLean](https://github.com/jsm28/IMOLean);
the experience of writing the formal statements here helped inform
those conventions.  Furthermore, some statements may correspond more
closely to preliminary versions of the English wording of the problem
statements rather than the version used in the final shortlist (this
can be seen in particular for N6, where an earlier version of the
English wording talked about polynomial roots modulo n, so fitting the
given formal statement better than the final English wording does).

I do not expect to maintain these formal statements further or add
more solutions here; other locations such as
[Compfiles](https://dwrensha.github.io/compfiles/) might be more
appropriate for that.
