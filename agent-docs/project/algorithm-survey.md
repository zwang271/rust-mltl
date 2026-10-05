# Algorithm survey: what could be formalized next (2026-10-04)

Three searches on 2026-10-04: the MLTL literature, related logics (STL, MTL,
LTLf, …), and the local repos. Status: **candidates only**. The owner picks;
picked items move to `plan.md`. "No MLTL version found" is a negative search
result, not a proof that none exists. Citations marked (mem) were recalled
from memory, not re-checked.

Already mechanized (excluded): the four AFP entries, the REU MLTL→SAT
translation (Isabelle + Verus), and R2U2 (ours, in progress).

## Class 1: MLTL algorithms that exist but are not mechanized

| # | Algorithm | Source | Proof today | Cost |
|---|---|---|---|---|
| 1 | Satisfiability by translation: MLTL→LTL, →LTLf, →SMV, →SMT | Li, Vardi, Rozier, CAV'19 / I&C'22; C++ `mltlsat` (`REU2026/automata-group/mltlsat`) | paper | med |
| 2 | MaxSAT over requirement sets (the max-satisfiable-subset layer; the translation is done) | Hariharan et al., FORMATS'23 | paper | small-med |
| 3 | Bit-vector encoding for monitoring + SAT, O(n log K) | Johannsen et al., FMCAD'25; SABRe | paper | med (D32 conflict: ask) |
| 4 | Tableau satisfiability for bounded discrete STL, which covers MLTL; with unsat cores | Melani, Bartocci, Chiari, EMSOFT'25; STLSat 2026 fixed a soundness flaw in it | paper, already found buggy | med-large |
| 5 | MLTL→pushdown / timed automata via progression (MARTEE) | REU automata group, `paper/ta_alg_and_proofs.tex` | paper | large |
| 6 | Observer pairs: synchronous 3-valued + asynchronous exact | Reinbacher, Rozier, Schumann, TACAS'14 | paper | med |
| 7 | Past-time MLTL (H, O, S, T) and its operators | Aurandt et al., NFM'25; native in `r2u2_core` | paper + local Verus contracts | med (new semantics) |
| 8 | Model-predictive RV (deadline, minimum predicted horizon); multimodal PMLTL | Zhang et al., FORMATS'23; Aurandt et al., FMICS'24 | paper | med / high |
| 9 | Multi-type MLTL (MLTLM) → MLTL translation, minimal length | Hariharan et al., NSV'22, TECS | paper | med |
| 10 | First-order / set aggregation (foreach, forsome, forexactly(n), …) and its monitor | Johannsen MS thesis 2024; C2PO `unroll_set_aggregation` | paper | med-high |
| 11 | Assume-guarantee contracts → 3 streams (active, valid, verified) | C2PO `resolve_contracts`; CAV'23 | none | small |
| 12 | C2PO passes: syntactic CSE, extended-operator removal, SCQ sizing, binary assembly | CAV'23; `passes.py`, `assemble.py` | none | small (CSE) to large |
| 13a | 15 general rewrite rules + memory-reduction theorem | FMICS'23, hand proofs `temporallogic_site/research/FMICS2023/proofs.pdf` | paper | small-med |
| 13b | 69 equality-saturation rules + local DAG memory cost | Johannsen, Rozier, FMCAD'26 | SMT: 62/69 proved, 7 timed out | small-med |
| 13c | 157 FRET rewrites; "symbolic MLTL" (variable bounds) equivalence theorem | Aurandt et al., NFM'26; `IntegratingFRETAndR2U2Analysis` | SMT 152/157; local Isabelle with 16 sorry; 4 rules needed extra end-of-trace conditions | small-med |
| 14 | FRET fmLTL → MLTL (bound to [0,M]); FRET2WEST | NFM'26; Lai, Monahan, JOT'26 | none | small |
| 15 | Benchmark/oracle generation via progression; FPROGG | Li, Rozier, RV'18 | paper (progression itself in AFP) | small |
| 16 | Distance to the nearest satisfying trace via WEST | `AeRosentrater/MLTLDistanceMetricTool` (no paper) | none | small-med |
| 17 | Three-valued MLTL semantics, early evaluation | `ROOT/isabelle/Three_Valued_Mission_Time_LTL.thy` | 8 sorry | small-med |
| 18 | Formula learning from labeled traces | owner's `zwang271/mltl-inference`; Ahmed, LNNS'26 (evolutionary) | none; certify the output, not the search | small |
| 19 | Metric temporal conjunctive queries (MLTL + description-logic queries), `mltl2ltlf` | Westhofen et al., TACAS'24 | none | med |
| 20 | Low value: NEXPTIME/PSPACE complexity, FO-MLTL undecidability, ILP optimality of extraction | CAV'19; Johannsen'24; FMCAD'26 | paper | — |

Port gaps (already proved in Isabelle, not yet in Verus): AFP
`Regex_Equivalence.thy`; REU fast=slow equivalence and encoding-length
bounds.

## Class 2: related-logic algorithms with no MLTL version

| # | Algorithm (source logic) | Seminal work | Template mechanization | Cost |
|---|---|---|---|---|
| A | Vacuity and redundancy detection (LTL) | Beer et al. CAV'97; Kupferman, Vardi '03 (mem) | none; reduces to MLTL equivalence | small |
| B | Real-time inconsistency ("time bombs") and minimal conflicting requirement subsets (Hanfor) | Post, Hoenicke, Podelski FASE'11 (mem) | LRAT certificates | small-med |
| C | Explanations: proof trees with a verified checker (MTL/MFOTL) | Lima et al. TACAS'23; WhyMon | AFP verified MFOTL proof checker | med |
| D | Trace diagnostics via temporal implicants (STL) | Ferrère, Maler, Ničković ATVA'15 (mem) | WEST rows are implicants | small-med |
| E | MLTL → minimal / symbolic DFA (LTLf) | De Giacomo, Vardi '13; Lisa, Syft (mem) | AFP LTL→Büchi/Rabin, regex derivatives; no verified LTLf→DFA exists | med (hub for F, K, L, M) |
| F | Earliest-verdict (anticipatory) monitoring (LTL3) | Bauer, Leucker, Schallhart TOSEM'11 (mem) | AFP LTL3 definitive-set semantics | med (ties to R2U2 promptness) |
| G | Robustness, space and time (STL), sliding min/max | Fainekos, Pappas '09; Donzé et al. CAV'13 (mem) | Chattopadhyay, Mamouras RV'20 (Coq); Berrah et al. JAR'26 (Rocq) | med |
| H | Lattice/semiring-parametric monitor (one proof covers Boolean, robustness, counting) | Mamouras et al. TACAS'21 (mem) | same Coq work | med |
| I | Parameter synthesis / validity domains for interval bounds (PSTL) | Asarin et al. RV'11; Bakhirkin et al. HSCC'18 (mem) | none; monotonicity lemmas | small-med |
| J | Exact minimal learning by SAT, minimality certified by LRAT (LTLf/MTL) | Neider, Gavran FMCAD'18; Raha et al. TACAS'22 (mem) | none | med |
| K | Model counting, spec strength, similarity between formulas | Finkbeiner, Torfah LATA'14 (mem) | verified #SAT checker CPOG, Lean (mem) | small-med |
| L | Realizability and reactive synthesis; bounded synthesis (LTLf) | De Giacomo, Vardi IJCAI'15; BoSy | none verified | large |
| M | Safety shields / runtime enforcement | Bloem et al. TACAS'15; Falcone et al. (mem) | VeriPhy (mem) | med-large |
| N | Requirements coverage and test generation (UFC, MC/DC) | Whalen et al. ISSTA'06 (mem) | none | small-med |
| O | Monitoring with missing or uncertain data (3-valued, sound for all completions) | Basin et al. '15, '20 (mem) | none | small-med |
| P | Parallel monitoring by trace slicing (locality: overlap = complen) | Basin et al. RV'14 (mem) | Schneider et al. STTT'21 (verify) | small |
| Q | Compile to stream RV languages (Lola, Copilot) with memory bounds | Lola '05; RTLola CAV'19 (mem) | verified Rust Lola monitors RV'20; copilot-verifier ICFP'23 | med (overlaps C2PO) |
| R | Timed pattern matching (all matching segments) | Ulus et al. FORMATS'14 (mem) | AFP VeriMon MFODL, VYDRA | med |
| S | Booleanization and sampling correctness | Fainekos, Pappas FORMATS'07 (mem) | ModelPlex, VeriPhy | med (reals) |
| T | Contract algebra: refinement, composition, quotient | Benveniste et al. '18 (mem) | Coq realizability, Gacek et al. NFM'15 | med |
| U | Expressive completeness and normal forms | Kamp; Sickert, Esparza LICS'20 | AFP LTL normalisation | small-med (theory) |
| V | Memory lower bounds and optimality of SCQ sizing (MTL space-optimal monitoring) | Basin et al. Acta Inf.'18; Aerial | Aerial (Isabelle) | med |
| W | HyperMLTL (bounded hyperproperties) | Clarkson et al. POST'14 (mem) | AFP HyperCTL* | med |
| X | Downstream of G and E: falsification, reward machines, statistical model checking | S-TaLiRo; Icarte et al. ICML'18 (mem) | Hölzl, Nipkow pCTL (Isabelle) | small after G/E |

Low priority: spatial logics (STREL), duration and counting operators,
native bounded model checking (via CAVA), repair of interval bounds.

The 2025 language-partitioning paper says explicitly that synthesis and
coverage "are not yet defined for MLTL" (L, N). The MLTLM paper lists
realizability and vacuity as targets that have not been done (A, L).
