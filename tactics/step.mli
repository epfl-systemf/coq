type ('a, 'b, 'c) reduction =
(*| SRRule (* Rewrite rules *)*)
| SRCast of 'c Locus.occurrences_gen (* Cast removal *)
| SRBeta of 'c Locus.occurrences_gen
(* Beta: applied lambda to substitution *)
| SRZeta of 'c Locus.occurrences_gen (* Zeta: letin to substitution *)
| SRZetaMatch of 'a * 'c Locus.occurrences_gen
(* Zetamatch: match-letin to substitution *)
| SRDelta of 'b option * 'c Locus.occurrences_gen
(* Delta: name resolution (including application of primitives) *)
| SREta (* Eta expansion: expand lambda *)
| SREtaPrime of 'c Locus.occurrences_gen
(* Eta reduction:
    - lambda over application on the only occurence of the variable
    - constructor on respective primitive projections
*)
| SREvar of 'c Locus.occurrences_gen
(* Evar: evar resolution + context substitution, not sure about this one *)
| SRFix of 'c Locus.occurrences_gen
(* Fix: push fixpoint inward when allowed to *)
| SRFixPrime of 'c Locus.occurrences_gen
(* Fixprime: push fixpoint inward, maybe unfold and refold too? *)
| SRCofix of 'c Locus.occurrences_gen (* Cofix: match or project a cofix *)
| SRCofixPrime of 'c Locus.occurrences_gen
(* Cofixprime: push cofix inward, maybe unfold and refold too? *)
| SRMatch of 'c Locus.occurrences_gen
(* Match: match or project on a constructor *)
(* TODO: IOTA (match + fix + cofix)? *)
| SRUIP of 'c Locus.occurrences_gen
(* UIP: inversion of a match with a unique constructor in SProp *)
| SRHead (* Any reduction at head *)
| SRCbv (* Next reduction step of a call-by-value strategy *)
| SRCbn (* Next reduction step of a call-by-name strategy *)
| SRLazy (* Next reduction step of a call-by-need / lazy strategy *)

val map_reduction : ('a -> 'd) -> ('b -> 'e) -> ('c Locus.occurrences_gen -> 'f Locus.occurrences_gen) -> ('a, 'b, 'c) reduction -> ('d, 'e, 'f) reduction
val step : (Names.inductive * int * int, Evaluable.t, int) reduction -> Reductionops.e_reduction_function
