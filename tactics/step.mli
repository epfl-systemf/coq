type ('a, 'b, 'c) reduction =
(*| SRRule (* Rewrite rules *)*)
| Cast of 'c Locus.occurrences_gen (* Cast removal *)
| Beta of Names.Id.t option * 'c Locus.occurrences_gen
(* Beta: applied lambda to substitution *)
| Zeta of Names.Id.t option * 'c Locus.occurrences_gen (* Zeta: letin to substitution *)
| ZetaMatch of 'a * 'c Locus.occurrences_gen
(* Zeta-match: match-letin to substitution *)
| Delta of 'b option * 'c Locus.occurrences_gen
(* Delta: name resolution (including application of primitives) *)
| Eta of 'c Locus.occurrences_gen
(* Eta:
    - lambda over application on the only occurence of the variable
    - constructor on respective primitive projections
*)
| Evar of 'c Locus.occurrences_gen
(* Evar: evar resolution + context substitution, not sure about this one *)
| IotaFix of Names.Id.t option * 'c Locus.occurrences_gen
(* Iota-fix: push fixpoint inward when allowed to *)
| IotaFixPrime of Names.Id.t option * 'c Locus.occurrences_gen
(* Iota-fix-prime: push fixpoint inward, maybe unfold and refold too? *)
| IotaCofix of Names.Id.t option * 'c Locus.occurrences_gen (* Iota-cofix: match or project a cofix *)
| IotaCofixPrime of Names.Id.t option * 'c Locus.occurrences_gen
(* Iota-cofix-prime: push cofix inward, maybe unfold and refold too? *)
| IotaMatch of 'c Locus.occurrences_gen
(* Iota-match: match or project on a constructor + inversion in SProp *)
| Root (* Any reduction applicable at the root of the whole term *)
| Head (* Any reduction at head *)
| Cbv (* Next reduction step of a call-by-value strategy *)
| Cbn (* Next reduction step of a call-by-name strategy *)
| Lazy (* Next reduction step of a call-by-need / lazy strategy *)

val map_reduction : ('a -> 'd) -> ('b -> 'e) -> ('c Locus.occurrences_gen -> 'f Locus.occurrences_gen) -> ('a, 'b, 'c) reduction -> ('d, 'e, 'f) reduction
val step : (Names.inductive * int * int, Evaluable.t, int) reduction -> Reductionops.e_reduction_function
