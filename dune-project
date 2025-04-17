(lang dune 3.8)
(using coq 0.8)
(using directory-targets 0.1)


(package
 (name coq-waterproof)
 (version 2.2.0+dev)
 (synopsis "Coq proofs in a style that resembles non-mechanized mathematical proofs")
 (depends rocq-core rocq-stdlib))
