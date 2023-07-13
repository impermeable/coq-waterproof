(lang dune 3.9)
(using coq 0.8)

(package
 (name coq-waterproof)
 (synopsis "Coq proofs in a style that resembles non-mechanized mathematical proofs")
 (depends coq-core coq-stdlib coq ltac2))