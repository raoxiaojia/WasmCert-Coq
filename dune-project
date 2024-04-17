(lang dune 3.12)
(using coq 0.8)
(using mdx 0.2)
(name coq-wasm)
(version 2.0.1)

(generate_opam_files true)
(license MIT)
(source (github WasmCert/WasmCert-Coq))

(package
  (name coq-wasm)
  (synopsis "Wasm formalisation in Coq")
  (description "Wasm formalisation in Coq, following the AFP formalisation of Conrad Watt")
  (depends
    (coq (and (>= 8.16) (< 8.19~)))
    (coq-compcert (>= 3.11))
    (coq-mathcomp-ssreflect (and (>= 1.16.0) (<= 1.18.0)))
    (coq-itree (>= 3.1.0))
    (coq-parseque (>= 0.2.0))
    (coq-ext-lib (>= 0.12.0))
    (coq-flocq (>= 4.1.3))
    (cmdliner (>= 1.1.0))
    (linenoise (>= 1.4.0))
    (mdx (>= 1.9.0))
  )
  (maintainers
    "Xiaojia Rao"
    "Martin Bodin"
  )
  (authors
    "Martin Bodin"
    "Philippa Gardner"
    "Jean Pichon"
    "Xiaojia Rao"
    "Conrad Watt"
  )
)

