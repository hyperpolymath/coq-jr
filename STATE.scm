;; SPDX-License-Identifier: PMPL-1.0-or-later
;; STATE.scm - Project state for coq-jr

(state
  (metadata
    (version "0.1.0")
    (schema-version "1.0")
    (created "2024-06-01")
    (updated "2025-01-17")
    (project "coq-jr")
    (repo "hyperpolymath/coq-jr"))

  (project-context
    (name "Coq-Jr")
    (tagline "Web-native interactive theorem proving with Coq")
    (tech-stack ("rescript" "deno" "coq")))

  (current-position
    (phase "alpha")
    (overall-completion 25)
    (working-features
      ("Browser-native interface"
       "HTTP/GraphQL API"
       "poly-proof-mcp integration"))))
