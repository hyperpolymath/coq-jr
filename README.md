<!--
SPDX-License-Identifier: CC-BY-SA-4.0
SPDX-FileCopyrightText: 2025-2026 Jonathan D.A. Jewell <j.d.a.jewell@open.ac.uk>
-->

<div class="lead" wrapper="1">

**Coq-Jr** is a lightweight, browser-native interface for the [Coq proof
assistant](https://coq.inria.fr), built with AffineScript. It provides
HTTP and GraphQL access to interactive theorem proving, serving as both
a standalone proof environment and a satellite component of the
[poly-proof-mcp](https://github.com/hyperpolymath/poly-proof-mcp)
AI-accessible verification network.

</div>

# Status: Alpha (v0.2.0-dev)

![Coq Compatible](https://img.shields.io/badge/coq-compatible-orange)
![ReScript](https://img.shields.io/badge/rescript-v11-red)
![Deno](https://img.shields.io/badge/deno-v2-black)

------------------------------------------------------------------------

<div id="toc">

</div>

# What is Coq-Jr?

Coq-Jr democratizes formal verification by making the Coq proof
assistant accessible through:

- **Web Interface** — An interactive browser-based IDE for writing and
  executing Coq proofs

- **GraphQL API** — Programmatic access for automated verification
  pipelines

- **MCP Integration** — AI-accessible proof assistance via the Model
  Context Protocol

Unlike traditional Coq installations requiring local setup, Coq-Jr runs
entirely in the browser using WebAssembly, with optional server-side
verification for enhanced capabilities.

## Core Capabilities

| Feature | Description |
|----|----|
| **Interactive Proofs** | Step through proofs with real-time goal display, tactic feedback, and error highlighting |
| **MathComp Support** | Built-in Mathematical Components library for advanced mathematical reasoning |
| **Zero Installation** | No local Coq installation required—proofs execute in WebAssembly |
| **Session Persistence** | Save and resume proof sessions (roadmap) |
| **Multi-Backend** | Pluggable architecture supporting jsCoq (browser) and SerAPI (server) backends |

# The Hyperpolymath Ecosystem

Coq-Jr is one component of a larger formal verification ecosystem:

                        ┌──────────────────────────────────────────────┐
                        │           poly-proof-mcp                     │
                        │    (AI-Accessible Proof Orchestration)       │
                        └──────────────┬───────────────────────────────┘
                                       │ MCP Protocol
               ┌───────────────────────┼───────────────────────┐
               │                       │                       │
               ▼                       ▼                       ▼
        ┌─────────────┐        ┌─────────────┐        ┌─────────────┐
        │   Coq-Jr    │        │   ECHIDNA   │        │  Other      │
        │  (Coq/Rocq) │        │ (12 provers)│        │  Provers    │
        └─────────────┘        └─────────────┘        └─────────────┘
               │                       │
               │              ┌────────┴────────┐
               │              │                 │
               ▼              ▼                 ▼
        ┌─────────────┐ ┌───────────┐   ┌─────────────┐
        │ echidnabot  │ │git-eco-bot│   │   ...       │
        │(math verify)│ │(efficiency)│   │             │
        └─────────────┘ └───────────┘   └─────────────┘

**[ECHIDNA](https://github.com/hyperpolymath/echidna)**  
Neurosymbolic theorem proving platform supporting 12 proof assistants
(Agda, Coq, Lean, Isabelle, Z3, etc.) with neural candidate generation

**[echidnabot](https://github.com/hyperpolymath/echidnabot)**  
Mathematical verification bot for git forges—like Dependabot, but for
proof obligations

**[git-eco-bot](https://github.com/hyperpolymath/git-eco-bot)**  
Ecological and thermodynamic efficiency analysis for codebases

# Quick Start

## Prerequisites

- [Deno](https://deno.land) v2.0+

- <a href="https://nodejs.org" class="js">Node</a> v18+ (for
  AffineScript compilation only)

## Installation

```bash
# Clone the repository
git clone https://github.com/hyperpolymath/coq-jr.git
cd coq-jr

# Install ReScript compiler
npm install

# Compile ReScript sources
npm run res:build

# Start the server
deno task dev
```

The proof environment is now available at <http://localhost:8000>

## Docker (Coming Soon)

```bash
docker run -p 8000:8000 ghcr.io/hyperpolymath/coq-jr:latest
```

# Usage

## Web Interface

Navigate to <http://localhost:8000> to access the interactive proof
environment.

| Key | Action |
|----|----|
| <span class="kbd">**Alt**</span>+<span class="kbd">**↓**</span> / <span class="kbd">**Alt**</span>+<span class="kbd">**N**</span> | Execute next proof step |
| <span class="kbd">**Alt**</span>+<span class="kbd">**↑**</span> / <span class="kbd">**Alt**</span>+<span class="kbd">**P**</span> | Undo last proof step |
| <span class="kbd">**Alt**</span>+<span class="kbd">**→**</span> / <span class="kbd">**Alt**</span>+<span class="kbd">**Enter**</span> | Execute to cursor position |
| <span class="kbd">**F8**</span> | Toggle goal panel visibility |

Key Bindings

## GraphQL API (Roadmap)

```graphql
# Start a new proof session
mutation {
  createSession(theorem: "forall n : nat, n + 0 = n") {
    sessionId
    goals
  }
}

# Execute a tactic
mutation {
  executeTactic(sessionId: "abc123", tactic: "intros n.") {
    goals
    proofState
    isComplete
  }
}

# Query available lemmas
query {
  searchLemmas(pattern: "*comm*", library: "mathcomp") {
    name
    statement
    library
  }
}
```

## MCP Integration (Roadmap)

For AI assistants using the Model Context Protocol:

```json
{
  "mcpServers": {
    "coq-jr": {
      "command": "deno",
      "args": ["run", "--allow-net", "mcp-server.mjs"],
      "env": {
        "COQ_JR_URL": "http://localhost:8000"
      }
    }
  }
}
```

# Architecture

## Technology Stack

| Layer | Technology | Purpose |
|----|----|----|
| **Frontend** | ReScript → JavaScript | Type-safe UI generation and DOM manipulation |
| **Server** | Deno | HTTP server, static file serving, API endpoints |
| **Proof Engine** | jsCoq (WebAssembly) | Browser-side Coq execution via WASM |
| **Styles** | CSS | Custom styling with Bootstrap foundation |

## Module Structure

    src/
    ├── Main.res          # Entry point and module exports
    ├── Page.res          # HTML page generation
    ├── Components.res    # Reusable UI components
    ├── JsCoq.res         # jsCoq library bindings
    ├── Dom.res           # Browser DOM API bindings
    ├── Server.res        # HTTP server implementation
    └── Deno.res          # Deno runtime bindings

## Request Flow

    Browser Request
           │
           ▼
    ┌─────────────────┐
    │  Deno Server    │
    │  (Server.res)   │
    └────────┬────────┘
             │
        ┌────┴────┐
        │         │
        ▼         ▼
     /index    /static
        │         │
        ▼         ▼
    Page.res   File I/O
        │         │
        ▼         ▼
    HTML Gen   Asset
        │         │
        └────┬────┘
             │
             ▼
       HTTP Response
             │
             ▼
    ┌─────────────────────┐
    │       Browser       │
    │   jsCoq (WASM)      │
    │   Proof Engine      │
    └─────────────────────┘

# Example: Infinitude of Primes

The default page demonstrates the classic proof that there are
infinitely many primes:

```coq
From Coq Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import eqtype ssrnat div prime.

Lemma prime_above m : {p | m < p & prime p}.
Proof.
  have /pdivP[p pr_p p_dv_m1]: 1 < m`! + 1
    by rewrite addn1 ltnS fact_gt0.
  exists p => //; rewrite ltnNge; apply: contraL p_dv_m1 => p_le_m.
  by rewrite dvdn_addr ?dvdn_fact ?prime_gt0 // gtnNdvd ?prime_gt1.
Qed.
```

This proof uses the Mathematical Components library to show that for any
natural number `m`, there exists a prime `p` greater than `m`.

# Development

## Build Commands

```bash
# Watch mode for ReScript compilation
npm run res:dev

# Production build
npm run res:build

# Start development server
deno task dev

# Type check
deno check server.mjs
```

## Testing (Roadmap)

```bash
# Run unit tests
deno test

# Run integration tests
deno task test:integration

# Run proof verification tests
deno task test:proofs
```

# API Reference

## HTTP Endpoints

| Method | Path                          | Description                           |
|--------|-------------------------------|---------------------------------------|
| GET    | `/`                           | Serve interactive proof environment   |
| GET    | `/index.html`                 | Alias for `/`                         |
| GET    | `/{file}`                     | Serve static assets (CSS, JS, images) |
| POST   | `/api/session` *(roadmap)*    | Create new proof session              |
| POST   | `/api/tactic` *(roadmap)*     | Execute tactic in session             |
| GET    | `/api/state/{id}` *(roadmap)* | Retrieve proof state                  |

## Configuration

| Variable       | Default        | Description               |
|----------------|----------------|---------------------------|
| `PORT`         | `8000`         | HTTP server port          |
| `COQ_PACKAGES` | `coq,mathcomp` | Coq packages to load      |
| `JSCOQ_CDN`    | unpkg          | jsCoq distribution source |

Environment Variables

# Contributing

We welcome contributions! Please see
<a href="CONTRIBUTING.adoc" class="adoc">CONTRIBUTING</a> for
guidelines.

## Development Philosophy

- **Minimal dependencies** — Prefer standard library solutions

- **Type safety** — Leverage ReScript’s type system

- **Polyglot flexibility** — Support multiple compilation targets (Deno,
  Node, browser)

- **Accessibility** — Theorem proving should be approachable

# License

Dual-licensed under your choice of:

- Palimpsest-MPL License v1.0 (PMPL-1.0)

- Palimpsest-MPL License v3.0 or later (MPL-2.0)

See <a href="LICENSE-PMPL-1.0" class="0">LICENSE-PMPL-1</a> and
[LICENSE-AGPL](LICENSE-AGPL) for details.

# Acknowledgements

- [jsCoq](https://github.com/jscoq/jscoq) — The Coq proof assistant in
  the browser

- [Coq](https://coq.inria.fr) — The formal proof management system

- [Mathematical Components](https://math-comp.github.io) — A library for
  formalized mathematics

- The Hyperpolymath community for the broader verification ecosystem

------------------------------------------------------------------------

<div class="text-center" wrapper="1">

*Part of the [Hyperpolymath](https://github.com/hyperpolymath) formal
verification ecosystem*

</div>
