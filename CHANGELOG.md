<!--
SPDX-License-Identifier: MPL-2.0
SPDX-FileCopyrightText: 2026 Jonathan D.A. Jewell (hyperpolymath)
-->

# Changelog

All notable changes to `coq-jr` will be documented in this file.

This file is generated from conventional commits by the
[`changelog-reusable.yml`](https://github.com/hyperpolymath/standards/blob/main/.github/workflows/changelog-reusable.yml)
workflow (`hyperpolymath/standards#206`). Adopt the workflow in this repo's CI to keep this file in sync automatically — see
[`templates/cliff.toml`](https://github.com/hyperpolymath/standards/blob/main/templates/cliff.toml)
for the canonical config.

The format follows [Keep a Changelog](https://keepachangelog.com/en/1.1.0/);
this project aims to follow [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

### Added

- feat(ci): enable Hypatia scanning

### Fixed

- fix(ci): migrate dependency-review from deny-licenses to allow-licenses (#27)
- fix(ci): migrate dependency-review from deny-licenses to allow-licenses (#25)
- fix(ci): sync hypatia-scan.yml to canonical (413: env.HOME+Phase-2+SARIF) (#24)
- fix(ci): adopt canonical hypatia-scan.yml (env.HOME/scanner-layout + Comment-step gate) (#20)
- fix(codeql): switch language matrix to 'actions' (no JS/TS in repo) (#15)
- fix(ci): repair corrupted rsr-antipattern.yml from #17 (#18)
- fix(ci): move secret-scanner Cargo.toml gate from job-level if: to step-level (#19)
- fix(ci): rsr-antipattern.yml duplicate heredoc (#17)
- fix(ci): migrate dependency-review from deny-licenses to allow-licenses (#16)
- fix: remove duplicate SCM files from root

### Changed

- refactor: server.ts → server.mjs (TS types stripped) (#7)

### Documentation

- docs: update SCM files with project information
- docs: add checkpoint files for state tracking
- docs: update license from AGPL to PMPL

### CI

- ci(workflow): adopt hardened hypatia-scan from hyperpolymath/hypatia#237 (#14)
- ci: bump actions/upload-artifact SHA to current v4 (#12)
- ci(secret-scanner): drop duplicate --fail from trufflehog extra_args (#11)
- ci(antipattern): fix top-level dir matching + benchmarks/lsp/bench filename allowlists (#9)
- ci(antipattern): TS check reads .claude/CLAUDE.md exemption table (#8)

## Pre-history

Prior commits to this file's introduction are recorded in git history but not formally classified into Keep-a-Changelog sections. To backfill, run `git cliff -o CHANGELOG.md` locally using the canonical [`cliff.toml`](https://github.com/hyperpolymath/standards/blob/main/templates/cliff.toml) — this is one-shot mechanical work.

---

<!-- This file was seeded by the 2026-05-26 estate tech-debt audit follow-up (Row-2 Phase 3); see [`hyperpolymath/standards/docs/audits/2026-05-26-estate-documentation-debt.md`](https://github.com/hyperpolymath/standards/blob/main/docs/audits/2026-05-26-estate-documentation-debt.md). -->
