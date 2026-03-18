# JIBLM DIY Intro Number Theory (Lean)

This repository is for learning how to write formal proofs in Lean by working through problems from the *Journal of Inquiry-Based Learning in Mathematics* text:

- `V100420S.pdf` (*A Do-It-Yourself Introduction to Number Theory*)

## Goal

Use the textbook as a problem source and formalize solutions in Lean, chapter by chapter, to build theorem-proving fluency.

## Repository Skeleton

- `lean-toolchain` — Lean toolchain version for this project
- `lakefile.lean` — Lake project configuration
- `JIBLM_DIY_INTRO_NUMBER_THEORY.lean` — top-level import file
- `JIBLM_DIY_INTRO_NUMBER_THEORY/Chapters/` — chapter-by-chapter formalizations
- `V100420S.pdf` — source textbook

## Getting Started

1. Install Lean 4 and Lake (recommended via `elan`).
2. From the repository root, build the project:

   ```bash
   lake build
   ```

3. Add new chapter/problem files under `JIBLM_DIY_INTRO_NUMBER_THEORY/Chapters/` and import them from `JIBLM_DIY_INTRO_NUMBER_THEORY.lean`.
