# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## Development Commands

### Building
- `lake build` - Build the entire project
- `lake build Flean` - Build the main library
- `lake update` - Update dependencies (mathlib4, aesop, etc.)
- `lake clean` - Clean build artifacts

### Working with Lean
- To check a specific file: `lake env lean <file.lean>`
- To get diagnostics/errors: Use the `mcp__ide__getDiagnostics` tool
- The project uses Lean 4.21.0-rc3 (specified in lean-toolchain)

### Dependencies
This project depends on:
- mathlib4 - Mathematical library for Lean 4
- aesop - Automated proof search tool

## Architecture Overview

This is a mathematical library focused on floating-point arithmetic formalization. The codebase is organized as follows:

**Core Components:**
- `Flean.lean` - Root module that imports all library components
- `Flean/FloatFormat.lean` - Defines floating-point formats and their properties
- `Flean/Encoding/` - Handles encoding/decoding of floating-point representations
- `Flean/Rounding.lean` - Formalization of rounding operations
- `Flean/RelativeError.lean` - Relative error analysis
- `Flean/Ulp.lean` & `Flean/Ufp.lean` - Unit in last/first place definitions

**Key Design Patterns:**
1. Heavy use of mathlib4 for mathematical foundations
2. Modular structure with clear separation between basic definitions and advanced properties
3. Encoding functionality is split into multiple submodules for better organization

**Important Notes:**
- The project uses `autoImplicit = false` in lakefile.toml, so all implicit arguments must be explicit
- Unicode pretty-printing is enabled
- No separate test files - correctness is verified through Lean's proof checker
- When modifying proofs, consider adding linguistic comments as suggested in idea.md to improve readability
- When using `.toVal`, you need to specify the type. Usually this will be `(f.toVal : R)`
- We use `R` to be generic over the numbers that we are talking about, most usually Reals and Rationals

**Key Mathematical Functions:**
- `Int.log b x`: Returns the greatest power of `b` such that `b^(Int.log b x) ≤ x`. Essential for floating-point exponent calculations without noncomputability issues