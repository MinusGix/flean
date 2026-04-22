import Lean.Elab.Tactic

/-!
# Forward-Compatible Tag Framework Attributes

Three label attributes for the tag framework:

* `@[tag_generator]` — marks a `IsStrong.toWeak` lemma.
* `@[tag_propagate]` — marks a propagation through FP ops.
* `@[tag_bridge]`   — marks a bridge to a pre-existing hypothesis.

Inert today (no tactic consumes them); zero-cost to add, and populate
the registry for when a tag-inference engine is built (post-~15-tag
threshold per the backlog's design note).

Declared here so both attribute registration and downstream usage can
happen in separate files — Lean processes `initialize` in the order
imports are processed, and attribute application needs the
registration to have already happened.
-/

open Lean

/-- A registered lemma name (wrapper for the env extension). -/
structure TagFrameworkLemma where
  declName : Name
  deriving Inhabited

/-- Environment extension storing `@[tag_generator]` lemmas. -/
initialize tagGeneratorExt :
    SimpleScopedEnvExtension TagFrameworkLemma (Array TagFrameworkLemma) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun lemmas entry => lemmas.push entry
    initial := #[]
  }

/-- Environment extension storing `@[tag_propagate]` lemmas. -/
initialize tagPropagateExt :
    SimpleScopedEnvExtension TagFrameworkLemma (Array TagFrameworkLemma) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun lemmas entry => lemmas.push entry
    initial := #[]
  }

/-- Environment extension storing `@[tag_bridge]` lemmas. -/
initialize tagBridgeExt :
    SimpleScopedEnvExtension TagFrameworkLemma (Array TagFrameworkLemma) ←
  registerSimpleScopedEnvExtension {
    addEntry := fun lemmas entry => lemmas.push entry
    initial := #[]
  }

initialize registerBuiltinAttribute {
  name := `tag_generator
  descr := "mark a tag generator lemma (strong tag → weaker tag)"
  applicationTime := .afterCompilation
  add := fun declName _stx _kind => do
    tagGeneratorExt.add { declName }
}

initialize registerBuiltinAttribute {
  name := `tag_propagate
  descr := "mark a tag propagation lemma (tag through FP op)"
  applicationTime := .afterCompilation
  add := fun declName _stx _kind => do
    tagPropagateExt.add { declName }
}

initialize registerBuiltinAttribute {
  name := `tag_bridge
  descr := "mark a tag bridge lemma (tag → pre-existing hypothesis)"
  applicationTime := .afterCompilation
  add := fun declName _stx _kind => do
    tagBridgeExt.add { declName }
}
