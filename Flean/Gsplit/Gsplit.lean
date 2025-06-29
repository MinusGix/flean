import Lean
import Lean.Elab.Tactic.Basic
import Lean.Elab.Tactic.Location
import Lean.Elab.Term
import Batteries.Lean.Expr

namespace Flean.Gsplit

open Lean Elab Meta Tactic

initialize registerTraceClass `gsplit

/-- Find the first application of a function in an expression -/
partial def findFirstApp (e : Expr) (p : Name → Bool) : MetaM (Option (Expr × Array Expr)) := do
  trace[gsplit] "Visiting Expr: {e} (kind: {e.ctorName})"

  if e.isApp then
    let fn := e.getAppFn
    let args := e.getAppArgs
    trace[gsplit] "  Is App. Fn: {fn} (kind: {fn.ctorName}), Args: {args.map (fun x => x.ctorName)}"
    if fn.isConst then
      trace[gsplit] "  Fn is constant: {fn.constName!}"
      if p fn.constName! then
        trace[gsplit] "  Found target function: {fn.constName!}"
        return some (fn, args)
    else
      trace[gsplit] "  Fn is not constant: {fn}"
      -- Recurse into the function part of the application
      let res_fn ← findFirstApp fn p
      if res_fn.isSome then
        return res_fn

    -- Recurse into arguments
    for arg in args do
      let res_arg ← findFirstApp arg p
      if res_arg.isSome then
        return res_arg
    return none
  else if e.isLambda then
    trace[gsplit] "  Is Lambda. Body: {e.bindingBody!}"
    findFirstApp e.bindingBody! p
  else if e.isForall then
    trace[gsplit] "  Is Forall. Body: {e.bindingBody!}"
    findFirstApp e.bindingBody! p
  else if e.isLet then
    trace[gsplit] "  Is Let. Value: {e.letValue!}, Body: {e.letBody!}"
    let res_v ← findFirstApp e.letValue! p
    if res_v.isSome then
      return res_v
    findFirstApp e.letBody! p
  else if e.isMData then
    trace[gsplit] "  Is MData. Body: {e.mdataExpr!}"
    findFirstApp e.mdataExpr! p
  else if e.isProj then
    trace[gsplit] "  Is Proj. Body: {e.projExpr!}"
    findFirstApp e.projExpr! p
  else
    trace[gsplit] "  Not an application, lambda, forall, let, mdata, or proj. Returning none."
    return none

/-- The gsplit tactic syntax -/
syntax (name := gsplit) "gsplit " ident (" with " ident)? : tactic

/-- Elaboration rule for gsplit tactic -/
elab_rules : tactic
  | `(tactic| gsplit $fnName:ident $[with $h:ident]?) => do
    let g ← getMainGoal
    g.withContext do
      let goalType ← instantiateMVars (← g.getType) -- Instantiate metavariables
      trace[gsplit] "Goal: {goalType}"
      trace[gsplit] "fnName: {fnName.getId}"
      let some (fn, args) ← findFirstApp goalType (fun n => fnName.getId.isSuffixOf n)
        | throwError "Could not find application of {fnName.getId} in the goal"

      trace[gsplit] "Found function: {fn}"
      trace[gsplit] "Arguments: {args}"

      let constNameStr := fn.constName!.components.getLast!.toString false
      trace[gsplit] "constNameStr: {constNameStr}"
      let casesLemmaName := (constNameStr ++ "_cases").toName
      trace[gsplit] "Using cases lemma: {casesLemmaName}"

      let rcasesPat := h.map (fun id => mkIdentFrom id id.getId)
                      |>.getD (mkIdent `h)
      trace[gsplit] "rcasesPat: {rcasesPat}"

      let lemmaIdent := mkIdent casesLemmaName
      let argTerms : Array (TSyntax `term) ← args.mapM (fun arg => arg.toSyntax)
      let argTerms := argTerms.drop 2 -- Drop type and instance arguments

      let appTerm : TSyntax `term := ⟨lemmaIdent.raw⟩

      trace[gsplit] "appTerm: {appTerm}"

      let stx ← `(tactic| rcases $appTerm $argTerms* with $rcasesPat | $rcasesPat)
      trace[gsplit] "stx: {stx}"
      evalTactic stx

end Flean.Gsplit
