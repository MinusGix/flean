-- import Mathlib.Data.Int.Notation
-- import Mathlib.Data.Rat.Defs
-- import Mathlib.Data.Rat.Cast.Defs
-- import Mathlib.Tactic.Linarith
-- import Mathlib.Data.Real.Basic
-- import Mathlib.Analysis.SpecialFunctions.Log.Base
-- import Mathlib.Util.Qq
-- import Flean.PowLinarith.Lemmas
-- import Flean.PowLinarith.Datatypes

-- open Lean Meta Elab Tactic Term Mathlib.Ineq Qq

-- namespace PowLinarith

-- open Lean Meta Elab Tactic Term
-- open Batteries Mathlib

-- -- /-- Convenience: elaborate the numeral `2` at an arbitrary type that has an
-- --    `OfNat` instance. -/
-- -- private def mkTwo (α : Expr) : TermElabM Expr := do
-- --   -- let stx ← `(2 : $((← Term.ensureType α)))
-- --   let ty ← exprToSyntax (← Term.ensureType α)
-- --   dbg_trace ty
-- --   let stx ← `(@Nat.cast $(ty) _ 2)
-- --   Term.elabTerm stx (some α)


-- -- /-- A *very* conservative matcher: succeeds if `e` is syntactically
-- --    `(base : _) ^ k` for some `k : ℤ` using the heterogenous‑pow instance
-- --    `HPow.hPow` (which is what Lean generates for `^` with integer exponents). -/
-- -- private def matchBaseZPow? (base : Expr) (e : Expr) : Option Expr :=
-- --   if !e.isAppOf ``HPow.hPow then
-- --     none
-- --   else
-- --     let args := e.getAppArgs
-- --     if h : args.size = 5 then
-- --       let b := args[3]!
-- --       let k := args[4]!
-- --       if b == base then some k else none
-- --     else
-- --       none

-- -- /-- Recursively traverse an expression and collect *syntactically distinct*
-- --    exponents that appear in powers of our base.  No MetaM needed anymore. -/
-- -- partial def collectExponents (base : Expr) (e : Expr)
-- --     (acc : Std.HashSet Expr := {}) : Std.HashSet Expr :=
-- --   let acc := match matchBaseZPow? base e with
-- --     | some k => acc.insert k
-- --     | none   => acc
-- --   match e with
-- --   | Expr.app f a        => collectExponents base a (collectExponents base f acc)
-- --   | Expr.lam _ _ body _ => collectExponents base body acc
-- --   | Expr.forallE _ _ body _ => collectExponents base body acc
-- --   | Expr.letE _ t v body _ =>
-- --       let acc := collectExponents base t acc
-- --       let acc := collectExponents base v acc
-- --       collectExponents base body acc
-- --   | _ => acc


-- -- /-- Pretty‑print a set of expressions (debug helper). -/
-- -- private def showSet (s : Std.HashSet Expr) : MetaM String := do
-- --   let mut parts := #["{" ]
-- --   for e in s.toList do
-- --     let fmt ← ppExpr e
-- --     parts := parts.push (toString fmt) |>.push ", "
-- --   parts := parts.push "}"
-- --   pure <| String.intercalate "" parts.toList


-- -- syntax (name := pow_linarith) "pow_linarith" : tactic

-- -- @[tactic pow_linarith]
-- -- unsafe def evalPowLinarith : Tactic := fun stx => do
-- --   -- (1) grab the goal (we ignore local hypotheses for now).
-- --   let tgt ← Lean.Elab.Tactic.getMainTarget

-- --   -- (2) figure out the type R, then create the expression `(2 : R)`.
-- --   -- We assume the goal’s type is a `Prop`; nonetheless, any numeral *inside*
-- --   -- the goal must also have that type.  So we try to spot a numeral and fall
-- --   -- back to a metavariable trick if that fails.
-- --   let Rty ←
-- --     match tgt with
-- --     | Expr.app (Expr.app (Expr.const ``LT.lt _) lhs) _ => inferType lhs
-- --     | _ => do
-- --         -- emergency: create a fresh type `?R` and hope type‑class search fills it.
-- --         inferType (← mkFreshExprMVar none)
-- --   let two ← mkTwo Rty

-- --   -- (3) collect exponents inside the goal.
-- --   let exps := collectExponents two tgt
-- --   let dbg ← showSet exps
-- --   logInfo m!"[pow_linarith] exponents found: {dbg}"

-- --   -- TODO: generate fresh metavariables, rewrite goal, add lemmas …

-- --   -- For now just give up to `linarith` as a fallback so the tactic still *does*
-- --   -- something useful for purely linear goals.
-- --   evalTactic (← `(tactic| linarith))

-- structure PowLinarithConfig : Type where
--   exfalso : Bool := false

-- /--
-- `parseCompAndExpr e` checks if `e` is of the form `t < 0`, `t ≤ 0`, or `t = 0`.
-- If it is, it returns the comparison along with `t`.
-- -/
-- def parseCompAndExpr (e : Expr) : MetaM (Ineq × Expr) := do
--   let (rel, _, e, z) ← e.ineq?
--   if z.zero? then return (rel, e) else throwError "invalid comparison, rhs not zero: {z}"

-- /--
-- `mkSingleCompZeroOf c h` assumes that `h` is a proof of `t R 0`.
-- It produces a pair `(R', h')`, where `h'` is a proof of `c*t R' 0`.
-- Typically `R` and `R'` will be the same, except when `c = 0`, in which case `R'` is `=`.
-- If `c = 1`, `h'` is the same as `h` -- specifically, it does *not* change the type to `1*t R 0`.
-- -/
-- def mkSingleCompZeroOf (c : Nat) (h : Expr) : MetaM (Ineq × Expr) := do
--   let tp ← inferType h
--   let (iq, e) ← parseCompAndExpr tp
--   if c = 0 then do
--     let e' ← mkAppM ``zero_mul #[e]
--     return (Ineq.eq, e')
--   else if c = 1 then return (iq, h)
--   else do
--     let (_, tp, _) ← tp.ineq?
--     let cpos : Q(Prop) ← mkAppM ``GT.gt #[(← tp.ofNat c), (← tp.ofNat 0)]
--     let ex ← synthesizeUsingTactic' cpos (← `(tactic| norm_num))
--     let e' ← mkAppM iq.toConstMulName #[h, ex]
--     return (iq, e')

-- /--
-- If our goal is to add together two inequalities `t1 R1 0` and `t2 R2 0`,
-- `addIneq R1 R2` produces the strength of the inequality in the sum `R`,
-- along with the name of a lemma to apply in order to conclude `t1 + t2 R 0`.
-- -/
-- def addIneq : Ineq → Ineq → (Name × Ineq)
--   | eq, eq => (``Linarith.eq_of_eq_of_eq, eq)
--   | eq, le => (``Linarith.le_of_eq_of_le, le)
--   | eq, lt => (``Linarith.lt_of_eq_of_lt, lt)
--   | le, eq => (``Linarith.le_of_le_of_eq, le)
--   | le, le => (``Linarith.add_nonpos, le)
--   | le, lt => (``Linarith.add_lt_of_le_of_neg, lt)
--   | lt, eq => (``Linarith.lt_of_lt_of_eq, lt)
--   | lt, le => (``Linarith.add_lt_of_neg_of_le, lt)
--   | lt, lt => (``Linarith.add_neg, lt)

-- /--
-- `mkLTZeroProof coeffs pfs` takes a list of proofs of the form `tᵢ Rᵢ 0`,
-- paired with coefficients `cᵢ`.
-- It produces a proof that `∑cᵢ * tᵢ R 0`, where `R` is as strong as possible.
-- -/
-- def mkLTZeroProof : List (Expr × ℕ) → MetaM Expr
--   | [] => throwError "no linear hypotheses found"
--   | [(h, c)] => do
--       let (_, t) ← mkSingleCompZeroOf c h
--       return t
--   | ((h, c)::t) => do
--       let (iq, h') ← mkSingleCompZeroOf c h
--       let (_, t) ← t.foldlM (fun pr ce ↦ step pr.1 pr.2 ce.1 ce.2) (iq, h')
--       return t
-- where
--   /--
--   `step c pf npf coeff` assumes that `pf` is a proof of `t1 R1 0` and `npf` is a proof
--   of `t2 R2 0`. It uses `mkSingleCompZeroOf` to prove `t1 + coeff*t2 R 0`, and returns `R`
--   along with this proof.
--   -/
--   step (c : Ineq) (pf npf : Expr) (coeff : ℕ) : MetaM (Ineq × Expr) := do
--     let (iq, h') ← mkSingleCompZeroOf coeff npf
--     let (nm, niq) := addIneq c iq
--     return (niq, ← mkAppM nm #[pf, h'])

-- /-- If `prf` is a proof of `t R s`, `leftOfIneqProof prf` returns `t`. -/
-- def leftOfIneqProof (prf : Expr) : MetaM Expr := do
--   let (_, _, t, _) ← (← inferType prf).ineq?
--   return t

-- /-- If `prf` is a proof of `t R s`, `typeOfIneqProof prf` returns the type of `t`. -/
-- def typeOfIneqProof (prf : Expr) : MetaM Expr := do
--   let (_, ty, _) ← (← inferType prf).ineq?
--   return ty

-- /--
-- If `e` is a comparison `a R b` or the negation of a comparison `¬ a R b`, found in the target,
-- `getContrLemma e` returns the name of a lemma that will change the goal to an
-- implication, along with the type of `a` and `b`.

-- For example, if `e` is `(a : ℕ) < b`, returns ``(`lt_of_not_ge, ℕ)``.
-- -/
-- def getContrLemma (e : Expr) : MetaM (Name × Expr) := do
--   match ← e.ineqOrNotIneq? with
--   | (true, Ineq.lt, t, _) => pure (``lt_of_not_ge, t)
--   | (true, Ineq.le, t, _) => pure (``le_of_not_gt, t)
--   | (true, Ineq.eq, t, _) => pure (``eq_of_not_lt_of_not_gt, t)
--   | (false, _, t, _) => pure (``Not.intro, t)

-- /--
-- `applyContrLemma` inspects the target to see if it can be moved to a hypothesis by negation.
-- For example, a goal `⊢ a ≤ b` can become `a > b ⊢ false`.
-- If this is the case, it applies the appropriate lemma and introduces the new hypothesis.
-- It returns the type of the terms in the comparison (e.g. the type of `a` and `b` above) and the
-- newly introduced local constant.
-- Otherwise returns `none`.
-- -/
-- def applyContrLemma (g : MVarId) : MetaM (Option (Expr × Expr) × MVarId) := do
--   try
--     let (nm, tp) ← getContrLemma (← withReducible g.getType')
--     let [g] ← g.apply (← mkConst' nm) | failure
--     let (f, g) ← g.intro1P
--     return (some (tp, .fvar f), g)
--   catch _ => return (none, g)

-- /-- A map of keys to values, where the keys are `Expr` up to defeq and one key can be
-- associated to multiple values. -/
-- abbrev ExprMultiMap α := Array (Expr × List α)

-- /-- Retrieves the list of values at a key, as well as the index of the key for later modification.
-- (If the key is not in the map it returns `self.size` as the index.) -/
-- def ExprMultiMap.find {α : Type} (self : ExprMultiMap α) (k : Expr) : MetaM (Nat × List α) := do
--   for h : i in [:self.size] do
--     let (k', vs) := self[i]
--     if ← isDefEq k' k then
--       return (i, vs)
--   return (self.size, [])

-- /-- Insert a new value into the map at key `k`. This does a defeq check with all other keys
-- in the map. -/
-- def ExprMultiMap.insert {α : Type} (self : ExprMultiMap α) (k : Expr) (v : α) :
--     MetaM (ExprMultiMap α) := do
--   for h : i in [:self.size] do
--     if ← isDefEq self[i].1 k then
--       return self.modify i fun (k, vs) => (k, v::vs)
--   return self.push (k, [v])

-- /--
-- `partitionByType l` takes a list `l` of proofs of comparisons. It sorts these proofs by
-- the type of the variables in the comparison, e.g. `(a : ℚ) < 1` and `(b : ℤ) > c` will be separated.
-- Returns a map from a type to a list of comparisons over that type.
-- -/
-- def partitionByType (l : List Expr) : MetaM (ExprMultiMap Expr) :=
--   l.foldlM (fun m h => do m.insert (← typeOfIneqProof h) h) #[]

-- /--
-- Given a list `ls` of lists of proofs of comparisons, `findLinarithContradiction cfg ls` will try to
-- prove `False` by calling `linarith` on each list in succession. It will stop at the first proof of
-- `False`, and fail if no contradiction is found with any list.
-- -/
-- def findPowLinarithContradiction (cfg : PowLinarithConfig) (g : MVarId) (ls : List (Expr × List Expr)) :
--     MetaM Expr :=
--   try
--     ls.firstM (fun ⟨α, L⟩ =>
--       withTraceNode `linarith (return m!"{exceptEmoji ·} running on type {α}") <|
--         proveFalseByPowLinarith cfg.transparency cfg.oracle cfg.discharger g L)
--   catch e => throwError "linarith failed to find a contradiction\n{g}\n{e.toMessageData}"

-- def runPowLinarith (cfg : PowLinarithConfig) (prefType : Option Expr) (g : MVarId) (hyps : List Expr) : MetaM Unit := do
--   let singleProcess (g : MVarId) (hyps : List Expr) : MetaM Expr := g.withContext do
--     powLinarithTraceProofs s!"after preprocessing, linarith has {hyps.length} facts:" hyps
--     let mut hyp_set ← partitionByType hyps
--     trace[linarith] "hypotheses appear in {hyp_set.size} different types"
--     -- If we have a preferred type, strip it from `hyp_set` and prepare a handler with a custom
--     -- trace message
--     let pref : MetaM _ ← do
--       if let some t := prefType then
--         let (i, vs) ← hyp_set.find t
--         hyp_set := hyp_set.eraseIdxIfInBounds i
--         pure <|
--           withTraceNode `pow_linarith (return m!"{exceptEmoji ·} running on preferred type {t}") <|
--             proveFalseByPowLinarith cfg.transparency cfg.oracle cfg.discharger g vs
--       else
--         pure failure
--     pref <|> findPowLinarithContradiction cfg g hyp_set.toList

-- partial def pow_linarith (only_on : Bool) (hyps : List Expr) (cfg : PowLinarithConfig := {}) (g : MVarId) : MetaM unit := g.withContext do
--   -- if the target is an equality we simply run nlinarith twice to prove ≤ and ≥ directions
--   if (← whnfR (← instantiateMVars (← g.getType))).isEq then
--     trace[pow_linarith] "target is an equality: splitting"
--     if let some [g₁, g₂] ← try? (g.apply (← mkConst' ``eq_of_not_lt_of_not_gt)) then
--       withTraceNode `pow_linarith (return m!"{exceptEmoji ·} proving ≥") <| pow_linarith only_on hyps cfg g₁
--       withTraceNode `pow_linarith (return m!"{exceptEmoji ·} proving ≤") <| pow_linarith only_on hyps cfg g₂
--       return

--   -- If proving a comparison goal, the type of the elements is presumed to be the preferred type.
--   -- If we find a comparison hypotheses in multiple types, we will run pow_linarith on the goal type first.
--   -- In this case we also receive a new variable from moving the goal to a hypothesis
--   -- Otherwise there is no preferred type and no new variable; so we change the goal to False to prove contradiction

--   let (g, target_type, new_var) ← match ← applyContrLemma g with
--   | (none, g) =>
--     if cfg.exfalso then
--       trace[pow_linarith] "using exfalso"
--       pure (← g.exfalso, none, none)
--     else
--       pure (g, none, none)
--   | (some (t, v), g) => pure (g, some t, some v)

--   g.withContext do
--     -- get list of hyps
--     let hyps ← (if only_on then return new_var.toList ++ hyps else return (← getLocalHyps).toList ++ hyps)

--     powLinarithTraceProofs "linarith is running on the following hypotheses:" hyps
--     runPowLinarith cfg target_type g hyps

-- syntax (name := pow_linarith) "pow_linarith" "!"? powLinarithArgsRest : tactic

-- @[inherit_doc pow_linarith]
-- macro "pow_linarith!" rest:linarithArgsRest : tactic =>
--   `(tactic| pow_linarith ! $rest:powLinarithArgsRest)

-- theorem test : (2 : ℝ) ^ (2 : ℤ) = (4 : ℝ) := by pow_linarith

-- end PowLinarith
