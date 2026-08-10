# Q252 retry 01 — repair the project context and finish the exact four PM definitions

Continue the existing Q252 Aristotle project. This is a same-project continuation of task
`0f7e984b-0eec-4af6-af8f-671ac5cfcc56`; do not create a new project and do
not restart the formalization from an empty scaffold.

## Fixed target — unchanged

Formalize exactly the four first-edition `Df` items ✱9·01, ✱9·02, ✱9·011,
and ✱9·021. The target is neither wider nor narrower than the original Q252
request:

- ✱9·01: `∼{(x).φx} .=. (∃x).∼φx  Df`;
- ✱9·02: `∼{(∃x).φx} .=. (x).∼φx  Df`;
- ✱9·011 and ✱9·021 are only the printed brace-omission readings and add no
  theorem.

`Quantified.always` and `Quantified.sometimes` remain distinct primitive
binding forms. Existence must not be defined as `∼∀∼`. Do not introduce
semantic Lean `Prop`, `Not`, `Or`, `And`, `Iff`, `∀`, or `∃` as the
object language.

Return the following four declarations exactly, including their bodies:

```lean
namespace PM.FirstEdition.Volume1.Star9

abbrev star_9_01 {Γ Δ}
    (φ : PM.Apparent Γ (.elementaryProposition :: Δ)) :
    PM.FirstOrder Γ Δ :=
  PM.FirstOrder.neg (PM.FirstOrder.always φ)

abbrev star_9_02 {Γ Δ}
    (φ : PM.Apparent Γ (.elementaryProposition :: Δ)) :
    PM.FirstOrder Γ Δ :=
  PM.FirstOrder.neg (PM.FirstOrder.sometimes φ)

abbrev star_9_011 {Γ Δ}
    (φ : PM.Apparent Γ (.elementaryProposition :: Δ)) :
    PM.FirstOrder Γ Δ :=
  star_9_01 φ

abbrev star_9_021 {Γ Δ}
    (φ : PM.Apparent Γ (.elementaryProposition :: Δ)) :
    PM.FirstOrder Γ Δ :=
  star_9_02 φ

end PM.FirstEdition.Volume1.Star9
```

## Prior-run evidence and exact diagnosis

The immutable prior archive is `aristotle/results/Q252-final.tar.gz`, SHA-256
`a59ab1b65bd38ba13c7095a7ea13d999253b85437d3da99d1f234ada977c866a`.
The remote task ended `COMPLETE_WITH_ERRORS`. Its sole recorded `ERROR`
event was:

`Failed: Writing /workspace/request-project/Principia/Syntax/Apparent.lean`

(event `34ed18cf-7134-4bab-8a5e-41f296661faf`, duration 0.2 seconds). There
is no recorded Lean compiler or theorem error. After that transient write
failure, the task successfully wrote the file, ran `lake build Principia`,
and ran two `rfl` checks; its summary claims those checks succeeded.

Nevertheless, the resulting archive is not acceptable for the repository.
The compiler was run against a newly invented, standalone foundation rather
than the accepted repository API. In particular, the archive replaced
`Principia/Syntax/Apparent.lean` with unrelated declarations `Index`,
`RealSort`, `ApparentSort`, and `Argument`, and a different `Apparent`
signature. The actual repository file imports `Principia.Syntax.Formula`
and uses `RealType`, `RealVar`, `BoundVar`, and the already audited
capture-safe operations. Thus the four target abbreviations are valid and
must be preserved, but the context in which they were checked was the wrong
context. Do not retain, adapt, or extend the invented foundation.

## Work from the prior run that must be preserved

Preserve the complete diplomatic first-edition source comment already in
`Principia/FirstEdition/Volume1/Star9.lean`. Preserve the import, namespace,
and the four displayed abbreviations byte-for-byte. In particular, do not
turn any `Df` item into a theorem, an axiom, or a semantic equivalence.

## Authoritative repository context

Replace the invented `Principia/Syntax/Apparent.lean` completely. Do not
merge the two architectures. Install the two authoritative repository
context files below byte-for-byte. Their expected SHA-256 hashes are:

- `Principia/Syntax/Formula.lean`:
  `4ae57f04fe68659b5afc75e7edf065a229ca1b68ef7ada719797c5011240bb8d`;
- `Principia/Syntax/Apparent.lean`:
  `781387ff47f160b546d91106d5bf9afe5750735aec49ccb58bcf28501d4e069b`.

The additional mixed-disjunction declarations already present at the end of
the authoritative `Apparent.lean` are existing context only; Q252 must not
alter or claim them.

### `Principia/Syntax/Formula.lean`

```lean
namespace PM

/-- Types of real variables recognized by the reconstructed PM syntax.

Only elementary propositions are available in ✱1. Further constructors must be
introduced from their first audited source passages. -/
inductive RealType where
  | elementaryProposition : RealType
  deriving DecidableEq, Repr

/-- A context of *real variables* in the terminology of PM.

This is not a context of logical hypotheses. -/
abbrev RealContext := List RealType

/-- Well-typed de Bruijn variables in a real-variable context. -/
inductive RealVar : (Γ : RealContext) → RealType → Type where
  | zero : RealVar (τ :: Γ) τ
  | succ : RealVar Γ τ → RealVar (σ :: Γ) τ
  deriving DecidableEq, Repr

/-- Elementary propositions and elementary propositional functions.

An expression in the empty context is a definite elementary proposition. An
expression in a nonempty context is an elementary propositional function whose
undetermined constituents are real variables. -/
inductive Elementary : RealContext → Type where
  | constant : String → Elementary Γ
  | var : RealVar Γ .elementaryProposition → Elementary Γ
  | neg : Elementary Γ → Elementary Γ
  | disj : Elementary Γ → Elementary Γ → Elementary Γ
  deriving DecidableEq, Repr

namespace Elementary

prefix:max "∼ₚ" => neg
/-- PM's unbracketed iterated disjunction, introduced at ✱2·33, associates
to the left: `p ∨ q ∨ r` abbreviates `(p ∨ q) ∨ r`.  Formulae printed
before ✱2·33 retain their explicit brackets in the edition. -/
infixl:55 " ∨ₚ " => disj

/-- ✱1·01: `p ⊃ q .=. ∼p ∨ q  Df.`

Implication is an abbreviation, not a primitive constructor and not a theorem
asserting an object-language equivalence. -/
def imp (p q : Elementary Γ) : Elementary Γ := disj (neg p) q

infixr:54 " ⊃ₚ " => imp

end Elementary
end PM
```

### `Principia/Syntax/Apparent.lean`

```lean
import Principia.Syntax.Formula

namespace PM

/-!
# Apparent variables

This file is the capture-safe syntactic foundation required at ✱9. It does
not change `Elementary` and postulates no rules of deduction. `Apparent` is a
matrix with free apparent variables; `Quantified` performs one explicit step
to the next proposition order. Thus higher orders can be constructed one at a
time without a universe ranging over every order.
-/

/-- A context of typed apparent variables, not a context of assumptions. -/
abbrev BoundContext := List RealType

/-- Intrinsically scoped, typed de Bruijn apparent variables. -/
inductive BoundVar : (Δ : BoundContext) → RealType → Type where
  | zero : BoundVar (τ :: Δ) τ
  | succ : BoundVar Δ τ → BoundVar (σ :: Δ) τ
  deriving DecidableEq, Repr

/-- Elementary matrices in which variables from `Δ` may occur apparently. -/
inductive Apparent (Γ : RealContext) : BoundContext → Type where
  | constant : String → Apparent Γ Δ
  | real : RealVar Γ .elementaryProposition → Apparent Γ Δ
  | bound : BoundVar Δ .elementaryProposition → Apparent Γ Δ
  | neg : Apparent Γ Δ → Apparent Γ Δ
  | disj : Apparent Γ Δ → Apparent Γ Δ → Apparent Γ Δ
  deriving DecidableEq, Repr

namespace Apparent

prefix:max "∼ₐ" => neg
infixl:55 " ∨ₐ " => disj

/-- Regard a variable of the currently available PM real type as an atomic
formula. This match is intentionally exhaustive over `RealType`: adding a new
argument type later will force an audited account of its atomic formulae. -/
def boundFormula (v : BoundVar Δ .elementaryProposition) : Apparent Γ Δ :=
  .bound v

/-- The conservative inclusion of the pre-✱9 elementary syntax. -/
def ofElementary : Elementary Γ → Apparent Γ Δ
  | .constant name => .constant name
  | .var v => .real v
  | .neg proposition => .neg (ofElementary proposition)
  | .disj left right => .disj (ofElementary left) (ofElementary right)

/-- Partial erasure to elementary syntax; binders and bound variables fail. -/
def toElementary? : Apparent Γ Δ → Option (Elementary Γ)
  | .constant name => some (.constant name)
  | .real v => some (.var v)
  | .bound _ => none
  | .neg proposition => (toElementary? proposition).map .neg
  | .disj left right => do
      let p ← toElementary? left
      let q ← toElementary? right
      pure (.disj p q)

/-- Capture-free renamings of apparent variables. -/
abbrev Renaming (Δ Ξ : BoundContext) :=
  BoundVar Δ .elementaryProposition → BoundVar Ξ .elementaryProposition

/-- Lift a renaming through one binder. -/
def liftRenaming (ρ : Renaming Δ Ξ) :
    Renaming (.elementaryProposition :: Δ) (.elementaryProposition :: Ξ)
  | .zero => .zero
  | .succ v => .succ (ρ v)

/-- Embed a one-variable matrix under a new inner variable. The old head
variable becomes the outer variable (index one). -/
def outerVariableRenaming :
    Renaming (.elementaryProposition :: Δ)
      (.elementaryProposition :: .elementaryProposition :: Δ)
  | .zero => .succ .zero
  | .succ v => .succ (.succ v)

/-- Embed a one-variable matrix as the new inner variable. The old head stays
at index zero, while variables from the tail cross both binders. -/
def innerVariableRenaming :
    Renaming (.elementaryProposition :: Δ)
      (.elementaryProposition :: .elementaryProposition :: Δ)
  | .zero => .zero
  | .succ v => .succ (.succ v)

/-- Simultaneous, capture-free renaming of apparent variables. -/
def rename (ρ : Renaming Δ Ξ) : Apparent Γ Δ → Apparent Γ Ξ
  | .constant name => .constant name
  | .real v => .real v
  | .bound v => .bound (ρ v)
  | .neg proposition => .neg (rename ρ proposition)
  | .disj left right => .disj (rename ρ left) (rename ρ right)

/-- Weakening by a freshly bound apparent variable. -/
def weaken (proposition : Apparent Γ Δ) : Apparent Γ (τ :: Δ) :=
  rename (fun v => .succ v) proposition

/-- Capture-free simultaneous substitutions for apparent variables. -/
abbrev Substitution (Γ : RealContext) (Δ Ξ : BoundContext) :=
  BoundVar Δ .elementaryProposition → Apparent Γ Ξ

/-- Lift a substitution through one binder. -/
def liftSubstitution (σ : Substitution Γ Δ Ξ) :
    Substitution Γ (.elementaryProposition :: Δ)
      (.elementaryProposition :: Ξ)
  | .zero => boundFormula .zero
  | .succ v => weaken (σ v)

/-- Simultaneous, capture-free substitution of apparent variables. -/
def substitute (σ : Substitution Γ Δ Ξ) : Apparent Γ Δ → Apparent Γ Ξ
  | .constant name => .constant name
  | .real v => .real v
  | .bound v => σ v
  | .neg proposition => .neg (substitute σ proposition)
  | .disj left right => .disj (substitute σ left) (substitute σ right)

/-- The substitution which replaces the nearest binder and lowers the rest. -/
def instantiateSubstitution (argument : Apparent Γ Δ) :
    Substitution Γ (.elementaryProposition :: Δ) Δ
  | .zero => argument
  | .succ predecessor => .bound predecessor

/-- Instantiate the nearest apparent-variable binder. -/
def instantiate (body : Apparent Γ (.elementaryProposition :: Δ))
    (argument : Apparent Γ Δ) : Apparent Γ Δ :=
  substitute (instantiateSubstitution argument) body

/-- Decidable structural occurrence of a free apparent variable. -/
def significant (v : BoundVar Δ .elementaryProposition) : Apparent Γ Δ → Bool
  | .constant _ => false
  | .real _ => false
  | .bound candidate =>
      v == candidate
  | .neg proposition => significant v proposition
  | .disj left right => significant v left || significant v right

/-- Proposition-valued, auditable form of syntactic significance. -/
def Significant (v : BoundVar Δ .elementaryProposition)
    (proposition : Apparent Γ Δ) : Prop :=
  significant v proposition = true

@[simp] theorem rename_bound (ρ : Renaming Δ Ξ)
    (v : BoundVar Δ .elementaryProposition) :
    rename ρ (.bound v : Apparent Γ Δ) = .bound (ρ v) := rfl

@[simp] theorem substitute_bound (σ : Substitution Γ Δ Ξ)
    (v : BoundVar Δ .elementaryProposition) :
    substitute σ (.bound v : Apparent Γ Δ) = σ v := rfl

@[simp] theorem instantiate_zero (argument : Apparent Γ Δ) :
    instantiate
        (.bound (.zero : BoundVar (.elementaryProposition :: Δ)
          .elementaryProposition)) argument = argument := rfl

@[simp] theorem toElementary_ofElementary (proposition : Elementary Γ) :
    toElementary? (ofElementary proposition : Apparent Γ Δ) = some proposition := by
  induction proposition with
  | constant name => rfl
  | var v => rfl
  | neg proposition ih => simp [ofElementary, toElementary?, ih]
  | disj left right ihLeft ihRight =>
      simp [ofElementary, toElementary?, ihLeft, ihRight]

end Apparent

/-- One fixed step from matrices to quantified propositions.

The two constructors are PM's two primitive binding ideas, kept injectively
distinct. The parameter `Matrix` permits repetition for any *assigned* next
order; it is not a quantification over all proposition orders. -/
inductive Quantified (Matrix : BoundContext → Type) (Δ : BoundContext) where
  | always : Matrix (.elementaryProposition :: Δ) → Quantified Matrix Δ
  | sometimes : Matrix (.elementaryProposition :: Δ) → Quantified Matrix Δ

namespace Quantified

/-- Negation at one quantified order, given negation for its fixed matrix
order. Its two equations are the definitional reductions printed at ✱9·01
and ✱9·02. -/
def neg (matrixNeg : {Δ : BoundContext} → Matrix Δ → Matrix Δ) :
    Quantified Matrix Δ → Quantified Matrix Δ
  | .always body => .sometimes (matrixNeg body)
  | .sometimes body => .always (matrixNeg body)

/-- ✱9·07 at one explicitly assigned matrix order.

`renameMatrix` and `disjMatrix` are supplied for that fixed order. The result
performs exactly two quantifier steps, with `x` outermost and `y` innermost. -/
def disjAlwaysSometimes
    (renameMatrix : {Δ Ξ : BoundContext} → Apparent.Renaming Δ Ξ →
      Matrix Δ → Matrix Ξ)
    (disjMatrix : {Δ : BoundContext} → Matrix Δ → Matrix Δ → Matrix Δ)
    (φ ψ : Matrix (.elementaryProposition :: Δ)) :
    Quantified (Quantified Matrix) Δ :=
  Quantified.always
    (Quantified.sometimes
      (disjMatrix
        (renameMatrix Apparent.outerVariableRenaming φ)
        (renameMatrix Apparent.innerVariableRenaming ψ)))

/-- ✱9·08 at one explicitly assigned matrix order. The binders remain `x`
outside `y`; only the printed operand order in the matrix is reversed. -/
def disjSometimesAlways
    (renameMatrix : {Δ Ξ : BoundContext} → Apparent.Renaming Δ Ξ →
      Matrix Δ → Matrix Ξ)
    (disjMatrix : {Δ : BoundContext} → Matrix Δ → Matrix Δ → Matrix Δ)
    (ψ φ : Matrix (.elementaryProposition :: Δ)) :
    Quantified (Quantified Matrix) Δ :=
  Quantified.always
    (Quantified.sometimes
      (disjMatrix
        (renameMatrix Apparent.innerVariableRenaming ψ)
        (renameMatrix Apparent.outerVariableRenaming φ)))

@[simp] theorem neg_always
    {Matrix : BoundContext → Type}
    (matrixNeg : {Δ : BoundContext} → Matrix Δ → Matrix Δ)
    (body : Matrix (.elementaryProposition :: Δ)) :
    neg (Δ := Δ) matrixNeg (@Quantified.always Matrix Δ body) =
      @Quantified.sometimes Matrix Δ (matrixNeg body) := rfl

@[simp] theorem neg_sometimes
    {Matrix : BoundContext → Type}
    (matrixNeg : {Δ : BoundContext} → Matrix Δ → Matrix Δ)
    (body : Matrix (.elementaryProposition :: Δ)) :
    neg (Δ := Δ) matrixNeg (@Quantified.sometimes Matrix Δ body) =
      @Quantified.always Matrix Δ (matrixNeg body) := rfl

end Quantified

/-- First-order propositions: one quantified step over elementary matrices. -/
abbrev FirstOrder (Γ : RealContext) : BoundContext → Type :=
  Quantified (Apparent Γ)

/-- Propositions obtained by a second assigned quantifier step. -/
abbrev SecondOrder (Γ : RealContext) : BoundContext → Type :=
  Quantified (FirstOrder Γ)

namespace FirstOrder

/-- PM's primitive idea `(x).φx`. -/
abbrev always (body : Apparent Γ (.elementaryProposition :: Δ)) :
    FirstOrder Γ Δ := Quantified.always body

/-- PM's primitive idea `(∃x).φx`. -/
abbrev sometimes (body : Apparent Γ (.elementaryProposition :: Δ)) :
    FirstOrder Γ Δ := Quantified.sometimes body

/-- Capture-free renaming beneath either primitive binder. -/
def rename (ρ : Apparent.Renaming Δ Ξ) : FirstOrder Γ Δ → FirstOrder Γ Ξ
  | Quantified.always body =>
      Quantified.always (Apparent.rename (Apparent.liftRenaming ρ) body)
  | Quantified.sometimes body =>
      Quantified.sometimes (Apparent.rename (Apparent.liftRenaming ρ) body)

/-- Capture-free substitution beneath either primitive binder. -/
def substitute (σ : Apparent.Substitution Γ Δ Ξ) :
    FirstOrder Γ Δ → FirstOrder Γ Ξ
  | Quantified.always body =>
      Quantified.always
        (Apparent.substitute (Apparent.liftSubstitution σ) body)
  | Quantified.sometimes body =>
      Quantified.sometimes
        (Apparent.substitute (Apparent.liftSubstitution σ) body)

/-- A free apparent variable is significant in a quantified proposition when
its shifted occurrence is significant in the matrix. -/
def Significant (v : BoundVar Δ .elementaryProposition) :
    FirstOrder Γ Δ → Prop
  | Quantified.always body => Apparent.Significant (.succ v) body
  | Quantified.sometimes body => Apparent.Significant (.succ v) body

/-- First-order negation. The two constructor cases reduce definitionally to
✱9·01 and ✱9·02; no semantic Lean negation is involved. -/
def neg : FirstOrder Γ Δ → FirstOrder Γ Δ :=
  Quantified.neg (fun proposition => Apparent.neg proposition)

prefix:max "∼₁" => neg

@[simp] theorem neg_always
    (body : Apparent Γ (.elementaryProposition :: Δ)) :
    neg (always body) = sometimes (.neg body) := rfl

@[simp] theorem neg_sometimes
    (body : Apparent Γ (.elementaryProposition :: Δ)) :
    neg (sometimes body) = always (.neg body) := rfl

/-- Disjunction of a first-order proposition with an elementary proposition.
The binder is preserved and elementary disjunction is formed in its matrix;
the two branches are precisely ✱9·03 and ✱9·05. -/
def disjRightElementary : FirstOrder Γ Δ → Elementary Γ → FirstOrder Γ Δ
  | Quantified.always body, proposition =>
      always (body ∨ₐ Apparent.ofElementary proposition)
  | Quantified.sometimes body, proposition =>
      sometimes (body ∨ₐ Apparent.ofElementary proposition)

/-- Disjunction of an elementary proposition with a first-order proposition.
Operand order is retained in the matrix; the two branches are precisely
✱9·04 and ✱9·06. -/
def disjElementaryLeft : Elementary Γ → FirstOrder Γ Δ → FirstOrder Γ Δ
  | proposition, Quantified.always body =>
      always (Apparent.ofElementary proposition ∨ₐ body)
  | proposition, Quantified.sometimes body =>
      sometimes (Apparent.ofElementary proposition ∨ₐ body)

/-- ✱9·03 as a kernel reduction. -/
@[simp] theorem star_9_03_reduction
    (body : Apparent Γ (.elementaryProposition :: Δ))
    (proposition : Elementary Γ) :
    disjRightElementary (always body) proposition =
      always (body ∨ₐ Apparent.ofElementary proposition) := rfl

/-- ✱9·04 as a kernel reduction. -/
@[simp] theorem star_9_04_reduction
    (proposition : Elementary Γ)
    (body : Apparent Γ (.elementaryProposition :: Δ)) :
    disjElementaryLeft proposition (always body) =
      always (Apparent.ofElementary proposition ∨ₐ body) := rfl

/-- ✱9·05 as a kernel reduction. -/
@[simp] theorem star_9_05_reduction
    (body : Apparent Γ (.elementaryProposition :: Δ))
    (proposition : Elementary Γ) :
    disjRightElementary (sometimes body) proposition =
      sometimes (body ∨ₐ Apparent.ofElementary proposition) := rfl

/-- ✱9·06 as a kernel reduction. -/
@[simp] theorem star_9_06_reduction
    (proposition : Elementary Γ)
    (body : Apparent Γ (.elementaryProposition :: Δ)) :
    disjElementaryLeft proposition (sometimes body) =
      sometimes (Apparent.ofElementary proposition ∨ₐ body) := rfl

/-- The elementary-matrix specialization of ✱9·07. -/
def disjAlwaysSometimes
    (φ ψ : Apparent Γ (.elementaryProposition :: Δ)) : SecondOrder Γ Δ :=
  Quantified.disjAlwaysSometimes Apparent.rename Apparent.disj φ ψ

/-- The elementary-matrix specialization of ✱9·08. Arguments retain the
printed left-to-right order: existential body `ψ`, then universal body `φ`. -/
def disjSometimesAlways
    (ψ φ : Apparent Γ (.elementaryProposition :: Δ)) : SecondOrder Γ Δ :=
  Quantified.disjSometimesAlways Apparent.rename Apparent.disj ψ φ

/-- ✱9·07 as an exact kernel reduction. -/
@[simp] theorem star_9_07_reduction
    (φ ψ : Apparent Γ (.elementaryProposition :: Δ)) :
    disjAlwaysSometimes φ ψ =
      Quantified.always
        (Quantified.sometimes
          (Apparent.rename Apparent.outerVariableRenaming φ ∨ₐ
            Apparent.rename Apparent.innerVariableRenaming ψ)) := rfl

/-- ✱9·08 as an exact kernel reduction. -/
@[simp] theorem star_9_08_reduction
    (ψ φ : Apparent Γ (.elementaryProposition :: Δ)) :
    disjSometimesAlways ψ φ =
      Quantified.always
        (Quantified.sometimes
          (Apparent.rename Apparent.innerVariableRenaming ψ ∨ₐ
            Apparent.rename Apparent.outerVariableRenaming φ)) := rfl

end FirstOrder
end PM
```

## Required staged continuation

1. Inspect the current same-project files. Keep the valid Star9 source
   comment and exact four declarations. Record that the only prior error was
   the failed first write, not a Lean theorem error.
2. Replace the invented syntax foundation with the two authoritative files
   above exactly. Verify their hashes. Remove every prior-run substitute
   declaration (`Index`, `RealSort`, `ApparentSort`, `Argument`) by full-file
   replacement; do not create aliases for them.
3. Ensure `Principia/FirstEdition/Volume1/Star9.lean` imports
   `Principia.Syntax.Apparent` and contains only its preserved source comment,
   the exact four requested abbreviations, and namespace terminators.
4. Compile the authoritative context and Star9 file in the remote project.
   In a disposable check file, verify by `rfl` that `star_9_01 φ` reduces to
   `PM.FirstOrder.sometimes (.neg φ)` and `star_9_02 φ` reduces to
   `PM.FirstOrder.always (.neg φ)`. Also check that `star_9_011` and
   `star_9_021` are aliases of the first two. Delete the disposable check
   file afterward.
5. Scan all returned Lean sources. There must be no `sorry`, `admit`, new
   `axiom`, `unsafe` declaration, `@[implemented_by]`, or other escape hatch.
   Do not use `Classical`, choice, quotients, alternate syntax, generic
   substitution/inference, or target weakening.
6. Finish only after the remote Lean compiler accepts the exact target over
   the authoritative repository API. In the final summary, distinguish the
   restored context files from the sole Q252 edition addition,
   `Principia/FirstEdition/Volume1/Star9.lean`, and report the exact build and
   reduction-check commands and their successful results.

Do not change the four target bodies, the parameter contexts, the namespace,
or the canonical scope. Do not solve any later ✱9 proposition in this task.

