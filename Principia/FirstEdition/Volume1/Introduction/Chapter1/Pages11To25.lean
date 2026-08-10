namespace PM.FirstEdition.Volume1.Introduction.Chapter1

/-! # Chapter I, pages 11–25

Canonical edition: first edition, volume I (1910), pp. 11–25, scan leaves
33–47. This file is documentary: it introduces no Lean declarations or binders.
-/

/- PM-VERBATIM-BEGIN PM1:INTRODUCTION-CH1-DEFINITIONS-PP11-12
If this is to be asserted, we
must put four dots after the assertion-sign, thus:

“⊢ :: p ∨ q.⊃ :. p. ∨ .q ⊃ r : ⊃ .p ∨ r.”

(This proposition is proved in the body of the work; it is *2·75.) If
we wish to assert (what is equivalent to the above) the proposition:
"if either p or q is true, and either p or ' q implies
r ' is true, then either p or r is true," we write

“⊢ :. p ∨ q : p. ∨ .q ⊃ r : ⊃ .p ∨ r.”

Here the first pair of dots indicates a logical product, while the
second pair does not. Thus the scope of the second pair of dots passes
over the first pair, and back until we reach the three dots after the
assertion-sign.

Other uses of dots follow the same principles, and will be explained as
they are introduced. In reading a proposition, the dots should be noticed
first, as they show its structure. In a proposition containing several signs of
implication or equivalence, the one with the greatest number of dots before
or after it is the principal one: everything that goes before this one is stated
by the proposition to imply or be equivalent to everything that comes
after it.

Definitions. A definition is a declaration that a certain
newly-introduced symbol or combination of symbols is to mean the same
as a certain other combination of symbols of which the meaning is
already known. Or, if the defining combination of symbols is one which
only acquires meaning when combined in a suitable manner with other
symbols[4], what is meant is that any combination of symbols in which
the newly-defined symbol or combination of symbols occurs is to have
that meaning (if any) which results from substituting the defining
combination of symbols for the newly-defined symbol or combination
of symbols wherever the latter occurs. We will give the names of
definiendum and definiens respectively to what is defined
and to that which it is defined as meaning. We express a definition by
putting the definiendum to the left and the definiens to
the right, with the sign "=" between, and the letters "Df" to the right
of the definiens. It is to be understood that the sign "=" and
the letters "Df" are to be regarded as together forming one symbol. The
sign "=" without the letters "Df" will have a different meaning, to be
explained shortly.

An example of a definition is

p ⊃ q . = . ∼ p ∨ q Df.

It is to be observed that a definition is, strictly speaking, no part
of the subject in which it occurs. For a definition is concerned
wholly with the symbols, not with what they symbolise. Moreover it
is not true or false, being the expression of a volition, not of a
proposition. (For this reason, definitions are not preceded by the
assertion-sign.) Theoretically, it is unnecessary ever to give a
definition: we might always use the definiens instead, and thus
wholly dispense with the definiendum. Thus although we employ
definitions and do not define "definition," yet "definition" does
not appear among our primitive ideas, because the definitions are no
part of our subject, but are, strictly speaking, mere typographical
conveniences. Practically, of course, if we introduced no definitions,
our formulae would very soon become so lengthy as to be unmanageable;
but theoretically, all definitions are superfluous.

In spite of the fact that definitions are theoretically superfluous, it
is nevertheless true that they often convey more important information
than is contained in the propositions in which they are used. This
arises from two causes. First, a definition usually implies that
the definiens is worthy of careful consideration. Hence the
collection of definitions embodies our choice of subjects and our
judgment as to what is most important. Secondly, when what is defined
is (as often occurs) something already familiar, such as cardinal or
ordinal numbers, the definition contains an analysis of a common idea,
and may therefore express a notable advance. Cantor's definition of the
continuum illustrates this: his definition amounts to the statement
that what he is defining is the object which has the properties
commonly associated with the word "continuum," though what precisely
constitutes these properties had not before been known. In such cases,
a definition is a "making definite": it gives definiteness to an idea
which had previously been more or less vague.

For these reasons, it will be found, in what follows, that the
definitions are what is most important, and what most deserves the
reader's prolonged attention.

Some important remarks must be made respecting the variables occurring
in the definiens and the definiendum. But these will be
deferred till the notion of an "apparent variable" has been introduced,
when the subject can be considered as a whole.

Summary of preceding statements. There are, in the above,
three primitive ideas which are not "defined" but only descriptively
explained. Their primitiveness is only relative to our exposition
of logical connection and is not absolute; though of course such an
exposition gains in importance according to the simplicity of its
primitive ideas. These ideas are symbolised by " ∼ p " and " p
∨ q ," and by " ⊢ " prefixed to a proposition.

Three definitions have been introduced:

p . q . = . ∼ (∼ p ∨ ∼ q) Df,

p ⊃ q . = . ∼ p ∨ q Df,

p ≡ q . = . p ⊃ q . q ⊃ p Df.
PM-VERBATIM-END PM1:INTRODUCTION-CH1-DEFINITIONS-PP11-12 -/

/- PM-FORMAL-GLOSS
Definitions, dot scope, and the summary of the three primitive ideas. Definitions remain source-level declarations, not asserted propositions or Lean theorems.
-/

/- PM-VERBATIM-BEGIN PM1:INTRODUCTION-CH1-PRIMITIVES-PP13-15A
Primitive propositions. Some propositions must be assumed
without proof, since all inference proceeds from propositions
previously asserted. These, as far as they concern the functions
of propositions mentioned above, will be found stated in *1, where
the formal and continuous exposition of the subject commences. Such
propositions will be called "primitive propositions." These, like the
primitive ideas, are to some extent a matter of arbitrary choice;
though, as in the previous case, a logical system grows in importance
according as the primitive propositions are few and simple. It will be
found that owing to the weakness of the imagination in dealing with
simple abstract ideas no very great stress can be laid upon their
obviousness. They are obvious to the instructed mind, but then so are
many propositions which cannot be quite true, as being disproved by
their contradictory consequences. The proof of a logical system is
its adequacy and its coherence. That is: (1) the system must embrace
among its deductions all those propositions which we believe to be
true and capable of deduction from logical premisses alone, though
possibly they may require some slight limitation in the form of an
increased stringency of enunciation; and (2) the system must lead to no
contradictions, namely in pursuing our inferences we must never be led
to assert both p and not- p , i.e. both " ⊢ .
p " and " ⊢ . ∼ p " cannot legitimately appear.

The following are the primitive propositions employed in the calculus
of propositions. The letters "Pp" stand for "primitive proposition."

(1) Anything implied by a true premiss is true Pp.

This is the rule which justifies inference.

(2) ⊢ : p ∨ p . ⊃ . p Pp ,

i.e. if p or p is true, then p is true.

(3) ⊢ : q . ⊃ . p ∨ q Pp ,

i.e. if q is true, then p or q is true.

(4) ⊢ : p ∨ q . ⊃ . q ∨ p Pp ,

i.e. if p or q is true, then q or p is true.

(5) ⊢ : p ∨ (q ∨ r) . ⊃ . q ∨ (p ∨ r) Pp ,

i.e. if either p is true or " q or r " is true, then
either q is true or " p or r " is true.

(6) ⊢ : . q ⊃ r . ⊃ : p ∨ q . ⊃ . p ∨ r Pp ,

i.e. if q implies r , then " p or q " implies
" p or r ."

(7) Besides the above primitive propositions, we require a primitive
proposition called "the axiom of identification of real variables."
When we have separately asserted two different functions of x ,
where x is undetermined, it is often important to know whether
we can identify the x in oneassertion with the x in the
other. This will be the case—so our axiom states—if both
assertions present x as the argument to some one function, that is
to say, if φ x is a constituent in both assertions (whatever
propositional function φ may be), or, more generally, if φ(x, y, z, )
is a constituent in one assertion, and φ (x, u, v, )
is a constituent in the other. This axiom introduces notions which
have not yet been explained; for a fuller account, see the remarks
accompanying *3·03 (which is the statement of
this axiom) in the body of the work, as well as the explanation of
propositional functions and ambiguous assertion to be given shortly.

Some simple propositions. In addition to the primitive
propositions we have already mentioned, the following are among the
most important of the elementary properties of propositions appearing
among the deductions.

The law of excluded middle:

⊢ . p ∨ ∼p.

This is *2·11 below. We shall indicate in brackets the numbers given to
the following propositions in the body of the work.

The law of contradiction (*3·24):

⊢ . ∼(p.∼p).

The law of double negation (*4·13):

⊢ . p ≡ ∼(∼p).

The principle of transposition, i.e. "if p implies
q , then not- q implies not- p ," and vice versa: this
principle has various forms, namely

(*4·1) ⊢ : p ⊃ q. ≡ .∼q ⊃ ∼p,

(*4·11) ⊢ : p ≡ q. ≡ . ∼p ≡ ∼q,

(*4·14) ⊢ :. p . q. ⊃ . r ≡ : p. ∼r . ⊃. ∼q,

as well as others which are variants of these.

The law of tautology, in the two forms:

(*4·24) ⊢ : p. ≡ .p . p,

(*4·25) ⊢ : p. ≡ .p ∨ p,

i.e. " p is true" is equivalent to " p is true and p
is true," as well as to " p is true or p is true." From a formal
point of view, it is through the law of tautology and its consequences
that the algebra of logic is chiefly distinguished from ordinary
algebra.

The law of absorption :

(*4·71) ⊢ :. p ⊃ q. ≡ : p. ≡ . p . q,

i.e. " p implies q " is equivalent to " p is equivalent
to p . q ." This is called the law of absorption because it shows
that the factor q in the product is absorbed by the factor
p , if p implies q . This principle enables us to replace
an implication ( p ⊃ q ) by an equivalence ( p . ≡. p . q)
whenever it is convenient to do so.

An analogous and very important principle is the following:

(*4·73) ⊢ : . q . ⊃ : p . ≡ . p . q.

Logical addition and multiplication of propositions obey the
associative and commutative laws, and the distributive law in two
forms, namely

(*4·4) ⊢ :. p . q ∨ r . ≡ : p . q . ∨ . p . r,

(*4·41) ⊢ : . p . ∨ . q . r : ≡ : p ∨ q . p ∨ r.

The second of these distinguishes the relations of logical addition and
multiplication from those of arithmetical addition and multiplication.
PM-VERBATIM-END PM1:INTRODUCTION-CH1-PRIMITIVES-PP13-15A -/

/- PM-FORMAL-GLOSS
The introductory inventory of primitive propositions and simple consequences points to their systematic loci in ✱1–✱4. It creates no duplicate axioms.
-/

/- PM-VERBATIM-BEGIN PM1:INTRODUCTION-CH1-FUNCTIONS-PP15B-17
Propositional functions. Let φx be a statement
containing a variable x and such that it becomes a proposition
when x is given any fixed determined meaning. Then φx is
called a "propositional function"; it is not a proposition, since owing
to the ambiguity of x it really makes no assertion at all. Thus
" x is hurt" really makes no assertion at all, till we have settled
who x is. Yet owing to the individuality retained by the ambiguous
variable x , it is an ambiguous example from the collection of
propositions arrived at by giving all possible determinations to x
in " x is hurt" which yield a proposition, true or false. Also if
" x is hurt" and " y is hurt" occur in the same context,
where y is another variable, then according to the determinations
given to x and y , they can be settled to be (possibly) the same
proposition or (possibly) different propositions. But apart from some
determination given to x and y , they retain in that context
their ambiguous differentiation. Thus " x is hurt" is an ambiguous
"value" of a propositional function. When we wish to speak of the
propositional function corresponding to " x is hurt," we shall write
" x̂ is hurt." Thus " x̂ is hurt" is the propositional
function and " x is hurt" is an ambiguous value of that function.
Accordingly though " x is hurt" and " y is hurt" occurring
in the same context can be distinguished, " x̂ is hurt"
and " ŷ is hurt" convey no distinction of meaning at all.
More generally, φx is an ambiguous value of the propositional
function φx̂ , and when a definite signification a
is substituted for x , φa is an unambiguous value of
φx̂ .

Propositional functions are the fundamental kind from which the more
usual kinds of function, such as " x " or " x " or
"the father of x ," are derived. These derivative functions are
considered later, and are called "descriptive functions." The functions
of propositions considered above are a particular case of propositional
functions.

The range of values and total variation. Thus corresponding
to any propositional function of φx̂ , there is a range, or
collection, of values, consisting of all the propositions (true or
false) which can be obtained by givingevery possible determination to
x in φx . A value of x for which φx is true
will be said to "satisfy" φx̂ . Now in respect to the truth
or falsehood of propositions of this range three important cases must
be noted and symbolised. These cases are given by three propositions
of which one at least must be true. Either (1) all propositions of the
range are true, or (2) some propositions of the range are true, or (3)
no proposition of the range is true. The statement (1) is symbolised
by " (x) . φx ," and (2) is symbolised by " (∃
x) . φx ." No definition is given of these two symbols,
which accordingly embody two new primitive ideas in our system. The
symbol " (x) . φx " may be read " φx always," or
" φx is always true," or " φx is true for all possible
values of x ." The symbol " (∃ x) . φx " may be
read "there exists an x for which φx is true," or "there
exists an x satisfying φx̂ ," and thus conforms to the
natural form of the expression of thought.

Proposition (3) can be expressed in terms of the fundamental ideas now
on hand. In order to do this, note that " ∼φx " stands for
the contradictory of φx . Accordingly ∼φx̂ is
another propositional function such that each value of φx̂
contradicts a value of ∼φx̂ and vice versa. Hence
" (x) . ∼φx " symbolises the proposition that every
value of φx̂ is untrue. This is number (3) as stated above.

It is an obvious error, though one easy to commit, to assume that
cases (1) and (3) are each other's contradictories. The symbolism
exposes this fallacy at once, for (1) is (x) . φx , and
(3) is (x) . ∼φx , while the contradictory of (1) is
∼{(x) . φx}. For the sake of brevity of symbolism
a definition is made, namely

∼(x) . φx . = . ∼{(x) . φx} Df.

Definitions of which the object is to gain some trivial advantage in
brevity by a slight adjustment of symbols will be said to be of "merely
symbolic import," in contradistinction to those definitions which
invite consideration of an important idea.

The proposition (x) . φx is called the "total variation"
of the function φx̂ .

For reasons which will be explained in Chapter II, we do not take
negation as a primitive idea when propositions of the forms (x). φx
and (∃ x) . φx are concerned, but
we define the negation of (x) . φx , i.e.
of " φx is always true," as being " φx is sometimes
false," i.e. " (∃ x) . ∼φx ," and
similarly we define the negation of (∃ x) . φx
as being (x) . ∼φx . Thus we put

∼{(x) . φx} . = . (∃ x) . ∼φx Df,

∼{(∃ x) . φx} . = . (x) . ∼φx Df.

In like manner we define a disjunction in which one of the propositions
is of the form " (x) . φx " or "( ∃ x) .φx "
in terms of a disjunction of propositions not of this form, putting

(x) . φx . ∨ . p : = . (x) . φx ∨ p Df,

i.e. "either φ x is always true, or p is true" is to
mean "' φ x or p ' is always true," with similar definitions
in other cases. This subject is resumed in Chapter II, and in *9 in the
body of the work.

Apparent variables. The symbol "( x) . φ x " denotes one
definite proposition, and there is no distinction in meaning between
"( x) . φ x " and " (y) . φ y " when they occur in the same
context. Thus the " x " in " (x) . φ x " is not an ambiguous
constituent of any expression in which "( x) . φ x " occurs; and
such an expression does not cease to convey a determinate meaning by
reason of the ambiguity of the x in the " φ x ." The symbol "( x). φ x "
has some analogy to the symbol

“∫ₐᵇ φ(x) dx”

for definite integration, since in neither case is the expression a
function of x .

The range of x in "( x) . φ x " or "( ∃ x) . φ x "
extends over the complete field of the values of x for
which " φ x " has meaning, and accordingly the meaning of "( x). φ x "
or "( ∃ x) . φ x " involves the supposition
that such a field is determinate. The x which occurs in "( x) .φ x "
or "( ∃ x) . φ x " is called (following Peano)
an "apparent variable." It follows from the meaning of "( ∃ x). φ x "
that the x in this expression is also an apparent
variable. A proposition in which x occurs as an apparent variable
is not a function of x . Thus e.g. "( x) . x = x " will
mean "everything is equal to itself." This is an absolute constant,
not a function of a variable x . This is why the x is called an
apparent variable in such cases.

Besides the "range" of x in "( x) . φ x " or
"( ∃ x) . φ x ," which is the field of the values that
x may have, we shall speak of the "scope" of x , meaning
the function of which all values or some value are being affirmed. If
we are asserting all values (or some value) of " φ x ," " φ x "
is the scope of x ; if we are asserting all values (or some
value) of " φ x ⊃ p ," " φ x ⊃ p " is the scope
of x ; if we are asserting all values (or some value) of " φ x ⊃ ψ x ,"
" φ x ⊃ ψ x " will be the scope of x , and so on. The
scope of x is indicated by the number of dots after the "( x )"
or " ∃ x "; that is to say, the scope extends forwards until we
reach an equal number of dots not indicating a logical product, or a
greater number indicating a logical product, or the end of the asserted
proposition in which the "( x )" or " ∃ x " occurs, whichever
of these happens first[5]. Thus e.g.

“(x) : φ x . ⊃ . ψ x ”

will mean " φ x always implies ψ x ," but

“(x) . φ x . ⊃ . ψ x ”

will mean "if φ x is always true, then ψ x is true for
the argument x ."

Note that in the proposition

(x) . φ x . ⊃ . ψ x

the two x 's have no connection with each other. Since only one dot
follows the x in brackets, the scope of the first x is limited
to the " φx " immediately following the x in brackets. It
usually conduces to clearness to write

(x) . φx . ⊃ . ψy

rather than (x) . φx . ⊃ . ψx,

since the use of different letters emphasises the absence of connection
between the two variables; but there is no logical necessity to use
different letters, and it is sometimes convenient to use the
same letter.
PM-VERBATIM-END PM1:INTRODUCTION-CH1-FUNCTIONS-PP15B-17 -/

/- PM-FORMAL-GLOSS
Propositional functions, total variation, and apparent variables are recorded without identifying a real-variable context with quantification.
-/

/- PM-VERBATIM-BEGIN PM1:INTRODUCTION-CH1-REAL-VARIABLES-PP18-20A
Ambiguous assertion and the real variable. Any value
" φx " of the function φx̂ can be asserted. Such an
assertion of an ambiguous member of the values of φx̂ is
symbolised by

“⊢ . φx.”

Ambiguous assertion of this kind is a primitive idea, which cannot
be defined in terms of the assertion of propositions. This primitive
idea is the one which embodies the use of the variable. Apart from
ambiguous assertion, the consideration of " φx ," which is an
ambiguous member of the values of φx̂ , would be of little
consequence. When we are considering or asserting " φx ," the
variable x is called a "real variable." Take, for example, the law
of excluded middle in the form which it has in traditional formal logic:

“ a is either b or not b.”

Here a and b are real variables: as they vary, different
propositions are expressed, though all of them are true. While a
and b are undetermined, as in the above enunciation, no one
definite proposition is asserted, but what is asserted is any
value of the propositional function in question. This can only be
legitimately asserted if, whatever value may be chosen, that value is
true, i.e. if all the values are true. Thus the above form of
the law of excluded middle is equivalent to

“(a, b).a is either b or not b,”

i.e. to "it is always true that a is either b or not
b ." But these two, though equivalent, are not identical, and we
shall find it necessary to keep them distinguished.

When we assert something containing a real variable, as in e.g.

“⊢ . x = x,”

we are asserting any value of a propositional function. When we
assert something containing an apparent variable, as in

“⊢ . (x) . x = x”

or “⊢ . (∃ x) . x = x,”

we are asserting, in the first case all values, in the second
case some value (undetermined), of the propositional function in
question. It is plain thatwe can only legitimately assert "any
value" if all values are true; for otherwise, since the value of
the variable remains to be determined, it might be so determined as to
give a false proposition. Thus in the above instance, since we have

⊢ . x = x

we may infer ⊢ . (x) . x = x.

And generally, given an assertion containing a real variable x , we
may transform the real variable into an apparent one by placing the
x in brackets at the beginning, followed by as many dots as there
are after the assertion-sign.

When we assert something containing a real variable, we cannot strictly
be said to be asserting a proposition, for we only obtain a
definite proposition by assigning a value to the variable, and then our
assertion only applies to one definite case, so that it has not at all
the same force as before. When what we assert contains a real variable,
we are asserting a wholly undetermined one of all the propositions
that result from giving various values to the variable. It will be
convenient to speak of such assertions as asserting a propositional
function. The ordinary formulae of mathematics contain such
assertions; for example

“sin² x + cos² x = 1”

does not assert this or that particular case of the formula, nor does
it assert that the formula holds for all possible values of
x , though it is equivalent to this latter assertion; it simply
asserts that the formula holds, leaving x wholly undetermined;
and it is able to do this legitimately, because, however x may be
determined, a true proposition results.

Although an assertion containing a real variable does not, in
strictness, assert a proposition, yet it will be spoken of as asserting
a proposition except when the nature of the ambiguous assertion
involved is under discussion.

Definition and real variables. When the definiens
contains one or more real variables, the definiendum must
also contain them. For in this case we have a function of the real
variables, and the definiendum must have the same meaning as the
definiens for all values of these variables, which requires that
the symbol which is the definiendum should contain the letters
representing the real variables. This rule is not always observed by
mathematicians, and its infringement has sometimes caused important
confusions of thought, notably in geometry and the philosophy of space.

In the definitions given above of " p . q " and " p ⊃ q "
and " p ≡ q ," p and q are real variables, and
therefore appear on both sides of the definition. In the definition
of " ∼{(x) . φx} " only the function considered,
namely φx̂ , is a real variable; thus so far as concerns the
rule in question, x need not appear on the left. But when a real
variable is a function, it is necessary to indicatehow the argument
is to be supplied, and therefore there are objections to omitting an
apparent variable where (as in the case before us) this is the argument
to the function which is the real variable. This appears more plainly
if, instead of a general function φ x̂ , we take some
particular function, say " x̂ = a ," and consider the definition
of ∼{(x) . x = a}. Our definition gives

∼{(x) . x = a} . = . (∃ x) . ∼(x = a) Df.

But if we had adopted a notation in which the ambiguous value " x = a ,"
containing the apparent variable x , did not occur in
the definiendum, we should have had to construct a notation
employing the function itself, namely " x̂ = a ." This does not
involve an apparent variable, but would be clumsy in practice. In fact
we have found it convenient and possible—except in the explanatory
portions—to keep the explicit use of symbols of the type " φx̂ ,"
either as constants [e.g. x̂ = a ] or as real variables,
almost entirely out of this work.
PM-VERBATIM-END PM1:INTRODUCTION-CH1-REAL-VARIABLES-PP18-20A -/

/- PM-FORMAL-GLOSS
Ambiguous assertion is historically primitive and remains represented by derivability over a real-variable context. No universal binder is introduced here.
-/

/- PM-VERBATIM-BEGIN PM1:INTRODUCTION-CH1-FORMAL-IMPLICATION-PP20B-23A
Propositions connecting real and apparent variables. The most important
propositions connecting real and apparent variables are the following:

(1) "When a propositional function can be asserted, so can the
proposition that all values of the function are true." More briefly, if
less exactly, "what holds of any, however chosen, holds of all." This
translates itself into the rule that when a real variable occurs in
an assertion, we may turn it into an apparent variable by putting the
letter representing it in brackets immediately after the assertion-sign.

(2) "What holds of all, holds of any," i.e.

⊢ : (x). φ x . ⊃ . φ y.

This states "if φ x is always true, then φ y is true."

(3) "If φ y is true, then φ x is sometimes true,"
i.e.

⊢ : φ y . ⊃ . (∃ x). φ x.

An asserted proposition of the form " (∃ x). φ x " expresses
an "existence-theorem," namely "there exists an x for which
φ x is true." The above proposition gives what is in practice
the only way of proving existence-theorems: we always have to find
some particular y for which φ y holds, and thence to infer
" (∃ x). φ x ." If we were to assume what is called the
multiplicative axiom, or the equivalent axiom enunciated by Zermelo,
that would, in an important class of cases, give an existence-theorem
where no particular instance of its truth can be found.

In virtue of " ⊢ : (x). φ x . ⊃ . φ y " and
" ⊢ : φ y . ⊃ . (∃ x). φ x ," we have
" ⊢ : (x) . φ x . ⊃ . (∃ x). φ x ,"
i.e. "what is always true is sometimes true." This would not
be the case if nothing existed; thus our assumptions contain the
assumption that there is something. This is involved in the principle
that what holds of all, holds of any; for this would not be true if
there were no "any."

(4) "If φ x is always true, and ψ x is always true, then
' φ x . ψ x ' is always true," i.e.

⊢ :. (x) . φ x : (x) . ψ x : ⊃ . (x) . φ x . ψ x.

(This requires that φ and ψ should be functions which
take arguments of the same type. We shall explain this requirement at a
later stage.) The converse also holds; i.e. we have

⊢ :. (x) . φ x . ψ x . ⊃ : (x) . φ x : (x) . ψ x.

It is to some extent optional which of the propositions connecting
real and apparent variables are taken as primitive propositions. The
primitive propositions assumed, on this subject, in the body of the
work (*9), are the following:

(1) ⊢ : φ x . ⊃. (∃ z) . φ z.

(2)
⊢ : φ x ∨ φ y. ⊃ . (∃ z) . φ z,

i.e. if either φ x is true, or φ y is true, then
( ∃ z) . φ z is true. (On the necessity for this primitive
proposition, see remarks on *9·11 in the body of the work.)

(3) If we can assert φ y , where y is a real variable, then we
can assert (x) . φ x ; i.e. what holds of any, however
chosen, holds of all.

Formal implication and formal equivalence. When an implication,
say φ x . ⊃ . ψ x , is said to hold always, i.e.
when (x) : φ x . ⊃ . ψ x , we shall say that
φ x formally implies ψ x ; and propositions of the
form " (x) : φ x . ⊃ . ψ x " will be said to state
formal implications. In the usual instances of implication,
such as "'Socrates is a man' implies 'Socrates is mortal,'" we have
a proposition of the form " φ x . ⊃ . ψ x " in a case
in which " (x) : φ x . ⊃ . ψ x " is true. In such
a case, we feel the implication as a particular case of a formal
implication. Thus it has come about that implications which are not
particular cases of formal implications have not been regarded as
implications at all. There is also a practical ground for the neglect
of such implications, for, speaking generally, they can only be
known when it is already known either that their hypothesis is
false or that their conclusion is true; and in neither of these cases
do they serve to make us know the conclusion, since in the first case
the conclusion need not be true, and in the second it is known already.
Thus such implications do not serve the purpose for which implications
are chiefly useful, namely that of making us know, by deduction,
conclusions of which we were previously ignorant. Formal
implications, on the contrary, do serve this purpose, owing to the
psychological fact that we often know " (x) : φ x . ⊃ .ψ x "
and φ y , in cases where ψ y (which follows from
these premisses) cannot easily be known directly.

These reasons, though they do not warrant the complete neglect of
implications that are not instances of formal implications, are reasons
which make formal implication very important. A formal implication
states that, for all possible values of x , if the hypothesis
φ x is true, the conclusion ψ x is true. Since " φ x . ⊃ . ψ x "
will always be true when φ x is false, it is only the values of
x that make φ x true that are important in a formal
implication; what is effectively stated is that, for all these values,
ψ x is true. Thus propositions of the form "all α is
β ," "no α is β " state formal implications,
since the first (as appears by what has just been said) states

(x) : x is an α . ⊃ . x is a β,

while the second states

(x) : x is an α . ⊃ . x is not a β.

And any formal implication "( x) : φ x . ⊃ . ψ x "
may be interpreted as: "All values of x which satisfy[6] φ x
satisfy ψ x ," while the formal implication "( x) : φ x. ⊃ . ∼ψ x "
may be interpreted as: "No values of x which satisfy φ x
satisfy ψ x ."

We have similarly for "some α is β " the formula

(∃ x) . x is an α . x is a β,

and for "some α is not β " the formula

(∃ x) . x is an α . x is not a β.

Two functions φ x , ψ x are called formally
equivalent when each always implies the other, i.e. when

(x) : φ x . ≡ . ψ x,

and a proposition of this form is called a formal equivalence.
In virtue of what was said about truth-values, if φ x and
ψ x are formally equivalent, either may replace the other in
any truth-function. Hence for all the purposes of mathematics or of
the present work, φ ẑ may replace ψ ẑ or
vice versa in any proposition with which we shall be concerned. Now
to say that φ x and ψ x are formally equivalent is the
same thing as to say that φ ẑ and ψ ẑ have
the same extension, i.e. that any value of x which
satisfies either satisfies the other. Thus whenever a constant function
occurs in our work, the truth-value of the proposition in which it
occurs depends only upon the extension of the function. A proposition
containing a function φ ẑ and having this property
(i.e. that its truth-value depends only upon the extension of
φ ẑ will be called an extensional function of
φ ẑ . Thus the functions of functions with which we shall
be specially concerned will all be extensional functions of functions.

What has just been said explains the connection (noted above) between
the fact that the functions of propositions with which mathematics
is specially concerned are all truth-functions and the fact that
mathematics is concerned with extensions rather than intensions.

Convenient abbreviation. The following definitions give
alternative and often more convenient notations:

φx . ⊃ₓ . ψx :=: (x) : φx . ⊃ . ψx Df,

φx . ≡ₓ . ψx :=: (x) : φx . ≡ . ψx Df.

This notation "φx . ⊃ₓ . ψx" is due to Peano, who,
however, has no notation for the general idea " (x) . φ x ." It
may be noticed as an exercise in the use of dots as brackets that we
might have written

φx⊃ₓψx .=. (x).φx⊃ψx Df,

φx≡ₓψx .=. (x).φx≡ψx Df.

In practice however, when φ x̂ and ψ x̂ are
special functions, it is not possible to employ fewer dots than in the
first form, and often more are required.

The following definitions give abbreviated notations for functions of
two or more variables:

(x, y). φ(x, y). = : (x) : (y). φ(x, y) Df,

and so on for any number of variables;

φ(x, y) . ⊃ₓ,ᵧ . ψ(x, y) :=: (x, y) : φ(x, y) . ⊃ . ψ(x, y) Df,

and so on for any number of variables.
PM-VERBATIM-END PM1:INTRODUCTION-CH1-FORMAL-IMPLICATION-PP20B-23A -/

/- PM-FORMAL-GLOSS
The prose distinguishes particular implication from formal implication and records future rules connecting real and apparent variables. These await ✱9–✱11.
-/

/- PM-VERBATIM-BEGIN PM1:INTRODUCTION-CH1-IDENTITY-CLASSES-PP23B-25
Identity. The propositional function " x is identical with
y " is expressed by

x = y.

This will be defined (cf. *13·01), but, owing to certain difficult
points involved in the definition, we shall here omit it (cf. Chapter II). We have, of course,

⊢ . x = x (the law of identity),

⊢ : x = y . ≡ . y = x,

⊢ : x = y . y = z . ⊃ . x = z.

The first of these expresses the reflexive property of identity:
a relation is called reflexive when it holds between a term
and itself, either universally, or whenever it holds between that
term and some term. The second of the above propositions expresses
that identity is a symmetrical relation: a relation is called
symmetrical if, whenever it holds between x and y , it
also holds between y and x . The third proposition expresses
that identity is a transitive relation: a relation is called
transitive if, whenever it holds between x and y and
between y and z , it holds also between x and z .

We shall find that no new definition of the sign of equality is
required in mathematics: all mathematical equations in which the sign
of equality is used in the ordinary way express some identity, and
thus use the sign of equality in the above sense.

If x and y are identical, either can replace the other in any
proposition without altering the truth-value of the proposition; thus
we have

⊢ : x = y . ⊃ . φx ≡ φy.

This is a fundamental property of identity, from which the remaining
properties mostly follow.

It might be thought that identity would not have much importance,
since it can only hold between x and y if x and y
are different symbols for the same object. This view, however, does
not apply to what we shall call "descriptive phrases," i.e.
"the so-and-so." It is in regard to such phrases that identity is
important, as we shall shortly explain. A proposition such as "Scott
was the author of Waverley" expresses an identity in which there is a
descriptive phrase (namely "the author of Waverley"); this illustrates
how, in such cases, the assertion of identity may be important. It is
essentially the same case when the newspapers say "the identity of the
criminal has not transpired." In such a case, the criminal is known by
a descriptive phrase, namely "the man who did the deed," and we wish
to find an x of whom it is true that " x = the man who did the
deed." When such an x has been found, the identity of the criminal
has transpired.

Classes and relations. A class (which is the same as a
manifold or aggregate) is all the objects satisfying
some propositional function. If α is the class composed of
the objects satisfying φx̂ , we shall say that α
is the class determined by φx̂ . Every propositional
function thus determines a class, though if the propositional
function is one which is always false, the class will be null,
i.e. will have no members. The class determined by the function
φx̂ will be represented by ẑ (φz) [7]. Thus
for example if φx is an equation, ẑ (φz) will
be the class of its roots; if φx is " x has two legs and
no feathers," ẑ (φz) will be the class of men; if
φx is "0 < x < 1," ẑ(φz) will be the
class of proper fractions, and so on.

It is obvious that the same class of objects will have many determining
functions. When it is not necessary to specify a determining function
of a class, the class may be conveniently represented by a single Greek
letter. Thus Greek letters, other than those to which some constant
meaning is assigned, will be exclusively used for classes.

There are two kinds of difficulties which arise in formal logic; one
kind arises in connection with classes and relations and the other in
connection with descriptive functions. The point of the difficulty for
classes and relations, so far as it concerns classes, is that a class
cannot be an object suitable as an argument to any of its determining
functions. If α represents a class and φx̂ one
of its determining functions [so that α = ẑ(φz) ],
it is not sufficient that φα be a false proposition, it
must be nonsense. Thus a certain classification of what appear to be
objects into things of essentially different types seems to be rendered
necessary. This whole question is discussed in Chapter II, on the
theory of types, and the formal treatment in the systematic exposition,
which forms the main body of this work, is guided by this discussion.
The part of the systematic exposition which is specially concerned with
the theory of classes is *20, and in this Introduction it is discussed
in Chapter III. It is sufficient to note here that, in the complete
treatment of *20, we have avoided the decision as to whether a class of
things has in any sense an existence as one object. A decision of this
question in either way is indifferent to our logic, though perhaps, if
we had regarded some solution which held classes and relations to be
in some real sense objects as both true and likely to be universally
received, we might have simplified one or two definitions and a few
preliminary propositions. Our symbols, such as " x̂(φx) "
and α and others, which represent classes and relations, are
merely defined in their use, just as ∇², standing for

∂²/∂x² + ∂²/∂y² + ∂²/∂z²,

has no meaning apart from a suitable function of x , y , z
on which to operate. The result of our definitions is that the way in
which we use classes corresponds in general to their use in ordinary
thought and speech; and whatever may be the ultimate interpretation
of the one is also the interpretation of the other. Thus in fact our
classification of types in Chapter II really performs the single,
though essential, service of justifying us in refraining from entering
on trains of reasoning which lead to contradictory conclusions. The
justification is that what seem to be propositions are really nonsense.

The definitions which occur in the theory of classes, by which the
idea of a class (at least in use) is based on the other ideas assumed
as primitive, cannot be understood without a fuller discussion than
can be given now (cf. Chapter II of this Introduction and also *20).
Accordingly, in this preliminary survey, we proceed to state the more
important simple propositions which result from those definitions,
leaving the reader to employ in his mind the ordinary unanalysed
idea of a class of things. Our symbols in their usage conform to
the ordinary usage of this idea in language. It is to be noticed
that in the systematic exposition our treatment of classes and
relations requires no new primitive ideas and only two new primitive
propositions, namely the two forms of the "Axiom of Reducibility" (cf.
next Chapter) for one and two variables respectively.

The propositional function " x is a member of the class α "
will be expressed, following Peano, by the notation

x ∈ α.
PM-VERBATIM-END PM1:INTRODUCTION-CH1-IDENTITY-CLASSES-PP23B-25 -/

/- PM-FORMAL-GLOSS
Identity and classes are deferred to ✱13 and ✱20. Native Lean equality or Set is not silently substituted for PM's later defined-in-use symbols.
-/

/- PM-VERBATIM-BEGIN PM1:INTRODUCTION-CH1-NOTE-4
[4] This case will be fully considered in Chapter III of the Introduction. It need not further concern us at present.
PM-VERBATIM-END PM1:INTRODUCTION-CH1-NOTE-4 -/

/- PM-VERBATIM-BEGIN PM1:INTRODUCTION-CH1-NOTE-5
[5] This agrees with the rules for the occurrences of dots of the type of Group II as explained above, pp. 9 and 10.
PM-VERBATIM-END PM1:INTRODUCTION-CH1-NOTE-5 -/

/- PM-VERBATIM-BEGIN PM1:INTRODUCTION-CH1-NOTE-6
[6] A value of x is said to satisfy φx or φx̂ when φx is true for that value of x.
PM-VERBATIM-END PM1:INTRODUCTION-CH1-NOTE-6 -/

/- PM-VERBATIM-BEGIN PM1:INTRODUCTION-CH1-NOTE-7
[7] Any other letter may be used instead of z.
PM-VERBATIM-END PM1:INTRODUCTION-CH1-NOTE-7 -/

/- PM-EDITORIAL
The printed pages use page-local note calls. Stable labels [4]–[7] continue the
chapter-wide sequence established on pp. 4–10. The printed errata for pp. 14–15,
copy-specific manuscript annotations, and errors of digital witnesses are held
outside every canonical block in the linked critical apparatus.
-/

end PM.FirstEdition.Volume1.Introduction.Chapter1
