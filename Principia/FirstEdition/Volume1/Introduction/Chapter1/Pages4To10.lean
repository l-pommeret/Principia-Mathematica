namespace PM.FirstEdition.Volume1.Introduction.Chapter1

/-! # Chapter I. Preliminary Explanations of Ideas and Notations

Canonical edition: first edition, volume I (1910), pp. 4–10, scan leaves
26–32. Notes are transcribed in distinct, linked source blocks below.
-/

/- PM-VERBATIM-BEGIN PM1:INTRODUCTION-CH1-PP4-10
CHAPTER I.

PRELIMINARY EXPLANATIONS OF IDEAS AND NOTATIONS.

THE notation adopted in the present work is based upon that of Peano, and the
following explanations are to some extent modelled on those which he prefixes
to his Formulario Mathematico. His use of dots as brackets is adopted, and so
are many of his symbols.

Variables. The idea of a variable, as it occurs in the present work, is more
general than that which is explicitly used in ordinary mathematics. In
ordinary mathematics, a variable generally stands for an undetermined number
or quantity. In mathematical logic, any symbol whose meaning is not determinate
is called a variable, and the various determinations of which its meaning is
susceptible are called the values of the variable. The values may be any set
of entities, propositions, functions, classes or relations, according to
circumstances. If a statement is made about “Mr A and Mr B,” “Mr A” and “Mr B”
are variables whose values are confined to men. A variable may either have a
conventionally-assigned range of values, or may (in the absence of any
indication of the range of values) have as the range of its values all
determinations which render the statement in which it occurs significant. Thus
when a text-book of logic asserts that “A is A,” without any indication as to
what A may be, what is meant is that any statement of the form “A is A” is
true. We may call a variable restricted when its values are confined to some
only of those of which it is capable; otherwise, we shall call it unrestricted.
Thus when an unrestricted variable occurs, it represents any object such that
the statement concerned can be made significantly (i.e. either truly or
falsely) concerning that object. For the purposes of logic, the unrestricted
variable is more convenient than the restricted variable, and we shall always
employ it. We shall find that the unrestricted variable is still subject to
limitations imposed by the manner of its occurrence, i.e. things which can be
said significantly concerning a proposition cannot be said significantly
concerning a class or a relation, and so on. But the limitations to which the
unrestricted variable is subject do not need to be explicitly indicated, since
they are the limits of significance of the statement in which the variable
occurs, and are therefore intrinsically determined by this statement. This
will be more fully explained later[1].

To sum up, the three salient facts connected with the use of the variable are:
(1) that a variable is ambiguous in its denotation and accordingly undefined:
(2) that a variable preserves a recognizable identity in various occurrences
throughout the same context, so that many variables can occur together in the
same context each with its separate identity: and (3) that either the range of
possible determinations of two variables may be the same, so that a possible
determination of one variable is also a possible determination of the other,
or the ranges of two variables may be different, so that, if a possible
determination of one variable is given to the other, the resulting complete
phrase is meaningless instead of becoming a complete unambiguous proposition
(true or false) as would be the case if all variables in it had been given any
suitable determinations.

The uses of various letters. Variables will be denoted by single letters, and
so will certain constants; but a letter which has once been assigned to a
constant by a definition must not afterwards be used to denote a variable. The
small letters of the ordinary alphabet will all be used for variables, except
p and s after ✱40, in which constant meanings are assigned to these two
letters. The following capital letters will receive constant meanings: B, C,
D, E, F, I and J. Among small Greek letters, we shall give constant meanings
to ε, ι, π and (at a later stage) to η, θ and ω. Certain Greek capitals will
from time to time be introduced for constants, but Greek capitals will not be
used for variables. Of the remaining letters, p, q, r will be called
propositional letters, and will stand for variable propositions (except that,
from ✱40 onwards, p must not be used for a variable); f, g, φ, ψ, χ, θ and
(until ✱33) F will be called functional letters, and will be used for variable
functions.

The small Greek letters not already mentioned will be used for variables whose
values are classes, and will be referred to simply as Greek letters. Ordinary
capital letters not already mentioned will be used for variables whose values
are relations, and will be referred to simply as capital letters. Ordinary
small letters other than p, q, r, s, f, g will be used for variables whose
values are not known to be functions, classes, or relations; these letters
will be referred to simply as small Latin letters.

After the early part of the work, variable propositions and variable functions
will hardly ever occur. We shall then have three main kinds of variables:
variable classes, denoted by small Greek letters; variable relations, denoted
by capitals; and variables not given as necessarily classes or relations,
which will be denoted by small Latin letters.

In addition to this usage of small Greek letters for variable classes, capital
letters for variable relations, small Latin letters for variables of type
wholly undetermined by the context (these arise from the possibility of
“systematic ambiguity,” explained later in the explanations of the theory of
types), the reader need only remember that all letters represent variables,
unless they have been defined as constants in some previous place in the book.
In general the structure of the context determines the scope of the variables
contained in it; but the special indication of the nature of the variables
employed, as here proposed, saves considerable labour of thought.

The fundamental functions of propositions. An aggregation of propositions,
considered as wholes not necessarily unambiguously determined, into a single
proposition more complex than its constituents, is a function with propositions
as arguments. The general idea of such an aggregation of propositions, or of
variables representing propositions, will not be employed in this work. But
there are four special cases which are of fundamental importance, since all
the aggregations of subordinate propositions into one complex proposition
which occur in the sequel are formed out of them step by step.

They are (1) the Contradictory Function, (2) the Logical Sum, or Disjunctive
Function, (3) the Logical Product, or Conjunctive Function, (4) the Implicative
Function. These functions in the sense in which they are required in this work
are not all independent; and if two of them are taken as primitive undefined
ideas, the other two can be defined in terms of them. It is to some
extent—though not entirely—arbitrary as to which functions are taken as
primitive. Simplicity of primitive ideas and symmetry of treatment seem to be
gained by taking the first two functions as primitive ideas.

The Contradictory Function with argument p, where p is any proposition, is the
proposition which is the contradictory of p, that is, the proposition asserting
that p is not true. This is denoted by ∼p. Thus ∼p is the contradictory function
with p as argument and means the negation of the proposition p. It will also be
referred to as the proposition not-p. Thus ∼p means not-p, which means the
negation of p.

The Logical Sum is a propositional function with two arguments p and q, and is
the proposition asserting p or q disjunctively, that is, asserting that at
least one of the two p and q is true. This is denoted by p ∨ q. Thus p ∨ q is
the logical sum with p and q as arguments. It is also called the logical sum
of p and q. Accordingly p ∨ q means that at least p or q is true, not excluding
the case in which both are true.

The Logical Product is a propositional function with two arguments p and q,
and is the proposition asserting p and q conjunctively, that is, asserting
that both p and q are true. This is denoted by p . q, or—in order to make the
dots act as brackets in a way to be explained immediately—by p : q, or by
p :. q, or by p :: q. Thus p . q is the logical product with p and q as
arguments. It is also called the logical product of p and q. Accordingly p . q
means that both p and q are true. It is easily seen that this function can be
defined in terms of the two preceding functions. For when p and q are both
true it must be false that either ∼p or ∼q is true. Hence in this book p . q is
merely a shortened form of symbolism for

∼(∼p ∨ ∼q).

If any further idea attaches to the proposition “both p and q are true,” it is
not required here.

The Implicative Function is a propositional function with two arguments p and
q, and is the proposition that either not-p or q is true, that is, it is the
proposition ∼p ∨ q. Thus if p is true, ∼p is false, and accordingly the only
alternative left by the proposition ∼p ∨ q is that q is true. In other words
if p and ∼p ∨ q are both true, then q is true. In this sense the proposition
∼p ∨ q will be quoted as stating that p implies q. The idea contained in this
propositional function is so important that it requires a symbolism which with
direct simplicity represents the proposition as connecting p and q without
the intervention of ∼p. But “implies” as used here expresses nothing else than
the connection between p and q also expressed by the disjunction “not-p or q.”
The symbol employed for “p implies q,” i.e. for “∼p ∨ q” is “p ⊃ q.” This
symbol may also be read “if p, then q.” The association of implication with
the use of an apparent variable produces an extension called “formal
implication.” This is explained later: it is an idea derivative from
“implication” as here defined. When it is necessary explicitly to discriminate
“implication” from “formal implication,” it is called “material implication.”
Thus “material implication” is simply “implication” as here defined. The
process of inference, which in common usage is often confused with implication,
is explained immediately.

These four functions of propositions are the fundamental constant (i.e.
definite) propositional functions with propositions as arguments, and all other
constant propositional functions with propositions as arguments, so far as
they are required in the present work, are formed out of them by successive
steps. No variable propositional functions of this kind occur in this work.

Equivalence. The simplest example of the formation of a more complex function
of propositions by the use of these four fundamental forms is furnished by
“equivalence.” Two propositions p and q are said to be “equivalent” when p
implies q and q implies p. This relation between p and q is denoted by “p ≡ q.”
Thus “p ≡ q” stands for “(p ⊃ q) . (q ⊃ p).” It is easily seen that two
propositions are equivalent when, and only when, they are both true or are both
false. Equivalence rises in the scale of importance when we come to “formal
implication” and thus to “formal equivalence.” It must not be supposed that two
propositions which are equivalent are in any sense identical or even remotely
concerned with the same topic. Thus “Newton was a man” and “the sun is hot” are
equivalent as being both true, and “Newton was not a man” and “the sun is cold”
are equivalent as being both false. But here we have anticipated deductions
which follow later from our formal reasoning. Equivalence in its origin is
merely mutual implication as stated above.

Truth-values. The “truth-value” of a proposition is truth if it is true, and
falsehood if it is false[2]. It will be observed that the truth-values of
p ∨ q, p . q, p ⊃ q, ∼p, p ≡ q depend only upon those of p and q, namely the
truth-value of “p ∨ q” is truth if the truth-value of either p or q is truth,
and is falsehood otherwise; that of “p . q” is truth if that of both p and q is
truth, and is falsehood otherwise; that of “p ⊃ q” is truth if either that of p
is falsehood or that of q is truth; that of “∼p” is the opposite of that of p;
and that of “p ≡ q” is truth if p and q have the same truth-value, and is
falsehood otherwise. Now the only ways in which propositions will occur in the
present work are ways derived from the above by combinations and repetitions.
Hence it is easy to see (though it cannot be formally proved except in each
particular case) that if a proposition p occurs in any proposition f(p) which
we shall ever have occasion to deal with, the truth-value of f(p) will depend,
not upon the particular proposition p, but only upon its truth-value; i.e. if
p ≡ q, we shall have f(p) ≡ f(q). Thus whenever two propositions are known to
be equivalent, either may be substituted for the other in any formula with
which we shall have occasion to deal.

We may call a function f(p) a “truth-function” when its argument p is a
proposition, and the truth-value of f(p) depends only upon the truth-value of p.
Such functions are by no means the only common functions of propositions. For
example, “A believes p” is a function of p which will vary its truth-value for
different arguments having the same truth-value: A may believe one true
proposition without believing another, and may believe one false proposition
without believing another. Such functions are not excluded from our
consideration, and are included in the scope of any general propositions we
may make about functions; but the particular functions of propositions which
we shall have occasion to construct or to consider explicitly are all
truth-functions. This fact is closely connected with a characteristic of
mathematics, namely, that mathematics is always concerned with extensions
rather than intensions. The connection, if not now obvious, will become more
so when we have considered the theory of classes and relations.

Assertion-sign. The sign “⊢,” called the “assertion-sign,” means that what
follows is asserted. It is required for distinguishing a complete proposition,
which we assert, from any subordinate propositions contained in it but not
asserted. In ordinary written language a sentence contained between full stops
denotes an asserted proposition, and if it is false the book is in error. The
sign “⊢” prefixed to a proposition serves this same purpose in our symbolism.
For example, if “⊢(p ⊃ p)” occurs, it is to be taken as a complete assertion
convicting the authors of error unless the proposition “p ⊃ p” is true (as it
is). Also a proposition stated in symbols without this sign “⊢” prefixed is
not asserted, and is merely put forward for consideration, or as a subordinate
part of an asserted proposition.

Inference. The process of inference is as follows: a proposition “p” is
asserted, and a proposition “p implies q” is asserted, and then as a sequel the
proposition “q” is asserted. The trust in inference is the belief that if the
two former assertions are not in error, the final assertion is not in error.
Accordingly whenever, in symbols, where p and q have of course special
determinations,

“⊢p” and “⊢(p ⊃ q)”

have occurred, then “⊢q” will occur if it is desired to put it on record. The
process of the inference cannot be reduced to symbols. Its sole record is the
occurrence of “⊢q.” It is of course convenient, even at the risk of repetition,
to write “⊢p” and “⊢(p ⊃ q)” in close juxtaposition before proceeding to “⊢q”
as the result of an inference. When this is to be done, for the sake of drawing
attention to the inference which is being made, we shall write instead

“⊢p ⊃ ⊢q,”

which is to be considered as a mere abbreviation of the threefold statement

“⊢p” and “⊢(p ⊃ q)” and “⊢q.”

Thus “⊢p ⊃ ⊢q” may be read “p, therefore q,” being in fact the same
abbreviation, essentially, as this is; for “p, therefore q” does not explicitly
state, what is part of its meaning, that p implies q. An inference is the
dropping of a true premiss; it is the dissolution of an implication.

The use of dots. Dots on the line of the symbols have two uses, one to bracket
off propositions, the other to indicate the logical product of two
propositions. Dots immediately preceded or followed by “∨” or “⊃” or “≡” or
“⊢,” or by “(x),” “(x, y),” “(x, y, z)” ... or “(∃x),” “(∃x, y),”
“(∃x, y, z)” ... or “[(ιx)(φx)]” or “[Rʻy]” or analogous expressions, serve to
bracket off a proposition; dots occurring otherwise serve to mark a logical
product. The general principle is that a larger number of dots indicates an
outside bracket, a smaller number indicates an inside bracket. The exact rule
as to the scope of the bracket indicated by dots is arrived at by dividing the
occurrences of dots into three groups which we will name I, II, and III. Group I
consists of dots adjoining a sign of implication (⊃) or of equivalence (≡) or
of disjunction (∨) or of equality by definition (= Df). Group II consists of
dots following brackets indicative of an apparent variable, such as (x) or
(x, y) or (∃x) or (∃x, y) or [(ιx)(φx)] or analogous expressions[3]. Group III
consists of dots which stand between propositions in order to indicate a
logical product. Group I is of greater force than Group II, and Group II than
Group III. The scope of the bracket indicated by any collection of dots
extends backwards or forwards beyond any smaller number of dots, or any equal
number from a group of less force, until we reach either the end of the
asserted proposition or a greater number of dots or an equal number belonging
to a group of equal or superior force. Dots indicating a logical product have
a scope which works both backwards and forwards; other dots only work away
from the adjacent sign of disjunction, implication, or equivalence, or forward
from the adjacent symbol of one of the other kinds enumerated in Group II.

Some examples will serve to illustrate the use of dots.

“p ∨ q . ⊃ . q ∨ p” means the proposition “‘p or q’ implies ‘q or p.’” When
we assert this proposition, instead of merely considering it, we write

“⊢ : p ∨ q . ⊃ . q ∨ p,”

where the two dots after the assertion-sign show that what is asserted is the
whole of what follows the assertion-sign, since there are not as many as two
dots anywhere else. If we had written “p : ∨ : q . ⊃ . q ∨ p,” that would mean
the proposition “either p is true, or q implies ‘q or p.’” If we wished to
assert this, we should have to put three dots after the assertion-sign. If we
had written “p ∨ q . ⊃ . q : ∨ : p,” that would mean the proposition “either
‘p or q’ implies q, or p is true.” The forms “p . ∨ . q . ⊃ . q ∨ p” and
“p ∨ q . ⊃ . q . ∨ . p” have no meaning.

“p ⊃ q . ⊃ : q ⊃ r . ⊃ . p ⊃ r” will mean “if p implies q, then if q implies
r, p implies r.” If we wish to assert this (which is true) we write

“⊢ :. p ⊃ q . ⊃ : q ⊃ r . ⊃ . p ⊃ r.”

Again “p ⊃ q . ⊃ . q ⊃ r : ⊃ . p ⊃ r” will mean “if ‘p implies q’ implies
‘q implies r,’ then p implies r.” This is in general untrue. (Observe that
“p ⊃ q” is sometimes most conveniently read as “p implies q,” and sometimes
as “if p, then q.”) “p ⊃ q . q ⊃ r . ⊃ . p ⊃ r” will mean “if p implies q,
and q implies r, then p implies r.” In this formula, the first dot indicates a
logical product; hence the scope of the second dot extends backwards to the
beginning of the proposition. “p ⊃ q : q ⊃ r . ⊃ . p ⊃ r” will mean “p implies
q; and if q implies r, then p implies r.” (This is not true in general.) Here
the two dots indicate a logical product; since two dots do not occur anywhere
else, the scope of these two dots extends backwards to the beginning of the
proposition, and forwards to the end.

“p ∨ q . ⊃ :. p . ∨ . q ⊃ r : ⊃ . p ∨ r” will mean “if either p or q is
true, then if either p or ‘q implies r’ is true, it follows that either p or r
is true.”
PM-VERBATIM-END PM1:INTRODUCTION-CH1-PP4-10 -/

/- PM-EDITORIAL
This is a verbal-diplomatic reflow. Line-end hyphenation is silently rejoined;
page boundaries and typographic emphasis are recorded in metadata. The printed
reading on p. 10 is `(∃x, y)`: the Project Gutenberg witness’s `(∃x, ∼y)` is a
digital transcription error and is recorded only in the apparatus.
-/

/- PM-FORMAL-GLOSS
The prose successively introduces variables, propositional operations,
assertion, inference, and PM’s dot-scoping convention. These explanations are
not imported as axioms. Adjacent formal files may reconstruct their syntax, but
the historical claims in this block remain source prose.
-/

/- PM-VERBATIM-BEGIN PM1:INTRODUCTION-CH1-NOTE-1
[1] Cf. Chapter II of the Introduction.
PM-VERBATIM-END PM1:INTRODUCTION-CH1-NOTE-1 -/

/- PM-VERBATIM-BEGIN PM1:INTRODUCTION-CH1-NOTE-2
[2] This phrase is due to Frege.
PM-VERBATIM-END PM1:INTRODUCTION-CH1-NOTE-2 -/

/- PM-VERBATIM-BEGIN PM1:INTRODUCTION-CH1-NOTE-3
[3] The meaning of these expressions will be explained later, and examples of
the use of dots in connection with them will be given on pp. 17, 18.
PM-VERBATIM-END PM1:INTRODUCTION-CH1-NOTE-3 -/

/- PM-EDITORIAL
The printed pages use page-local asterisk note calls. Stable labels [1]–[3]
follow the chapter-wide note sequence and link these distinct note blocks to
the corresponding calls in the prose block.
-/

end PM.FirstEdition.Volume1.Introduction.Chapter1
