namespace PM.FirstEdition.Volume1.Introduction.Chapter1

/-! # Chapter I, pages 26–38

Canonical edition: first edition, volume I (1910), pp. 26–38, scan leaves
48–60. This file completes Chapter I. The four acknowledged or demonstrable
errors of the printing remain unchanged in the `PM-VERBATIM` text; corrections
are confined to the external critical apparatus.
-/

/- PM-VERBATIM-BEGIN PM1:INTRO-CH1-CLASSES-RELATIONS-CONT
Here ∈ is chosen as the initial of the word ἐστί. “x ∈ α” may be read “x is an
α.” Thus “x ∈ man” will mean “x is a man,” and so on. For typographical
convenience we shall put

x ∼∈ α . = . ∼(x ∈ α)     Df,
x, y ∈ α . = . x ∈ α . y ∈ α     Df.

For “class” we shall write “Cls”; thus “α ∈ Cls” means “α is a class.”

We have

⊢ : x ∈ ẑ(φz) . ≡ . φx,

i.e. “‘x is a member of the class determined by φẑ’ is equivalent to ‘x
satisfies φẑ,’ or to ‘φx is true.’”

A class is wholly determinate when its membership is known, that is, there
cannot be two different classes having the same membership. Thus if φx, ψx are
formally equivalent functions, they determine the same class; for in that
case, if x is a member of the class determined by φx̂, and therefore satisfies
φx, it also satisfies ψx, and is therefore a member of the class determined by
ψx̂. Thus we have

⊢ :. ẑ(φz) = ẑ(ψz) . ≡ : φx . ≡ₓ . ψx.

The following propositions are obvious and important:

⊢ :. α = ẑ(φz) . ≡ : x ∈ α . ≡ₓ . φx,

i.e. α is identical with the class determined by φẑ when, and only when, “x is
an α” is formally equivalent to φx;

⊢ :. α = β . ≡ : x ∈ α . ≡ₓ . x ∈ β,

i.e. two classes α and β are identical when, and only when, they have the same
membership;

⊢ . x̂(x ∈ α) = α,

i.e. the class whose determining function is “x is an α” is α, in other words,
α is the class of objects which are members of α;

⊢ . ẑ(φz) ∈ Cls,

i.e. the class determined by the function φẑ is a class.

It will be seen that, according to the above, any function of one variable can
be replaced by an equivalent function of the form “x ∈ α.” Hence any
extensional function of functions which holds when its argument is a function
of the form “ẑ ∈ α,” whatever possible value α may have, will hold also when
its argument is any function φẑ. Thus variation of classes can replace
variation of functions of one variable in all the propositions of the sort
with which we are concerned.

In an exactly analogous manner we introduce dual or dyadic relations, i.e.
relations between two terms. Such relations will be called simply “relations”;
relations between more than two terms will be distinguished as multiple
relations, or (when the number of their terms is specified) as triple,
quadruple, ... relations, or as triadic, tetradic, ... relations. Such
relations will not concern us until we come to Geometry. For the present, the
only relations we are concerned with are dual relations.

Relations, like classes, are to be taken in extension, i.e. if R and S are
relations which hold between the same pairs of terms, R and S are to be
identical. We may regard a relation, in the sense in which it is required for
our purposes, as a class of couples; i.e. the couple (x, y) is to be one of the
class of couples constituting the relation R if x has the relation R to y[8].
This view of relations as classes of couples will not, however, be introduced
into our symbolic treatment, and is only mentioned in order to show that it is
possible so to understand the meaning of the word relation that a relation
shall be determined by its extension.

Any function φ(x, y) determines a relation R between x and y. If we regard a
relation as a class of couples, the relation determined by φ(x, y) is the class
of couples (x, y) for which φ(x, y) is true. The relation determined by the
function φ(x, y) will be denoted by

x̂ŷ φ(x, y).

We shall use a capital letter for a relation when it is not necessary to
specify the determining function. Thus whenever a capital letter occurs, it is
to be understood that it stands for a relation.

The propositional function “x has the relation R to y” will be expressed by
the notation

xRy.

This notation is designed to keep as near as possible to common language,
which, when it has to express a relation, generally mentions it between its
terms, as in “x loves y,” “x equals y,” “x is greater than y,” and so on. For
“relation” we shall write “Rel” thus “R ∈ Rel” means “R is a relation.”

Owing to our taking relations in extension, we shall have

⊢ :. x̂ŷ φ(x, y) = x̂ŷ ψ(x, y) . ≡ : φ(x, y) . ≡ₓ,ᵧ . ψ(x, y),

i.e. two functions of two variables determine the same relation when, and only
when, the two functions are formally equivalent.

We have                    ⊢ . z{x̂ŷ φ(x, y)}w . ≡ . φ(z, w),

i.e. “z has to w the relation determined by the function φ(x, y)” is equivalent
to φ(z, w);

⊢ :. R = x̂ŷ φ(x, y) . ≡ : xRy . ≡ₓ,ᵧ . φ(x, y),
⊢ :. R = S . ≡ : xRy . ≡ₓ,ᵧ . xSy,
⊢ . x̂ŷ(xRy) = R,
⊢ . {x̂ŷ φ(x, y)} ∈ Rel.

These propositions are analogous to those previously given for classes. It
results from them that any function of two variables is formally equivalent
to some function of the form xRy; hence, in extensional functions of two
variables, variation of relations can replace variation of functions of two
variables.

Both classes and relations have properties analogous to most of those of
propositions that result from negation and the logical sum. The logical
product of two classes α and β is their common part, i.e. the class of terms
which are members of both. This is represented by α ∩ β. Thus we put

α ∩ β = x̂(x ∈ α . x ∈ β)     Df.

This gives us

⊢ : x ∈ α ∩ β . ≡ . x ∈ α . x ∈ β,

i.e. “x is a member of the logical product of α and β” is equivalent to the
logical product of “x is a member of α” and “x is a member of β.”

Similarly the logical sum of two classes α and β is the class of terms which
are members of either; we denote it by α ∪ β. The definition is

α ∪ β = x̂(x ∈ α . ∨ . x ∈ β)     Df,

and the connection with the logical sum of propositions is given by

⊢ :. x ∈ α ∪ β . ≡ : x ∈ α . ∨ . x ∈ β.

The negation of a class α consists of those terms x for which “x ∈ α” can be
significantly and truly denied. We shall find that there are terms of other
types for which “x ∈ α” is neither true nor false, but nonsense. These terms
are not members of the negation of α.

Thus the negation of a class α is the class of terms of suitable type which
are not members of it, i.e. the class x̂(x ∼∈ α). We call this class “−α” (read
“not-α”); thus the definition is

−α = x̂(x ∼∈ α)     Df,

and the connection with the negation of propositions is given by

⊢ : x ∈ −α . ≡ . x ∼∈ α.

In place of implication we have the relation of inclusion. A class α is said
to be included or contained in a class β if all members of α are members of β,
i.e. if x ∈ α . ⊃ₓ . x ∈ β. We write “α ⊂ β” for “α is contained in β.” Thus
we put

α ⊂ β . = : x ∈ α . ⊃ₓ . x ∈ β     Df.

Most of the formulae concerning p . q, p ∨ q, ∼p, p ⊃ q remain true if we
substitute α ∩ β, α ∪ β, −α, α ⊂ β. In place of equivalence, we substitute
identity; for “p ≡ q” was defined as “p ⊃ q . q ⊃ p,” but “α ⊂ β . β ⊂ α”
gives “x ∈ α . ≡ₓ . x ∈ β,” whence α = β.

The following are some propositions concerning classes which are analogues of
propositions previously given concerning propositions:

⊢ . α ∩ β = −(−α ∪ −β),

i.e. the common part of α and β is the negation of “not-α or not-β”;

⊢ . x ∈ (α ∪ −α),

i.e. “x is a member of α or not-α”;

⊢ . x ∼∈ (α ∩ −α),

i.e. “x is not a member of both α and not-α”;

⊢ . α = −(−α),
⊢ : α ⊂ β . ≡ . −β ⊂ −α,
⊢ : α = β . ≡ . −α = −β,
⊢ : α = α ∩ α,
⊢ : α = α ∪ α.

The two last are the two forms of the law of tautology.

The law of absorption holds in the form

⊢ : α ⊂ β . ≡ . α = α ∩ β.

Thus for example “all Cretans are liars” is equivalent to “Cretans are
identical with lying Cretans.”

Just as we have

⊢ : p ⊃ q . q ⊃ r . ⊃ . p ⊃ r,

so we have

⊢ : α ⊂ β . β ⊂ γ . ⊃ . α ⊂ γ.

This expresses the ordinary syllogism in Barbara (with the premisses
interchanged); for “α ⊂ β” means the same as “all α’s are β’s,” so that the
above proposition states: “If all α’s are β’s, and all β’s are γ’s, then all
α’s are γ’s.” (It should be observed that syllogisms are traditionally
expressed with “therefore,” as if they asserted both premisses and conclusion.
This is, of course, merely a slipshod way of speaking, since what is really
asserted is only the connection of premisses with conclusion.)

The syllogism in Barbara when the minor premiss has an individual subject is

⊢ : x ∈ β . β ⊂ γ . ⊃ . x ∈ γ,

e.g. “if Socrates is a man, and all men are mortals, then Socrates is a
mortal.” This, as was pointed out by Peano, is not a particular case of
“α ⊂ β . β ⊂ γ . ⊃ . α ⊂ γ,” since “x ∈ β” is not a particular case of
“α ⊂ β.” This point is important, since traditional logic is here mistaken.
The nature and magnitude of its mistake will become clearer at a later stage.

For relations, we have precisely analogous definitions and propositions. We
put

R ∩̇ S = x̂ŷ(xRy . xSy)     Df,

which leads to

⊢ : x(R ∩̇ S)y . ≡ . xRy . xSy.

Similarly

R ∪̇ S = x̂ŷ(xRy . ∨ . xSy)     Df,
−̇R = x̂ŷ{∼(xRy)}                 Df,
R ⊂̇ S . = : xRy . ⊃ₓ,ᵧ . xSy  Df.

Generally, when we require analogous but different symbols for relations and
for classes, we shall choose for relations the symbol obtained by adding a
dot, in some convenient position, to the corresponding symbol for classes.
(The dot must not be put on the line, since that would cause confusion with
the use of dots as brackets.) But such symbols require and receive a special
definition in each case.

A class is said to exist when it has at least one member: “α exists” is denoted
by “∃!α.” Thus we put

∃!α . = . (∃x) . x ∈ α     Df.

The class which has no members is called the “null-class,” and is denoted by
“Λ.” Any propositional function which is always false determines the
null-class. One such function is known to us already, namely “x is not
identical with x,” which we denote by “x ≠ x.” Thus we may use this function
for defining Λ, and put

Λ = x̂(x ≠ x)     Df.

The class determined by a function which is always true is called the
universal class, and is represented by V; thus

V = x̂(x = x)     Df.

Thus Λ is the negation of V. We have

⊢ . (x) . x ∈ V,

i.e. “‘x is a member of V’ is always true”; and

⊢ . (x) . x ∼∈ Λ,

i.e. “‘x is a member of Λ’ is always false.” Also

⊢ : α = Λ . ≡ . ∼∃!α,

i.e. “α is the null-class” is equivalent to “α does not exist.”

For relations we use similar notations. We put

∃̇!R . = . (∃x, y) . xRy,

i.e. “∃̇!R” means that there is at least one couple x, y between which the
relation R holds. Λ̇ will be the relation which never holds, and V̇ the relation
which always holds. V̇ is practically never required; Λ̇ will be the relation
x̂ŷ(x ≠ x . y ≠ y). We have

⊢ . (x, y) . ∼(xΛ̇y),
and     ⊢ : R = Λ̇ . ≡ . ∼∃̇!R.

There are no classes which contain objects of more than one type. Accordingly
there is a universal class and a null-class proper to each type of object. But
these symbols need not be distinguished, since it will be found that there is
no possibility of confusion. Similar remarks apply to relations.
PM-VERBATIM-END PM1:INTRO-CH1-CLASSES-RELATIONS-CONT -/

/- PM-FORMAL-GLOSS
This continuation develops the extensional notation for classes and relations.
Its displayed principles are historical exposition here, not new Lean axioms.
-/

/- PM-VERBATIM-BEGIN PM1:INTRO-CH1-DESCRIPTIONS
Descriptions. By a “description” we mean a phrase of the form “the so-and-so”
or of some equivalent form. For the present, we confine our attention to the
in the singular. We shall use this word strictly, so as to imply uniqueness;
e.g. we should not say “A is the son of B” if B had other sons besides A. Thus
a description of the form “the so-and-so” will only have an application in the
event of there being one so-and-so and no more. Hence a description requires
some propositional function φx̂ which is satisfied by one value of x and by no
other values; then “the x which satisfies φx̂” is a description which
definitely describes a certain object, though we may not know what object it
describes. For example, if y is a man, “x is the father of y” must be true for
one, and only one, value of x. Hence “the father of y” is a description of a
certain man, though we may not know what man it describes. A phrase containing
“the” always presupposes some initial propositional function not containing
“the”; thus instead of “x is the father of y” we ought to take as our initial
function “x begot y”; then “the father of y” means the one value of x which
satisfies this propositional function.

If φx̂ is a propositional function, the symbol “(℩x)(φx)” is used in our
symbolism in such a way that it can always be read as “the x which satisfies
φx̂.” But we do not define “(℩x)(φx)” as standing for “the x which satisfies
φx̂,” thus treating this last phrase as embodying a primitive idea. Every use
of “(℩x)(φx),” where it apparently occurs as a constituent of a proposition in
the place of an object, is defined in terms of the primitive ideas already on
hand. An example of this definition in use is given by the proposition
“E!(℩x)(φx)” which is considered immediately. The whole subject is treated
more fully in Chapter III.

The symbol should be compared and contrasted with “x̂(φx)” which in use can
always be read as “the x’s which satisfy φx̂.” Both symbols are incomplete
symbols defined only in use, and as such are discussed in Chapter III. The
symbol “x̂(φx)” always has an application, namely to the class determined by
φx; but “(℩x)(φx)” only has an application when φx̂ is only satisfied by one
value of x, neither more nor less. It should also be observed that the meaning
given to the symbol by the definition, given immediately below, of E!(℩x)(φx)
does not presuppose that we know the meaning of “one.” This is also
characteristic of the definition of any other use of (℩x)(φx).

We now proceed to define “E!(℩x)(φx)” so that it can be read “the x satisfying
φx exists.” (It will be observed that this is a different meaning of existence
from that which we express by “∃.”) Its definition is

E!(℩x)(φx) . = : (∃c) : φx . ≡ₓ . x = c     Df,

i.e. “the x satisfying φx̂ exists” is to mean “there is an object c such that
φx is true when x is c but not otherwise.”

The following are equivalent forms:

⊢ :. E!(℩x)(φx) . ≡ : (∃c) : φc : φx . ⊃ₓ . x = c,
⊢ :. E!(℩x)(φx) . ≡ : (∃c) . φc : φx . φy . ⊃ₓ,ᵧ . x = y,
⊢ :. E!(℩x)(φx) . ≡ : (∃c) : φc : x ≠ c . ⊃ₓ . ∼φx.

The last of these states that “the x satisfying φx̂ exists” is equivalent to
“there is an object c satisfying φx̂, and every object other than c does not
satisfy φx̂.”

The kind of existence just defined covers a great many cases. Thus for example
“the most perfect Being exists” will mean:

(∃c) : x is most perfect . ≡ₓ . x = c,

which, taking the last of the above equivalences, is equivalent to

(∃c) : c is most perfect : x ≠ c . ⊃ₓ . x is not most perfect.

A proposition such as “Apollo exists” is really of the same logical form,
although it does not explicitly contain the word the. For “Apollo” means
really “the object having such-and-such properties,” say “the object having
the properties enumerated in the Classical Dictionary[9].” If these properties
make up the propositional function φx, then “Apollo” means “(℩x)(φx),” and
“Apollo exists” means “E!(℩x)(φx).” To take another illustration, “the author
of Waverley” means “the man who (or rather, the object which) wrote Waverley.”
Thus “Scott is the author of Waverley” is

Scott = (℩x)(x wrote Waverley).

Here (as we observed before) the importance of identity in connection with
descriptions plainly appears.

The notation “(℩x)(φx),” which is long and inconvenient, is seldom used, being
chiefly required to lead up to another notation, namely “Rʻy,” meaning “the
object having the relation R to y.” That is, we put

Rʻy = (℩x)(xRy)     Df.

The inverted comma may be read “of.” Thus “Rʻy” is read “the R of y.” Thus if
R is the relation of father to son, “Rʻy” means “the father of y”; if R is the
relation of son to father, “Rʻy” means “the son of y,” which will only “exist”
if y has one son and no more. Rʻy is a function of y, but not a propositional
function; we shall call it a descriptive function. All the ordinary functions
of mathematics are of this kind, as will appear more fully in the sequel. Thus
in our notation, “sin y” would be written “sin ʻy,” and “sin” would stand for
the relation which sin ʻy has to y. Instead of a variable descriptive function
fy, we put Rʻy, where the variable relation R takes the place of the variable
function f. A descriptive function will in general exist while y belongs to a
certain domain, but not outside that domain; thus if we are dealing with
positive rationals, √y will be significant if y is a perfect square, but not
otherwise; if we are dealing with real numbers, and agree that “√y” is to mean
the positive square root (or, is to mean the negative square root), √y will be
significant provided y is positive, but not otherwise; and so on. Thus every
descriptive function has what we may call a “domain of definition” or a “domain
of existence,” which may be thus defined: If the function in question is Rʻy,
its domain of definition or of existence will be the class of those arguments
y for which we have E!Rʻy, i.e. for which E!(℩x)(xRy), i.e. for which there is
one x, and no more, having the relation R to y.

If R is any relation, we will speak of Rʻy as the “associated descriptive
function.” A great many of the constant relations which we shall have occasion
to introduce are only or chiefly important on account of their associated
descriptive functions. In such cases, it is easier (though less correct) to
begin by assigning the meaning of the descriptive function, and to deduce the
meaning of the relation from that of the descriptive function. This will be
done in the following explanations of notation.
PM-VERBATIM-END PM1:INTRO-CH1-DESCRIPTIONS -/

/- PM-FORMAL-GLOSS
Descriptions are explicitly introduced as incomplete symbols whose uses, not
putative denotations, receive definitions. The historical iota glyph is kept
in the transcription without adding a new logical object to the Lean kernel.
-/

/- PM-VERBATIM-BEGIN PM1:INTRO-CH1-DESCRIPTIVE-RELATION-FUNCTIONS
Various descriptive functions of relations. If R is any relation, the converse
of R is the relation which holds between y and x whenever R holds between x and
y. Thus greater is the converse of less, before of after, cause of effect,
husband of wife, etc. The converse of R is written[10] CnvʻR or Ř. The
definition is

Ř = x̂ŷ(yRx)     Df,
CnvʻR = Ř        Df.

The second of these is not a formally correct definition, since we ought to
define “Cnv” and deduce the meaning of CnvʻR. But it is not worth while to
adopt this plan in our present introductory account, which aims at simplicity
rather than formal correctness.

A relation is called symmetrical if R = Ř, i.e. if it holds between y and x
whenever it holds between x and y (and therefore vice versa). Identity,
diversity, agreement or disagreement in any respect, are symmetrical
relations. A relation is called asymmetrical when it is incompatible with its
converse, i.e. when R ∩̇ Ř = Λ̇, or, what is equivalent,

xRy . ⊃ₓ,ᵧ . ∼(yRx).

Before and after, greater and less, ancestor and descendant, are asymmetrical,
as are all other relations of the sort that lead to series. But there are many
asymmetrical relations which do not lead to series, for instance, that of
wife’s brother[11]. A relation may be neither symmetrical nor asymmetrical;
for example, this holds of the relation of inclusion between classes: α ⊂ β
and β ⊂ α will both be true if α = β, but otherwise only one of them, at most,
will be true. The relation brother is neither symmetrical nor asymmetrical,
for if x is the brother of y, y may be either the brother or the sister of x.

In the propositional function xRy, we call x the referent and y the relatum.
The class x̂(xRy), consisting of all the x’s which have the relation R to y, is
called the class of referents of y with respect to x; the class ŷ(xRy),
consisting of all the y’s to which x has the relation R, is called the class of
relata of x with respect to R. These two classes are denoted respectively by
R⃗ʻy and R⃖ʻx. Thus

R⃗ʻy = x̂(xRy)     Df,
R⃖ʻx = ŷ(yRx)     Df.

The arrow runs towards y in the first case, to show that we are concerned with
things having the relation R to y; it runs away from x in the second case to
show that the relation R goes from x to the members of R⃖ʻx. It runs in fact
from a referent and towards a relatum.

The notations R⃗ʻy, R⃖ʻx are very important, and are used constantly. If R is
the relation of parent to child, R⃗ʻy = the parents of y, R⃖ʻx = the children
of x. We have

⊢ : x ∈ R⃗ʻy . ≡ . xRy
and     ⊢ : y ∈ R⃖ʻx . ≡ . xRy.

These equivalences are often embodied in common language. For example, we say
indiscriminately “x is an inhabitant of London” or “x inhabits London.” If we
put “R” for “inhabits,” “x inhabits London” is “xR London,” while “x is an
inhabitant of London” is “x ∈ R⃗ʻLondon.”

Instead of R⃗ and R⃖ we sometimes use sgʻR, gsʻR, where “sg” stands for
“sagitta,” and “gs” is “sg” backwards. Thus we put

sgʻR = R⃗     Df,
gsʻR = R⃖     Df.

These notations are sometimes more convenient than an arrow when the relation
concerned is represented by a combination of letters, instead of a single
letter such as R. Thus e.g. we should write sgʻ(R ∩̇ S), rather than put an
arrow over the whole length of (R ∩̇ S).

The class of all terms that have the relation R to something or other is called
the domain of R. Thus if R is the relation of parent and child, the domain of R
will be the class of parents. We represent the domain of R by “DʻR.” Thus we
put

DʻR = x̂{(∃y) . xRy}     Df.

Similarly the class of all terms to which something or other has the relation
R is called the converse domain of R; it is the same as the domain of the
converse of R. The converse domain of R is represented by “ᗡʻR”; thus

ᗡʻR = ŷ{(∃x) . xRy}     Df.

The sum of the domain and the converse domain is called the field, and is
represented by CʻR: thus

CʻR = DʻR ∪ ᗡʻR     Df.

The field is chiefly important in connection with series. If R is the ordering
relation of a series, CʻR will be the class of terms of the series, DʻR will be
all the terms except the last (if any), and ᗡʻR will be all the terms except
the first (if any). The first term, if it exists, is the only member of
DʻR ∩ −ᗡʻR, since it is the only term which is a predecessor but not a
follower. Similarly the last term (if any) is the only member of ᗡʻR ∩ −DʻR.
The condition that a series should have no end is ᗡʻR ⊂ DʻR, i.e. “every
follower is a predecessor”; the condition for no beginning is DʻR ⊂ ᗡʻR.
These conditions are equivalent respectively to DʻR = CʻR and ᗡʻR = CʻR.

The relative product of two relations R and S is the relation which holds
between x and z when there is an intermediate term y such that x has the
relation R to y and y has the relation S to z. The relative product of R and S
is represented by R | S; thus we put

R | S = x̂ẑ{(∃y) . xRy . ySz}     Df,
whence     ⊢ : x(R | S)z . ≡ . (∃y) . xRy . ySz.

Thus “paternal aunt” is the relative product of sister and father; “paternal
grandmother” is the relative product of mother and father; “maternal
grandfather” is the relative product of father and mother. The relative product
is not commutative, but it obeys the associative law, i.e.

⊢ . (P | Q) | R = P | (Q | R).

It also obeys the distributive law with regard to the logical addition of
relations, i.e. we have

⊢ . P | (Q ∪̇ R) = (P | Q) ∪̇ (P | R),
⊢ . (Q ∪̇ R) | P = (Q | P) ∪̇ (Q | R).

But with regard to the logical product, we have only

⊢ . P | (Q ∩̇ R) ⊂̇ (P | Q) ∩̇ (P | R),
⊢ . (Q ∩̇ R) | P ⊂̇ (Q | P) ∩̇ (Q | R).

The relative product does not obey the law of tautology, i.e. we do not have in
general R | R = R. We put

R² = R | R     Df.

Thus paternal grandfather = (father)²,

maternal grandmother = (mother)².

A relation is called transitive when R² ⊂̇ R, i.e. when, if xRy and yRz, we
always have xRz, i.e. when

xRy . yRz . ⊃ₓ,ᵧ,𝓏 . xRz.

Relations which generate series are always transitive; thus e.g.

x > y . y > z . ⊃ₓ,ᵧ,𝓏 . x > z.

If P is a relation which generates a series, P may conveniently be read
“precedes”; thus “xPy . yPz . ⊃ₓ,ᵧ,𝓏 . xPz” becomes “if x precedes y and y
precedes z, then x always precedes z.” The class of relations which generate
series are partially characterized by the fact that they are transitive and
asymmetrical, and never relate a term to itself.

If P is a relation which generates a series, and if we have not merely
P² ⊂̇ P, but P² = P, then P generates a series which is compact (überall
dicht), i.e. such that there are terms between any two. For in this case we
have

xPz . ⊃ . (∃y) . xPy . yPz,

i.e. if x precedes z, there is a term y such that x precedes y and y precedes
z, i.e. there is a term between x and z. Thus among relations which generate
series, those which generate compact series are those for which P² = P.

Many relations which do not generate series are transitive, for example,
identity, or the relation of inclusion between classes. Such cases arise when
the relations are not asymmetrical. Relations which are transitive and
symmetrical are an important class: they may be regarded as consisting in the
possession of some common property.
PM-VERBATIM-END PM1:INTRO-CH1-DESCRIPTIVE-RELATION-FUNCTIONS -/

/- PM-EDITORIAL
Four printing errors are deliberately retained in this block: `x` for `R` in
the prose on referents; `ŷ(yRx)` for `ŷ(xRy)`; and the final `(Q | R)` in each
of the two right-distribution formulae. The apparatus supplies the corrections.
-/

/- PM-FORMAL-GLOSS
These paragraphs give the first-edition surface calculus of converse, domains,
fields and relative products. No declaration or axiom is introduced here.
-/

/- PM-VERBATIM-BEGIN PM1:INTRO-CH1-PLURAL-DESCRIPTIVE-FUNCTIONS
Plural descriptive functions. The class of terms x which have the relation R
to some member of a class α is denoted by Rʻʻα or R_∈ʻα. The definition is

Rʻʻα = x̂{(∃y) . y ∈ α . xRy}     Df.

Thus for example let R be the relation of inhabiting, and α the class of towns;
then Rʻʻα = inhabitants of towns. Let R be the relation “less than” among
rationals, and α the class of those rationals which are of the form 1 − 2⁻ⁿ,
for integral values of n; then Rʻʻα will be all rationals less than some member
of α, i.e. all rationals less than 1. If P is the generating relation of a
series, and α is any class of members of P, Pʻʻα will be predecessors of α’s,
i.e. the segment defined by α. If P is a relation such that Pʻy always exists
when y ∈ α, Pʻʻα will be the class of all terms of the form Pʻy for values of
y which are members of α; i.e.

Pʻʻα = x̂{(∃y) . y ∈ α . x = Pʻy}.

Thus a member of the class “fathers of great men” will be the father of y,
where y is some great man. In other cases, this will not hold; for instance,
let P be the relation of a number to any number of which it is a factor; then
Pʻʻ(even numbers) = factors of even numbers, but this class is not composed of
terms of the form “the factor of x,” where x is an even number, because numbers
do not have only one factor apiece.
PM-VERBATIM-END PM1:INTRO-CH1-PLURAL-DESCRIPTIVE-FUNCTIONS -/

/- PM-FORMAL-GLOSS
The doubled inverted comma denotes a plural descriptive image of a class. It is
retained as printed notation rather than normalized to a modern image operator.
-/

/- PM-VERBATIM-BEGIN PM1:INTRO-CH1-UNIT-CLASSES
Unit classes. The class whose only member is x might be thought to be identical
with x, but Peano and Frege have shown that this is not the case. (The reasons
why this is not the case will be explained in a preliminary way in Chapter II
of the Introduction.) We denote by “ιʻx” the class whose only member is x: thus

ιʻx = ŷ(y = x)     Df,

i.e. “ιʻx” means “the class of objects which are identical with x.”

The class consisting of x and y will be ιʻx ∪ ιʻy; the class got by adding x
to a class α will be α ∪ ιʻx; the class got by taking away x from a class α
will be α − ιʻx. (We write α − β as an abbreviation for α ∩ −β.)

It will be observed that unit classes have been defined without reference to
the number 1; in fact, we use unit classes to define the number 1. This number
is defined as the class of unit classes, i.e.

1 = α̂{(∃x) . α = ιʻx}     Df.

This leads to

⊢ :. α ∈ 1 . ≡ : (∃x) : y ∈ α . ≡ᵧ . y = x.

From this it appears further that

⊢ : α ∈ 1 . ≡ . E!(℩x)(x ∈ α),
whence     ⊢ : ẑ(φz) ∈ 1 . ≡ . E!(℩x)(φx),

i.e. “ẑ(φz) is a unit class” is equivalent to “the x satisfying φx̂ exists.”

If α ∈ 1, ι̌ʻα is the only member of α, for the only member of α is the only
term to which α has the relation ι. Thus “ι̌ʻα” takes the place of “(℩x)(φx),”
if α stands for ẑ(φz). In practice, “ι̌ʻα” is a more convenient notation than
“(℩x)(φx),” and is generally used instead of “(℩x)(φx).”

The above account has explained most of the logical notation employed in the
present work. In the applications to various parts of mathematics, other
definitions are introduced; but the objects defined by these later definitions
belong, for the most part, rather to mathematics than to logic. The reader who
has mastered the symbols explained above will find that any later formulae can
be deciphered by the help of comparatively few additional definitions.
PM-VERBATIM-END PM1:INTRO-CH1-UNIT-CLASSES -/

/- PM-FORMAL-GLOSS
Chapter I ends by relating descriptions to unit classes and by defining the
number 1 as the class of unit classes. These claims remain source prose in this
file and add nothing to the trusted kernel.
-/

/- PM-VERBATIM-BEGIN PM1:INTRO-CH1-NOTE-8
[8] Such a couple has a sense, i.e. the couple (x, y) is different from the
couple (y, x), unless x = y. We shall call it a “couple with sense,” to
distinguish it from the class consisting of x and y. It may also be called an
ordered couple.
PM-VERBATIM-END PM1:INTRO-CH1-NOTE-8 -/

/- PM-VERBATIM-BEGIN PM1:INTRO-CH1-NOTE-9
[9] The same principle applies to many uses of the proper names of existent
objects, e.g. to all uses of proper names for objects known to the speaker only
by report, and not by personal acquaintance.
PM-VERBATIM-END PM1:INTRO-CH1-NOTE-9 -/

/- PM-VERBATIM-BEGIN PM1:INTRO-CH1-NOTE-10
[10] The second of these notations is taken from Schröder’s Algebra und Logik
der Relative.
PM-VERBATIM-END PM1:INTRO-CH1-NOTE-10 -/

/- PM-VERBATIM-BEGIN PM1:INTRO-CH1-NOTE-11
[11] This relation is not strictly asymmetrical, but is so except when the
wife’s brother is also the sister’s husband. In the Greek Church the relation
is strictly asymmetrical.
PM-VERBATIM-END PM1:INTRO-CH1-NOTE-11 -/

/- PM-EDITORIAL
The printed leaves use page-local asterisks. Stable chapter-wide labels [8]–[11]
link the calls in the prose to these separate note blocks.
-/

end PM.FirstEdition.Volume1.Introduction.Chapter1
