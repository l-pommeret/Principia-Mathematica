namespace PM.FirstEdition.Volume1.Introduction.Chapter2

/-! # Chapter II, pages 39–50

Canonical edition: first edition, volume I (1910), pp. 39–50, scan leaves
61–72. The text is a scan-collated verbal-diplomatic reflow. Printed page
breaks are metadata, and the six page-local notes are separate canonical
blocks. No printed Errata entry concerns these pages. Two errors of the
Project Gutenberg witness are recorded only in the external apparatus.
-/

/- PM-VERBATIM-BEGIN PM1:INTRODUCTION-CH2-VICIOUS-CIRCLE-PP39-40
CHAPTER II. THE THEORY OF LOGICAL TYPES.

THE theory of logical types, to be explained in the present Chapter,
recommended itself to us in the first instance by its ability to solve
certain contradictions, of which the one best known to mathematicians
is Burali-Forti's concerning the greatest ordinal. But the theory in
question is not wholly dependent upon this indirect recommendation:
it has also a certain consonance with common sense which makes it
inherently credible. In what follows, we shall therefore first set
forth the theory on its own account, and then apply it to the solution
of the contradictions.

I. The Vicious-Circle Principle.

An analysis of the paradoxes to be avoided shows that they all result
from a certain kind of vicious circle [12]. The vicious circles in
question arise from supposing that a collection of objects may contain
members which can only be defined by means of the collection as a
whole. Thus, for example, the collection of propositions will be
supposed to contain a proposition stating that "all propositions are
either true or false." It would seem, however, that such a statement
could not be legitimate unless "all propositions" referred to some
already definite collection, which it cannot do if new propositions are
created by statements about "all propositions." We shall, therefore,
have to say that statements about "all propositions" are meaningless.
More generally, given any set of objects such that, if we suppose the
set to have a total, it will contain members which presuppose this
total, then such a set cannot have a total. By saying that a set has
"no total," we mean, primarily, that no significant statement can be
made about "all its members." Propositions, as the above illustration
shows, must be a set having no total. The same is true, as we shall
shortly see, of propositional functions, even when these are restricted
to such as can significantly have as argument a given object a. In
such cases, it is necessary to break up our set into smaller sets, each
of which is capable of a total. This is what the theory of types aims
at effecting.

The principle which enables us to avoid illegitimate totalities may
be stated as follows: "Whatever involves all of a collection must not
be one of the collection"; or, conversely: "If, provided a certain
collection had a total, it would have members only definable in terms
of that total, then the said collection has no total." We shall call
this the "vicious-circle principle," because it enables us to avoid the
vicious circles involved in the assumption of illegitimate totalities.
Arguments which are condemned by the vicious-circle principle will
be called "vicious-circle fallacies." Such arguments, in certain
circumstances, may lead to contradictions, but it often happens that
the conclusions to which they lead are in fact true, though the
arguments are fallacious. Take, for example, the law of excluded
middle, in the form "all propositions are true or false." If from this
law we argue that, because the law of excluded middle is a proposition,
therefore the law of excluded middle is true or false, we incur a
vicious-circle fallacy. "All propositions" must be in some way limited
before it becomes a legitimate totality, and any limitation which makes
it legitimate must make any statement about the totality fall outside
the totality. Similarly, the imaginary sceptic, who asserts that he
knows nothing, and is refuted by being asked if he knows that he knows
nothing, has asserted nonsense, and has been fallaciously refuted by
an argument which involves a vicious-circle fallacy. In order that
the sceptic's assertion may become significant, it is necessary to
place some limitation upon the things of which he is asserting his
ignorance, because the things of which it is possible to be ignorant
form an illegitimate totality. But as soon as a suitable limitation has
been placed by him upon the collection of propositions of which he is
asserting his ignorance, the proposition that he is ignorant of every
member of this collection must not itself be one of the collection.
Hence any significant scepticism is not open to the above form of
refutation.

The paradoxes of symbolic logic concern various sorts of objects:
propositions, classes, cardinal and ordinal numbers, etc. All these
sorts of objects, as we shall show, represent illegitimate totalities,
and are therefore capable of giving rise to vicious-circle fallacies.
But by means of the theory (to be explained in Chapter III ) which
reduces statements that are verbally concerned with classes and
relations to statements that are concerned with propositional
functions, the paradoxes are reduced to such as are concerned with
propositions and propositional functions. The paradoxes that concern
propositions are only indirectly relevant to mathematics, while those
that more nearly concern the mathematician are all concerned with propositional functions. We shall therefore proceed at once to
the consideration of propositional functions.
PM-VERBATIM-END PM1:INTRODUCTION-CH2-VICIOUS-CIRCLE-PP39-40 -/

/- PM-FORMAL-GLOSS
The vicious-circle principle and illegitimate totalities are retained as source-critical prose; this block introduces no Lean universe, binder, or axiom.
-/

/- PM-VERBATIM-BEGIN PM1:INTRODUCTION-CH2-NATURE-FUNCTIONS-PP41-44A
II. The Nature of Propositional Functions.

By a "propositional function" we mean something which contains a
variable x, and expresses a proposition as soon as a value
is assigned to x. That is to say, it differs from a proposition
solely by the fact that it is ambiguous: it contains a variable of
which the value is unassigned. It agrees with the ordinary functions
of mathematics in the fact of containing an unassigned variable:
where it differs is in the fact that the values of the function are
propositions. Thus e.g. "x is a man" or "sin x = 1"
is a propositional function. We shall find that it is possible to
incur a vicious-circle fallacy at the very outset, by admitting as
possible arguments to a propositional function terms which presuppose
the function. This form of the fallacy is very instructive, and its
avoidance leads, as we shall see, to the hierarchy of types.

The question as to the nature of a function [13] is by no means an easy
one. It would seem, however, that the essential characteristic of a
function is ambiguity. Take, for example, the law of identity
in the form "A is A," which is the form in which it is usually
enunciated. It is plain that, regarded psychologically, we have here a
single judgment. But what are we to say of the object of the judgment?
We are not judging that Socrates is Socrates, nor that Plato is Plato,
nor any other of the definite judgments that are instances of the law
of identity. Yet each of these judgments is, in a sense, within the
scope of our judgment. We are in fact judging an ambiguous instance of
the propositional function "A is A." We appear to have a single
thought which does not have a definite object, but has as its object
an undetermined one of the values of the function "A is A." It
is this kind of ambiguity that constitutes the essence of a function.
When we speak of "φx" where x is not specified, we mean one
value of the function, but not a definite one. We may express this by
saying that "φx" ambiguously denotes φa, φb,
φc, etc., where φa, φb, φc, etc.,
are the various values of "φx."

When we say that "φx" ambiguously denotes φa, φb,
φc, etc., we mean that "φx" means one of the
objects φa, φb, φc, etc., though not a definite
one, but an undetermined one. It follows that "φx" only has a
well-defined meaning (well-defined, that is to say, except in so far as
it is of its essence to be ambiguous) if the objects φa, φb,
φc, etc., are well-defined. That is to say, a function
is not a well-defined function unless all its values are already
well-defined. It follows from this that no function can have among
its values anything which presupposes the function, for if it had,
we could not regard the objects ambiguously denoted by the function
as definite until the function was definite, while conversely, as we
have just seen, the function cannot be definite until its values are
definite. This is a particular case, but perhaps the most fundamental
case, of the vicious-circle principle. A function is what ambiguously
denotes some one of a certain totality, namely the values of the
function; hence this totality cannot contain any members which involve
the function, since, if it did, it would contain members involving the
totality, which, by the vicious-circle principle, no totality can do.

It will be seen that, according to the above account, the values
of a function are presupposed by the function, not vice versa. It
is sufficiently obvious, in any particular case, that a value of
a function does not presuppose the function. Thus for example the
proposition "Socrates is human" can be perfectly apprehended without
regarding it as a value of the function "x is human." It is true
that, conversely, a function can be apprehended without its being
necessary to apprehend its values severally and individually. If this
were not the case, no function could be apprehended at all, since
the number of values (true and false) of a function is necessarily
infinite and there are necessarily possible arguments with which we are
unacquainted. What is necessary is not that the values should be given
individually and extensionally, but that the totality of the values
should be given intensionally, so that, concerning any assigned object,
it is at least theoretically determinate whether or not the said object
is a value of the function.

It is necessary practically to distinguish the function itself from
an undetermined value of the function. We may regard the function
itself as that which ambiguously denotes, while an undetermined
value of the function is that which is ambiguously denoted. If the
undetermined value is written "φx," we will write the function
itself "φx̂." (Any other letter may be used in place of
x.) Thus we should say "φx is a proposition," but "φx̂
is a propositional function." When we say "φx is
a proposition," we mean to state something which is true for every
possible value of x, though we do not decide what value x is
to have. We are making an ambiguous statement about any value of the
function. But when we say "φx̂ is a function," we are not
making an ambiguous statement. It would be more correct to say that
we are making a statement about an ambiguity, taking the view that a
function is an ambiguity. The function itself, φx̂, is the
single thing which ambiguously denotes its many values; while φx,
where x is not specified, is one of the denoted objects, with
the ambiguity belonging to the manner of denoting.

We have seen that, in accordance with the vicious-circle principle, the
values of a function cannot contain terms only definable in terms of
the function. Now given a function φx̂, the values for the
function [14] are all propositions of the form φx. It follows
that there must be no propositions, of the form φx, in which
x has a value which involves φx̂. (If this were the
case, the values of the function would not all be determinate until
the function was determinate, whereas we found that the function is
not determinate unless its values are previously determinate.) Hence
there must be no such thing as the value for φx̂ with the
argument φx̂, or with any argument which involves φx̂.
That is to say, the symbol "φ(φx̂)" must not express a
proposition, as "φa" does if φa is a value for φx̂.
In fact "φ(φx̂)" must be a symbol which does
not express anything: we may therefore say that it is not significant.
Thus given any function φx̂, there are arguments with
which the function has no value, as well as arguments with which it has
a value. We will call the arguments with which φx̂ has a
value "possible values of x." We will say that φx̂ is
"significant with the argument x" when φx̂ has a value
with the argument x.

When it is said that e.g. "φ(φẑ)" is
meaningless, and therefore neither true nor false, it is necessary to
avoid a misunderstanding. If "φ(φẑ)" were interpreted
as meaning "the value for φẑ with the argument φẑ
is true," that would be not meaningless, but false. It is
false for the same reason for which "the King of France is bald"
is false, namely because there is no such thing as "the value for
φẑ with the argument φẑ." But when, with
some argument a, we assert φa, we are not meaning to assert
"the value for φx̂ with the argument a is true"; we are
meaning to assert the actual proposition which is the value for φx̂
with the argument a. Thus for example if φx̂
is "x̂ is a man," φ (Socrates) will be "Socrates is a
man," not "the value for the function 'x̂ is a man,'
with the argument Socrates, is true." Thus in accordance with our
principle that "φ(φẑ)" is meaningless, we cannot
legitimately deny "the function 'x̂ is a man' is a man,"
because this is nonsense, but we can legitimately deny "the value for
the function 'x̂ is a man' with the argument 'x̂ is a
man' is true," not on the ground that the value in question is false,
but on the ground that there is no such value for the function.

We will denote by the symbol "(x).φx" the proposition "φx
always [15]," i.e. the proposition which asserts all the
values for φx̂. This proposition involves the function
φx̂, not merely an ambiguous value of the function. The
assertion of φx, where x is unspecified, is a different
assertion from the one which asserts all values for φx̂,
for the former is an ambiguous assertion, whereas the latter is in no
sense ambiguous. It will be observed that "(x) . φx" does not
assert "φx with all values of x," because, as we have seen,
there must be values of x with which "φx" is meaningless.
What is asserted by "(x) . φx" is all propositions which are
values for φx̂; hence it is only with such values of x as
make "φx" significant, i.e. with all possible arguments,
that φx is asserted when we assert "(x) . φx." Thus
a convenient way to read "(x) . φx" is "φx is true
with all possible values of x." This is, however, a less accurate
reading than "φx always," because the notion of truth is not
part of the content of what is judged. When we judge "all men are
mortal," we judge truly, but the notion of truth is not necessarily in
our minds, any more than it need be when we judge "Socrates is mortal."
PM-VERBATIM-END PM1:INTRODUCTION-CH2-NATURE-FUNCTIONS-PP41-44A -/

/- PM-FORMAL-GLOSS
The distinction between φx and φx̂ is documentary here. It does not change the project’s kernel syntax or binders.
-/

/- PM-VERBATIM-BEGIN PM1:INTRODUCTION-CH2-TRUTH-FALSEHOOD-PP44B-46
III. Definition and Systematic Ambiguity of Truth and Falsehood.

Since "(x) . φx" involves the function φx̂, it
must, according to our principle, be impossible as an argument to
φ. That is to say, the symbol "φ {(x) . φx}" must
be meaningless. This principle would seem, at first sight, to have
certain exceptions. Take, for example, the function "p̂ is
false," and consider the proposition "(p) . p is false." This
should be a proposition asserting all propositions of the form "p
is false." Such a proposition, we should be inclined to say, must be
false, because "p is false" is not always true. Hence we should be
led to the proposition

“{(p) . p is false} is false,”
i.e. we should be led to a proposition in which "(p) . p is
false" is the argument to the function "p̂ is false," which
we had declared to be impossible. Now it will be seen that "(p) .p
is false," in the above, purports to be a proposition about all
propositions, and that, by the general form of the vicious-circle
principle, there must be no propositions about all propositions.
Nevertheless, it seems plain that, given any function, there is a
proposition (true or false) asserting all its values. Hence we are led
to the conclusion that "p is false" and "q is false" must not
always be the values, with the arguments p and q, for a single
function "p̂ is false." This, however, is only possible if
the word "false" really has many different meanings, appropriate to
propositions of different kinds.

That the words "true" and "false" have many different meanings,
according to the kind of proposition to which they are applied, is
not difficult to see. Let us take any function φx̂, and let
φa be one of its values. Let us call the sort of truth which is
applicable to φa "first truth." (This is not to assume
that this would be first truth in another context: it is merely to
indicate that it is the first sort of truth in our context.) Consider
now the proposition (x) . φx. If this has truth of the sort
appropriate to it, that will mean that every value φx has
"first truth." Thus if we call the sort of truth that is appropriate to
(x) . φx "second truth," we may define "{(x) . φx}
has second truth" as meaning "every value for φx̂
has first truth," i.e. "(x).(φx has first truth)."
Similarly, if we denote by "(∃ x) . φx" the proposition
"φx sometimes," i.e. as we may less accurately
express it, "φx with some value of x," we find that
(∃ x) . φx has second truth if there is an x with which φx has first truth; thus we may define "{(∃ x).φx}
has second truth" as meaning "some value for φx̂ has first
truth," i.e. "(∃ x) . (φx has first truth)."
Similar remarks apply to falsehood. Thus "{(x).φx} has
second falsehood" will mean "some value for φx̂ has first
falsehood," i.e. "(∃ x) . (φx has first falsehood),"
while "{(∃ x).φx} has second falsehood"
will mean "all values for φx̂ have first falsehood," i.e. "(x). (φx has first falsehood)." Thus the
sort of falsehood that can belong to a general proposition is different
from the sort that can belong to a particular proposition.

Applying these considerations to the proposition "(p).p is false,"
we see that the kind of falsehood in question must be specified.
If, for example, first falsehood is meant, the function "p̂
has first falsehood" is only significant when p is the sort of
proposition which has first falsehood or first truth. Hence "(p) . p
is false" will be replaced by a statement which is equivalent to
"all propositions having either first truth or first falsehood have
first falsehood." This proposition has second falsehood, and is
not a possible argument to the function "p̂ has first falsehood." Thus the apparent exception to the principle that
"φ{(x) . φx}" must be meaningless disappears.

Similar considerations will enable us to deal with "not-p" and with
"p or q." It might seem as if these were functions in which any proposition might appear as argument. But this is due to a
systematic ambiguity in the meanings of "not" and "or," by which they
adapt themselves to propositions of any order. To explain fully how
this occurs, it will be well to begin with a definition of the simplest
kind of truth and falsehood.

The universe consists of objects having various qualities and standing
in various relations. Some of the objects which occur in the universe
are complex. When an object is complex, it consists of interrelated
parts. Let us consider a complex object composed of two parts a
and b standing to each other in the relation R. The complex
object "a-in-the-relation-R-to-b" may be capable of being perceived; when perceived, it is perceived as one object.
Attention may show that it is complex; we then judge that
a and b stand in the relation R. Such a judgment, being
derived from perception by mere attention, may be called a "judgment
of perception." This judgment of perception, considered as an actual
occurrence, is a relation of four terms, namely a and b and
R and the percipient. The perception, on the contrary, is a
relation of two terms, namely "a-in-the-relation-R-to-b,"
and the percipient. Since an object of perception cannot be nothing,
we cannot perceive "a-in-the-relation-R-to-b" unless a
is in the relation R to b. Hence a judgment of perception,
according to the above definition, must be true. This does not
mean that, in a judgment which appears to us to be one of
perception, we are sure of not being in error, since we may err in
thinking that our judgment has really been derived merely by analysis
of what was perceived. But if our judgment has been so derived,
it must be true. In fact, we may define truth, where such
judgments are concerned, as consisting in the fact that there is a
complex corresponding to the discursive thought which is the
judgment. That is, when we judge "a has the relation R to
b," our judgment is said to be true when there is a complex
"a-in-the-relation-R-to-b," and is said to be false when this is not the case. This is a definition of truth and falsehood
in relation to judgments of this kind.

It will be seen that, according to the above account, a judgment does
not have a single object, namely the proposition, but has several
interrelated objects. That is to say, the relation which constitutes
judgment is not a relation of two terms, namely the judging mind
and the proposition, but is a relation of several terms, namely the
mind and what are called the constituents of the proposition. That
is, when we judge (say) "this is red," what occurs is a relation of
three terms, the mind, and "this," and red. On the other hand, when
we perceive "the redness of this," there is a relation of two
terms, namely the mind and the complex object "the redness of this."
When a judgment occurs, there is a certain complex entity, composed of
the mind and the various objects of the judgment. When the judgment
is true , in the case of the kind of judgments we have been
considering, there is a corresponding complex of the objects of the judgment alone. Falsehood, in regard to our present class
of judgments, consists in the absence of a corresponding complex
composed of the objects alone. It follows from the above theory that
a "proposition," in the sense in which a proposition is supposed to
be the object of a judgment, is a false abstraction, because a
judgment has several objects, not one. It is the severalness of the
objects in judgment (as opposed to perception) which has led people to
speak of thought as "discursive," though they do not appear to have
realized clearly what was meant by this epithet.

Owing to the plurality of the objects of a single judgment, it follows
that what we call a "proposition" (in the sense in which this is
distinguished from the phrase expressing it) is not a single entity at
all. That is to say, the phrase which expresses a proposition is what
we call an "incomplete" symbol [16] ; it does not have meaning in itself,
but requires some supplementation in order to acquire a complete
meaning. This fact is somewhat concealed by the circumstance that
judgment in itself supplies a sufficient supplement, and that judgment
in itself makes no verbal addition to the proposition. Thus "the
proposition 'Socrates is human'" uses "Socrates is human" in a way
which requires a supplement of some kind before it acquires a complete
meaning; but when I judge "Socrates is human," the meaning is completed
by the act of judging, and we no longer have an incomplete symbol.
The fact that propositions are "incomplete symbols"
PM-VERBATIM-END PM1:INTRODUCTION-CH2-TRUTH-FALSEHOOD-PP44B-46 -/

/- PM-FORMAL-GLOSS
The hierarchy of truth and falsehood is recorded without being promoted to axioms or declarations.
-/

/- PM-VERBATIM-BEGIN PM1:INTRODUCTION-CH2-GENERAL-JUDGMENTS-PP47-48
is important
philosophically, and is relevant at certain points in symbolic logic.

The judgments we have been dealing with hitherto are such as are of the
same form as judgments of perception, i.e. their subjects are
always particular and definite. But there are many judgments which are
not of this form. Such are "all men are mortal," "I met a man," "some
men are Greeks." Before dealing with such judgments, we will introduce
some technical terms.

We will give the name of "a complex " to any such object as
"a in the relation R to b" or "a having the quality
q," or "a and b and c standing in the relation S."
Broadly speaking, a complex is anything which occurs in the
universe and is not simple. We will call a judgment elementary when it merely asserts such things as "a has the relation R to
b," "a has the quality q" or "a and b and c
stand in the relation S." Then an elementary judgment is
true when there is a corresponding complex, and false when there is no
corresponding complex.

But take now such a proposition as "all men are mortal." Here the
judgment does not correspond to one complex, but to many,
namely "Socrates is mortal," "Plato is mortal," "Aristotle is mortal,"
etc. (For the moment, it is unnecessary to inquire whether each of
these does not require further treatment before we reach the ultimate
complexes involved. For purposes of illustration, "Socrates is mortal"
is here treated as an elementary judgment, though it is in fact not
one, as will be explained later. Truly elementary judgments are not
very easily found.) We do not mean to deny that there may be some
relation of the concept man to the concept mortal which
may be equivalent to "all men are mortal," but in any case this
relation is not the same thing as what we affirm when we say that all
men are mortal. Our judgment that all men are mortal collects together
a number of elementary judgments. It is not, however, composed of
these, since ( e.g. ) the fact that Socrates is mortal is no
part of what we assert, as may be seen by considering the fact that
our assertion can be understood by a person who has never heard of
Socrates. In order to understand the judgment "all men are mortal," it
is not necessary to know what men there are. We must admit, therefore,
as a radically new kind of judgment, such general assertions as "all
men are mortal." We assert that, given that x is human, x is
always mortal. That is, we assert "x is mortal" of every x which is human. Thus we are able to judge (whether truly
or falsely) that all the objects which have some assigned
property also have some other assigned property. That is, given any
propositional functions φx̂ and ψx̂, there
is a judgment asserting ψx with every x for which we have
φx. Such judgments we will call general judgments .

It is evident (as explained above) that the definition of truth is different in the case of general judgments from what it was in the
case of elementary judgments. Let us call the meaning of truth which we gave for elementary judgments "elementary truth." Then when
we assert that it is true that all men are mortal, we shall mean that
all judgments of the form "x is mortal," where x is a man, have
elementary truth. We may define this as "truth of the second order" or
"second-order truth." Then if we express the proposition "all men are
mortal" in the form

“(x). x is mortal, where x is a man.”

and call this judgment p, then "p is true" must be taken to
mean "p has second-order truth," which in turn means

“(x). ‘x is mortal’ has elementary truth, where x is a man.”

In order to avoid the necessity for stating explicitly the limitation
to which our variable is subject, it is convenient to replace the
above interpretation of "all men are mortal" by a slightly different
interpretation. The proposition "all men are mortal" is equivalent to
"'x is a man' implies 'x is mortal,' with all possible values
of x." Here x is not restricted to such values as are men,
but may have any value with which "'x is a man' implies 'x is
mortal'" is significant , i.e. either true or false. Such
a proposition is called a "formal implication." The advantage of this
form is that the values which the variable may take are given by the
function to which it is the argument: the values which the variable may
take are all those with which the function is significant.

We use the symbol "(x).φx" to express the general judgment
which asserts all judgments of the form "φx." Then the judgment
"all men are mortal" is equivalent to

“(x). ‘x is a man’ implies ‘x is a mortal,’”
i.e. (in virtue of the definition of implication) to

“(x) . x is not a man or x is mortal.”

As we have just seen, the meaning of truth which is applicable
to this proposition is not the same as the meaning of truth which is applicable to "x is a man" or to "x is mortal." And
generally, in any judgment (x) . φx, the sense in which this
judgment is or may be true is not the same as that in which φx
is or may be true. If φx is an elementary judgment, it is true
when it points to a corresponding complex. But (x) . φx
does not point to a single corresponding complex: the corresponding
complexes are as numerous as the possible values of x.

It follows from the above that such a proposition as "all the judgments
made by Epimenides are true" will only be prima facie capable of truth
if all his judgments are of the same order. If they are of varying
orders, of which the nth is the highest, we may make n assertions of
the form "all the judgments of order m made by Epimenides are
true," where m has all values
PM-VERBATIM-END PM1:INTRODUCTION-CH2-GENERAL-JUDGMENTS-PP47-48 -/

/- PM-FORMAL-GLOSS
Elementary and general judgments, including formal implication, remain documentary pending an explicit audited semantic model.
-/

/- PM-VERBATIM-BEGIN PM1:INTRODUCTION-CH2-SYSTEMATIC-AMBIGUITY-PP49-50A
up to n. But no such judgment
can include itself in its own scope, since such a judgment is always of
higher order than the judgments to which it refers.

Let us consider next what is meant by the negation of a proposition
of the form "(x) · φx." We observe, to begin with,
that "φx in some cases," or "φx sometimes," is
a judgment which is on a par with "φx in all cases," or
"φx always." The judgment "φx sometimes" is true if
one or more values of x exist for which φx is true. We
will express the proposition "φx sometimes" by the notation
"(∃ x) · φx," where "∃" stands for "there
exists," and the whole symbol may be read "there exists an x
such that φx." We take the two kinds of judgment expressed
by "(x) · φx" and "(∃ x) · φx" as
primitive ideas. We also take as a primitive idea the negation of an elementary proposition. We can then define the negations of
(x) · φx and (∃ x) · φx. The negation
of any proposition p will be denoted by the symbol "∼p."
Then the negation of (x) · φx will be defined as
meaning

“(∃ x) · ∼φx,”

and the negation of (∃ x) · φx will be defined as meaning "(x) · ∼φx." Thus, in
the traditional language of formal logic, the negation of a universal
affirmative is to be defined as the particular negative, and the
negation of the particular affirmative is to be defined as the
universal negative. Hence the meaning of negation for such propositions
is different from the meaning of negation for elementary propositions.

An analogous explanation will apply to disjunction. Consider the
statement "either p, or φx always." We will denote the
disjunction of two propositions p, q by "p ∨ q." Then
our statement is "p · ∨ · (x) · φx." We will
suppose that p is an elementary proposition, and that φx
is always an elementary proposition. We take the disjunction of
two elementary propositions as a primitive idea, and we wish to define the disjunction

“p · ∨ · (x) · φx.”

This may be defined as "(x) · p ∨ φx," i.e. "either p is true, or φx is always true" is to mean
"'p or φx' is always true." Similarly we will define

“p · ∨ · (∃ x) · φx”

as meaning "(∃ x) · p ∨ φx," i.e. we
define "either p is true or there is an x for which φx
is true" as meaning "there is an x for which either p or
φx is true." Similarly we can define a disjunction of two
universal propositions: "(x) · φx · ∨ · (y)· ψy"
will be defined as meaning "(x, y) · φx ∨ ψy," i.e. "either φx is always true or
ψy is always true" is to mean "'φx or ψy'
is always true." By this method we obtain definitions of disjunctions
containing propositions of the form (x) · φx or
(∃ x) · φx in terms of disjunctions of elementary
propositions; but the meaning of "disjunction" is not the same for
propositions of the forms (x) . φx, (∃ x). φx,
as it was for elementary propositions.

Similar explanations could be given for implication and conjunction,
but this is unnecessary, since these can be defined in terms of
negation and disjunction.
PM-VERBATIM-END PM1:INTRODUCTION-CH2-SYSTEMATIC-AMBIGUITY-PP49-50A -/

/- PM-FORMAL-GLOSS
The order-sensitive negation and disjunction clauses are source text, not new overloaded Lean operators.
-/

/- PM-VERBATIM-BEGIN PM1:INTRODUCTION-CH2-TYPE-ARGUMENTS-P50B
IV. Why a Given Function requires Arguments of a Certain Type.

The considerations so far adduced in favour of the view that a
function cannot significantly have as argument anything defined in
terms of the function itself have been more or less indirect. But a
direct consideration of the kinds of functions which have functions
as arguments and the kinds of functions which have arguments other
than functions will show, if we are not mistaken, that not only
is it impossible for a function φẑ to have itself or
anything derived from it as argument, but that, if ψẑ is
another function such that there are arguments a with which both
"φa" and "ψa" are significant, then ψẑ
and anything derived from it cannot significantly be argument to
φẑ. This arises from the fact that a function is
essentially an ambiguity, and that, if it is to occur in a definite
proposition, it must occur in such a way that the ambiguity has
disappeared, and a wholly unambiguous statement has resulted. A few
illustrations will make this clear. Thus "(x) . φx," which we
have already considered, is a function of φx̂; as soon as
φx̂ is assigned, we have a definite proposition, wholly
free from ambiguity. But it is obvious that we cannot substitute for
the function something which is not a function: "(x) . φx"
means "φx in all cases," and depends for its significance
upon the fact that there are "cases" of φx, i.e. upon
the ambiguity which is characteristic of a function. This instance
illustrates the fact that, when a function can occur significantly as
argument, something which is not a function cannot occur significantly
as argument. But conversely, when something which is not a function can
occur significantly as argument, a function cannot occur significantly.
Take, e.g. "x is a man," and consider "φx̂
is a man." Here there is nothing to eliminate the ambiguity which
constitutes φx̂; there is thus nothing definite which
is said to be a man. A function, in fact, is not a definite object,
which could be or not be a man; it is a mere ambiguity awaiting
determination, and in order that it may occur significantly it must
receive the necessary determination, which it obviously does not
receive if it is merely substituted for something determinate in a
proposition [17]. This argument does not, however, apply directly as
against such a statement as "{(x) . φx} is a man." Common
sense would pronounce such a statement to be meaningless, but it
cannot be condemned on the ground of ambiguity in its subject. We
need
PM-VERBATIM-END PM1:INTRODUCTION-CH2-TYPE-ARGUMENTS-P50B -/

/- PM-FORMAL-GLOSS
This deliberately incomplete source fragment ends with printed page 50 and introduces no type-theoretic declaration.
-/

/- PM-VERBATIM-BEGIN PM1:INTRODUCTION-CH2-NOTE-12
See the last section of the present Chapter. Cf. also H.
Poincaré, "Les mathématiques et la logique," Revue de Métaphysique
et de Morale, Mai 1906, p. 307.
PM-VERBATIM-END PM1:INTRODUCTION-CH2-NOTE-12 -/

/- PM-VERBATIM-BEGIN PM1:INTRODUCTION-CH2-NOTE-13
When the word "function" is used in the sequel,
"propositional function" is always meant. Other functions will not be
in question in the present Chapter.
PM-VERBATIM-END PM1:INTRODUCTION-CH2-NOTE-13 -/

/- PM-VERBATIM-BEGIN PM1:INTRODUCTION-CH2-NOTE-14
We shall speak in this Chapter of "values for φx̂"
and of "values of φx," meaning in each case the same
thing, namely φa, φb, φc, etc. The distinction
of phraseology serves to avoid ambiguity where several variables are
concerned, especially when one of them is a function.
PM-VERBATIM-END PM1:INTRODUCTION-CH2-NOTE-14 -/

/- PM-VERBATIM-BEGIN PM1:INTRODUCTION-CH2-NOTE-15
We use "always" as meaning "in all cases," not "at all
times." Similarly "sometimes" will mean "in some cases."
PM-VERBATIM-END PM1:INTRODUCTION-CH2-NOTE-15 -/

/- PM-VERBATIM-BEGIN PM1:INTRODUCTION-CH2-NOTE-16
See Chapter III.
PM-VERBATIM-END PM1:INTRODUCTION-CH2-NOTE-16 -/

/- PM-VERBATIM-BEGIN PM1:INTRODUCTION-CH2-NOTE-17
Note that statements concerning the significance of
a phrase containing "φẑ" concern the symbol "φẑ," and therefore do not fall under the rule that the
elimination of the functional ambiguity is necessary to significance.
Significance is a property of signs. Cf. p. 43.
PM-VERBATIM-END PM1:INTRODUCTION-CH2-NOTE-17 -/

/- PM-EDITORIAL
No sic marker is required in this range. The scan is canonical. Project
Gutenberg’s omissions of φ on printed page 44 and ∼ on printed page 49 are
digital-witness errors and remain outside the canonical bytes.
-/

end PM.FirstEdition.Volume1.Introduction.Chapter2
