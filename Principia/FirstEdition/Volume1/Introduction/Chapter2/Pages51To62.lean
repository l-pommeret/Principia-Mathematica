namespace PM.FirstEdition.Volume1.Introduction.Chapter2

/-! # Chapter II, pages 51–62

Canonical edition: first edition, volume I (1910), pp. 51–62, scan leaves
73–84. This scan-collated verbal-diplomatic reflow continues section IV,
contains sections V and VI, and opens section VII. Page-local notes 18–22
are independent canonical blocks. No printed Errata entry concerns this
range; five errors of digital witnesses are confined to the apparatus.
-/

/- PM-VERBATIM-BEGIN PM1:INTRODUCTION-CH2-TYPE-ARGUMENTS-CONCLUSION-P51A
here a new objection, namely the following: A proposition is
not a single entity, but a relation of several; hence a statement in
which a proposition appears as subject will only be significant if
it can be reduced to a statement about the terms which appear in the
proposition. A proposition, like such phrases as "the so-and-so,"
where grammatically it appears as subject, must be broken up into its
constituents if we are to find the true subject or subjects [18]. But
in such a statement as "p is a man," where p is a proposition,
this is not possible. Hence "{(x) · φx} is a man" is
meaningless.
PM-VERBATIM-END PM1:INTRODUCTION-CH2-TYPE-ARGUMENTS-CONCLUSION-P51A -/

/- PM-FORMAL-GLOSS
This conclusion of section IV is documentary and completes the fragment begun on page 50.
-/

/- PM-VERBATIM-BEGIN PM1:INTRODUCTION-CH2-FUNCTION-HIERARCHY-PP51B-52
V. The Hierarchy of Functions and Propositions.

We are thus led to the conclusion, both from the vicious-circle
principle and from direct inspection, that the functions to which
a given object a can be an argument are incapable of being
arguments to each other, and that they have no term in common with the
functions to which they can be arguments. We are thus led to construct
a hierarchy. Beginning with a and the other terms which can be
arguments to the same functions to which a can be argument, we come
next to functions to which a is a possible argument, and then to
functions to which such functions are possible arguments, and so on.
But the hierarchy which has to be constructed is not so simple as might
at first appear. The functions which can take a as argument form an
illegitimate totality, and themselves require division into a hierarchy
of functions. This is easily seen as follows. Let f(φẑ, x)
be a function of the two variables φẑ and x. Then if,
keeping x fixed for the moment, we assert this with all possible
values of φ, we obtain a proposition:

(φ) · f(φẑ, x).

Here, if x is variable, we have a function of x; but as this
function involves a totality of values of φẑ [19], it
cannot itself be one of the values included in the totality, by the
vicious-circle principle. It follows that the totality of values of
φẑ concerned in (φ) · f(φẑ, x) is not
the totality of all functions in which x can occur as argument, and
that there is no such totality as that of all functions in which x
can occur as argument.

It follows from the above that a function in which φẑ
appears as argument requires that "φẑ" should not stand
for any function which is capable of a given argument, but
must be restricted in such a way that none of the functions which are
possible values of "φẑ" should involve any reference to
the totality of such functions. Let us take as an illustration the
definition of identity. We might attempt to define "x is identical
with y" as meaning "whatever is true of x is true of y," i.e. "φx always implies φy." But here, since we
are concerned to assert all values of "φx implies φy"
regarded as a function of φ, we shall be compelled to impose
upon φ some limitation which will prevent us from including
among values of φ values in which "all possible values of
φ" are referred to. Thus for example "x is identical with
a" is a function of x; hence, if it is a legitimate value of
φ in "φx always implies φy" we shall be able to
infer, by means of the above definition, that if x is identical
with a, and x is identical with y, then y is identical
with a. Although the conclusion is sound, the reasoning embodies
a vicious-circle fallacy, since we have taken "(φ)·φx
implies φa" as a possible value of φx, which it cannot
be. If, however, we impose any limitation upon φ, it may happen,
so far as appears at present, that with other values of φ we
might have φx true and φy false, so that our proposed
definition of identity would plainly be wrong. This difficulty is
avoided by the "axiom of reducibility," to be explained later. For the
present, it is only mentioned in order to illustrate the necessity and
the relevance of the hierarchy of functions of a given argument.

Let us give the name "a-functions" to functions that are
significant for a given argument a. Then suppose we take any
selection of a-functions, and consider the proposition "a
satisfies all the functions belonging to the selection in question."
If we here replace a by a variable, we obtain an a-function;
but by the vicious-circle principle this a-function cannot be a
member of our selection, since it refers to the whole of the selection.
Let the selection consist of all those functions which satisfy
f(φẑ). Then our new function is

(φ) · {f(φẑ) implies φx},

where x is the argument. It thus appears that, whatever selection
of a-functions we may make, there will be other a-functions
that lie outside our selection. Such a-functions, as the above
instance illustrates, will always arise through taking a function of
two arguments, φẑ and x, and asserting all or some
of the values resulting from varying φ. What is necessary,
therefore, in order to avoid vicious-circle fallacies, is to divide our
a-functions into "types," each of which contains no functions which
refer to the whole of that type.

When something is asserted or denied about all possible values or
about some (undetermined) possible values of a variable, that variable
is called apparent, after Peano. The presence of the words all or some in a proposition indicates the presence of
an apparent variable; but often an apparent variable is really present
where language does not at once indicate its presence. Thus for example
"A is mortal" means "there is a time at which A will die." Thus
a variable time occurs as apparent variable.

The clearest instances of propositions not containing apparent
variables are such as express immediate judgments of perception, such
as "this is red" or "this is painful," where "this" is something
immediately given. In other
PM-VERBATIM-END PM1:INTRODUCTION-CH2-FUNCTION-HIERARCHY-PP51B-52 -/

/- PM-FORMAL-GLOSS
The hierarchy and its restrictions are historical source text; no Lean universe or binder is introduced.
-/

/- PM-VERBATIM-BEGIN PM1:INTRODUCTION-CH2-MATRICES-FIRST-ORDER-PP53-54
judgments, even where at first sight no
variable appears to be present, it often happens that there really is
one. Take (say) "Socrates is human." To Socrates himself, the word
"Socrates" no doubt stood for an object of which he was immediately
aware, and the judgment "Socrates is human" contained no apparent
variable. But to us, who only know Socrates by description, the
word "Socrates" cannot mean what it meant to him; it means rather
"the person having such-and-such properties," (say) "the Athenian
philosopher who drank the hemlock." Now in all propositions about "the
so-and-so" there is an apparent variable, as will be shown in Chapter III .
Thus in what we have in mind when we say "Socrates is
human" there is an apparent variable, though there was no apparent
variable in the corresponding judgment as made by Socrates, provided we
assume that there is such a thing as immediate awareness of oneself.

Whatever may be the instances of propositions not containing apparent
variables, it is obvious that propositional functions whose values do not
contain apparent variables are the source of propositions containing apparent
variables, in the sense in which the function φx̂ is the source of the proposition
(x) · φx. For the values for φx̂ do not contain the apparent variable x,
which appears in (x) · φx; if they contain an apparent variable y, this can be
similarly eliminated, and so on. This process must come to an end, since no
proposition which we can apprehend can contain more than a finite number
of apparent variables, on the ground that whatever we can apprehend must
be of finite complexity. Thus we must arrive at last at a function of as
many variables as there have been stages in reaching it from our original
proposition, and this function will be such that its values contain no apparent
variables. We may call this function the matrix of our original proposition
and of any other propositions and functions to be obtained by turning some
of the arguments to the function into apparent variables. Thus for example,
if we have a matrix-function whose values are φ(x, y), we shall derive from it

(y) · φ(x, y), which is a function of x,

(x) · φ(x, y), which is a function of y,

(x,y) · φ(x, y), meaning "φ(x, y) is true with
all possible values of x and y." This last is a proposition
containing no real variable, i.e. no variable except
apparent variables.

It is thus plain that all possible propositions and functions are
obtainable from matrices by the process of turning the arguments to the
matrices into apparent variables. In order to divide our propositions
and functions into types, we shall, therefore, start from matrices,
and consider how they are to be divided with a view to the avoidance
of vicious-circle fallacies in the definitions of the functions
concerned. For this purpose, we will use such letters as a,
b, c, x, y, z, w, to denote objects which
are neither propositions nor functions. Such objects we shall call individuals. Such objects will be constituents of propositions
or functions, and will be genuine constituents, in the sense
that they do not disappear on analysis, as (for example) classes do, or
phrases of the form "the so-and-so."

The first matrices that occur are those whose values are of the forms

φx, ψ(x, y), χ(x, y, z …),
i.e. where the arguments, however many there may be, are
all individuals. The functions φ, ψ, χ ...,
since (by definition) they contain no apparent variables, and have
no arguments except individuals, do not presuppose any totality of
functions. From the functions ψ, χ ... we may proceed
to form other functions of x, such as (y) . ψ(x, y),
(∃ y) . ψ(x, y), (y, z) . χ(x, y, z), (y) :
(∃ z) . χ(x, y, z), and so on. All these presuppose no
totality except that of individuals. We thus arrive at a certain
collection of functions of x, characterized by the fact that they
involve no variables except individuals. Such functions we will call
"first-order functions."

We may now introduce a notation to express "any first-order function."
We will denote any first-order function by "φ ! x̂" and
any value for such a function by "φ ! x." Thus "φ! x"
stands for any value for any function which involves no
variables except individuals. It will be seen that "φ ! x̂"
is itself a function of two variables, namely φ ! ẑ and
x. Thus φ ! x̂ involves a variable which is not an
individual, namely φ ! ẑ. Similarly "(x). φ ! x"
is a function of the variable φ ! ẑ, and thus involves
a variable other than an individual. Again, if a is a given
individual,

“φ ! x implies φ ! a with all possible values of φ.”

is a function of x, but it is not a function of the form φ !x,
because it involves an (apparent) variable φ which is not
an individual. Let us give the name "predicate" to any first-order
function φ ! x̂ (This use of the word "predicate" is
only proposed for the purposes of the present discussion.) Then the
statement "φ ! x implies φ ! a with all possible values
of φ" may be read "all the predicates of x are predicates of
a." This makes a statement about x, but does not attribute to
x a predicate in the special sense just defined.

Owing to the introduction of the variable first-order function φ! ẑ,
we now have a new set of matrices. Thus "φ ! x" is
a function which contains no apparent variables, but contains the two
real variables φ ! ẑ and x. (It should be observed
that when φ is assigned, we may obtain a function whose values
do involve individuals as apparent variables, for example if φ! x
is (y) . ψ(x, y). But so long as φ is variable,
φ ! x contains no apparent variables.) Again, if a is a
definite individual, φ ! a is a function of the one variable
φ ! ẑ. If a and b are definite individuals,
"φ ! a implies ψ ! b" is a function of the two variables
φ ! ẑ, ψ ! ẑ, and so on. We are thus led to a
whole set of new matrices,

f(φ ! ẑ), g(φ ! ẑ, ψ ! ẑ), F(φ ! ẑ, x), and so on.

These matrices contain individuals and first-order functions as
arguments, but
PM-VERBATIM-END PM1:INTRODUCTION-CH2-MATRICES-FIRST-ORDER-PP53-54 -/

/- PM-FORMAL-GLOSS
Matrices, individuals, first-order functions, and predicates are recorded without kernel declarations.
-/

/- PM-VERBATIM-BEGIN PM1:INTRODUCTION-CH2-HIGHER-ORDER-PREDICATIVE-PP55-56
(like all matrices) they contain no apparent variables.
Any such matrix, if it contains more than one variable, gives rise to
new functions of one variable by turning all its arguments except one
into apparent variables. Thus we obtain the functions

(φ).g(φ!ẑ,ψ!ẑ), which is a function of ψ!ẑ.

(x).F(φ!ẑ, x), which is a function of φ!ẑ.

(φ).F(φ!ẑ, x), which is a function of x.

We will give the name of second-order matrices to such matrices
as have first-order functions among their arguments, and have no
arguments except first-order functions and individuals. (It is not necessary that they should have individuals among their
arguments.) We will give the name of second-order functions to such as either are second-order matrices or are derived from such
matrices by turning some of the arguments into apparent variables. It
will be seen that either an individual or a first-order function may
appear as argument to a second-order function. Second-order functions
are such as contain variables which are first-order functions, but
contain no other variables except (possibly) individuals.

We now have various new classes of functions at our command. In the
first place, we have second-order functions which have one argument
which is a first-order function. We will denote a variable function of
this kind by the notation f!(φ̂!ẑ), and any value
of such a function by f!(φ!ẑ). Like φ!x,
f!(φ!ẑ) is a function of two variables, namely
f!(φ̂!ẑ) and φ!ẑ. Among possible
values of f!(φ!ẑ) will be φ!a (where a
is constant), (x).φ!x, (∃ x).φ!x, and so on.
(These result from assigning a value to f, leaving φ to
be assigned.) We will call such functions "predicative functions of
first-order functions."

In the second place, we have second-order functions of two arguments,
one of which is a first-order function while the other is an
individual. Let us denote undetermined values of such functions by the
notation

f!(φ!ẑ, x).

As soon as x is assigned, we shall have a predicative function of
φ!ẑ. If our function contains no first-order function
as apparent variable, we shall obtain a predicative function of
x if we assign a value to φ!ẑ. Thus, to take the
simplest possible case, if f!(φ!ẑ, x) is φ!x,
the assignment of a value to φ gives us a predicative function
of x, in virtue of the definition of "φ!x." But if
f!(φ!ẑ, x) contains a first-order function as apparent
variable, the assignment of a value to φ!ẑ gives us a
second-order function of x.

In the third place, we have second-order functions of
individuals. These will all be derived from functions of the form
f!(φ!ẑ, x) by turning φ into an apparent
variable. We do not, therefore, need a new notation for them.

We have also second-order functions of two first-order functions, or of
two such functions and an individual, and so on.

We may now proceed in exactly the same way to third-order matrices,
which will be functions containing second-order functions as arguments,
and containing no apparent variables, and no arguments except
individuals and first-order functions and second-order functions.
Thence we shall proceed, as before, to third-order functions; and so we
can proceed indefinitely. If the highest order of variable occurring in
a function, whether as argument or as apparent variable, is a function
of the nth order, then the function in which it occurs is of the
n + 1th order. We do not arrive at functions of an infinite order,
because the number of arguments and of apparent variables in a function
must be finite, and therefore every function must be of a finite order.
Since the orders of functions are only defined step by step, there
can be no process of "proceeding to the limit," and functions of an
infinite order cannot occur.

We will define a function of one variable as predicative when
it is of the next order above that of its argument, i.e. of the
lowest order compatible with its having that argument. If a function
has several arguments, and the highest order of function occurring
among the arguments is the nth, we call the function predicative
if it is of the n + 1th order, i.e. again, if it is of
the lowest order compatible with its having the arguments it has. A
function of several arguments is predicative if there is one of its
arguments such that, when the other arguments have values assigned to
them, we obtain a predicative function of the one undetermined argument.

It is important to observe that all possible functions in the above
hierarchy can be obtained by means of predicative functions and
apparent variables. Thus, as we saw, second-order functions of an
individual x are of the form

(φ).f!(φ ! ẑ, x) or (∃ φ).f!(φ ! ẑ, x) or (φ, ψ).f!(φ !ẑ, ψ !ẑ, x) or etc.,

where f is a second-order predicative function. And speaking
generally, a non-predicative function of the nth order is
obtained from a predicative function of the nth order by turning
all the arguments of the n-1th order into apparent variables.
(Other arguments also may be turned into apparent variables.) Thus
we need not introduce as variables any functions except predicative
functions. Moreover, to obtain any function of one variable x,
we need not go beyond predicative functions of two variables.
For the function (ψ).f!(φ!ẑ, ψ !ẑ, x), where
f is given, is a function of φ !ẑ and x, and is
predicative. Thus it is of the form F!(φ !ẑ, x), and
therefore (φ, ψ).f!(φ !ẑ, ψ !ẑ, x) is of
the form (φ).F!(φ !ẑ, x). Thus speaking generally,
by a succession of steps we find that, if φ ! û is a
predicative function of a sufficiently high order, any assigned
non-predicative function of x will be of one of the two forms

(φ).F!(φ !û, x), (∃ φ).F!(φ !û, x),

where F is a predicative function of φ ! û and x.
PM-VERBATIM-END PM1:INTRODUCTION-CH2-HIGHER-ORDER-PREDICATIVE-PP55-56 -/

/- PM-FORMAL-GLOSS
The finite hierarchy of higher-order and predicative functions remains documentary pending a separate audited model.
-/

/- PM-VERBATIM-BEGIN PM1:INTRODUCTION-CH2-PROPOSITION-HIERARCHY-P57-58A
The nature of the above hierarchy of functions may be restated as
follows. A function, as we saw at an earlier stage, presupposes as
part of its meaning the totality of its values, or, what comes to the
same thing, the totality of its possible arguments. The arguments to
a function may be functions or propositions or individuals. (It will
be remembered that individuals were defined as whatever is neither a
proposition nor a function.) For the present we neglect the case in
which the argument to a function is a proposition. Consider a function
whose argument is an individual. This function presupposes the totality
of individuals; but unless it contains functions as apparent variables,
it does not presuppose any totality of functions. If, however, it does
contain a function as apparent variable, then it cannot be defined
until some totality of functions has been defined. It follows that we
must first define the totality of those functions that have individuals
as arguments and contain no functions as apparent variables. These
are the predicative functions of individuals. Generally, a
predicative function of a variable argument is one which involves no
totality except that of the possible values of the argument, and those
that are presupposed by any one of the possible arguments. Thus a
predicative function of a variable argument is any function which can
be specified without introducing new kinds of variables not necessarily
presupposed by the variable which is the argument.

A closely analogous treatment can be developed for propositions.
Propositions which contain no functions and no apparent variables may
be called elementary propositions. Propositions which are not
elementary, which contain no functions, and no apparent variables
except individuals, may be called first-order propositions. (It
should be observed that no variables except apparent variables
can occur in a proposition, since whatever contains a real variable is a function, not a proposition.) Thus elementary and
first-order propositions will be values of first-order functions. (It
should be remembered that a function is not a constituent in one of its
values: thus for example the function "x̂ is human" is not a
constituent of the proposition "Socrates is human.") Elementary and
first-order propositions presuppose no totality except (at most) the
totality of individuals. They are of one or other of the three forms

φ !x; (x). φ !x; (∃ x).φ !x,

where φ !x is a predicative function of an individual. It
follows that, if p represents a variable elementary proposition
or a variable first-order proposition, a function fp is either
f(φ !x) or f{(x).φ !x} or f{(∃ x).φ !x}.
Thus a function of an elementary or a first-order proposition may
always be reduced to a function of a first-order function. It follows
that a proposition involving the totality of first-order propositions
may be reduced to one involving the totality of first-order functions;
and this obviously applies equally to higher orders. The propositional
hierarchy can, therefore, be derived from the functional hierarchy, and
we may define a proposition of the nth order as one which involves an
apparent variable of the n - 1th order in the functional hierarchy.
The propositional hierarchy is never required in practice, and is only
relevant for the solution of paradoxes; hence it is unnecessary to go
into further detail as to the types of propositions.
PM-VERBATIM-END PM1:INTRODUCTION-CH2-PROPOSITION-HIERARCHY-P57-58A -/

/- PM-FORMAL-GLOSS
The hierarchy of propositions is source-critical prose and does not alter the current formal syntax.
-/

/- PM-VERBATIM-BEGIN PM1:INTRODUCTION-CH2-REDUCIBILITY-PP58B-60
VI. The Axiom of Reducibility.

It remains to consider the "axiom of reducibility." It will be seen
that, according to the above hierarchy, no statement can be made
significantly about "all a-functions," where a is some given
object. Thus such a notion as "all properties of a," meaning
"all functions which are true with the argument a," will be
illegitimate. We shall have to distinguish the order of function
concerned. We can speak of "all predicative properties of a," "all
second-order properties of a," and so on. (If a is not an
individual, but an object of order n, "second-order properties of
a" will mean "functions of order n + 2 satisfied by a.")
But we cannot speak of "all properties of a." In some cases, we can
see that some statement will hold of "all nth-order properties of
a," whatever value n may have. In such cases, no practical harm
results from regarding the statement as being about "all properties of
a," provided we remember that it is really a number of statements,
and not a single statement which could be regarded as assigning another
property to a, over and above all properties. Such cases will
always involve some systematic ambiguity, such as that involved in
the meaning of the word "truth," as explained above. Owing to this
systematic ambiguity, it will be possible, sometimes, to combine
into a single verbal statement what are really a number of different
statements, corresponding to different orders in the hierarchy. This is
illustrated in the case of the liar, where the statement "all A's
statements are false" should be broken up into different statements
referring to his statements of various orders, and attributing to each
the appropriate kind of falsehood.

The axiom of reducibility is introduced in order to legitimate a great
mass of reasoning, in which, prima facie, we are concerned with such
notions as "all properties of a" or "all a-functions," and
in which, nevertheless, it seems scarcely possible to suspect any
substantial error. In order to state the axiom, we must first define
what is meant by "formal equivalence." Two functions φx̂,
ψx̂ are said to be "formally equivalent" when, with
every possible argument x, φx is equivalent to ψx, i.e. φx and ψx are either both true or
both false. Thus two functions are formally equivalent when they are
satisfied by the same set of arguments. The axiom of reducibility is
the assumption that, given any function φx̂, there is a
formally equivalent predicative function, i.e. there is
a predicative function which is true when φx is true and false
when φx is false. In symbols, the axiom is:

⊢ : (∃ ψ) : φx · ≡₍x₎ · ψ!x.

For two variables, we require a similar axiom, namely: Given any
function φ(x̂, ŷ), there is a formally equivalent predicative function, i.e.
⊢ : (∃ ψ) : φ(x, y) · ≡₍x, y₎ · ψ!(x, y).

In order to explain the purposes of the axiom of reducibility, and the
nature of the grounds for supposing it true, we shall first illustrate
it by applying it to some particular cases.

If we call a predicate of an object a predicative function which
is true of that object, then the predicates of an object are only some
among its properties. Take for example such a proposition as "Napoleon
had all the qualities that make a great general." We may interpret this
as meaning "Napoleon had all the predicates that make a great general."
Here there is a predicate which is an apparent variable. If we put
"f(φ!ẑ)" for "φ!ẑ is a predicate required
in a great general," our proposition is

(φ) : f(φ!ẑ) implies φ!(Napoleon).

Since this refers to a totality of predicates, it is not itself a
predicate of Napoleon. It by no means follows, however, that there is
not some one predicate common and peculiar to great generals. In fact,
it is certain that there is such a predicate. For the number of great
generals is finite, and each of them certainly possessed some predicate
not possessed by any other human being—for example, the exact instant
of his birth. The disjunction of such predicates will constitute a
predicate common and peculiar to great generals [20]. If we call this
predicate ψ!ẑ, the statement we made about Napoleon was
equivalent to ψ!(Napoleon). And this equivalence holds
equally if we substitute any other individual for Napoleon. Thus we
have arrived at a predicate which is always equivalent to the property
we ascribed to Napoleon, i.e. it belongs to those objects which
have this property, and to no others. The axiom of reducibility states
that such a predicate always exists, i.e. that any property
of an object belongs to the same collection of objects as those that
possess some predicate.

We may next illustrate our principle by its application to identity. In this connection, it has a certain affinity with
Leibniz's identity of indiscernibles. It is plain that, if x and
y are identical, and φx is true, then φy is
true. Here it cannot matter what sort of function φx̂ may
be: the statement must hold for any function. But we cannot
say, conversely: "If, with all values of φ, φx implies
φy, then x and y are identical"; because "all values
of φ" is inadmissible. If we wish to speak of "all values of
φ," we must confine ourselves to functions of one order. We may
confine φ to predicates, or to second-order functions, or to
functions of any order we please. But we must necessarily leave out
functions of all but one order. Thus we shall obtain, so to speak,
a hierarchy of different degrees of identity. We may say "all the
predicates of x belong to y," "all second-order properties of
x belong to y," and so on. Each of these statements implies
all its predecessors: for example, if all second-order properties of
x belong to y, then all predicates of x belong to y,
for to have all the predicates of x is a second-order property,
and this property belongs to x. But we cannot, without the help of
an axiom, argue conversely that if all the predicates of x belong
to y, all the second-order properties of x must also belong to
y. Thus we cannot, without the help of an axiom, be sure that x
and y are identical if they have the same predicates. Leibniz's
identity of indiscernibles supplied this axiom. It should be observed
that by "indiscernibles" he cannot have meant two objects which agree
as to all their properties, for one of the properties of x
is to be identical with x, and therefore this property would
necessarily belong to y if x and y agreed in all their properties. Some limitation of the common properties necessary to
make things indiscernible is therefore implied by the necessity of an
axiom. For purposes of illustration (not of interpreting Leibniz) we
may suppose the common properties required for indiscernibility to be
limited to predicates. Then the identity of indiscernibles will state
that if x and y agree as to all their predicates, they are
identical. This can be proved if we assume the axiom of reducibility.
For, in that case, every property belongs to the same collection of
objects as is defined by some predicate. Hence there is some predicate
common and peculiar to the objects which are identical with x. This
predicate belongs to x, since x is identical with itself; hence
it belongs to y, since y has all the predicates of x; hence y
is identical with x. It follows that we may define x and
y as identical when all the predicates of x belong to y, i.e. when (φ): φ !x . ⊃ . φ !y. We
therefore adopt the following definition of identity [21] :

x = y . = : (φ) : φ !x . ⊃ . φ !y Df.

But apart from the axiom of reducibility, or some axiom equivalent
in this connection, we should be compelled to regard identity as
indefinable, and to admit (what seems impossible) that two objects may
agree in all their predicates without being identical.

The axiom of reducibility is even more essential in the theory of
classes. It should be observed, in the first place, that if we assume
the existence of classes, the axiom of reducibility can be proved.
For in that case, given any function φẑ of whatever
order, there is a class α consisting of just those objects
which satisfy φẑ. Hence "φx̂" is equivalent
to "x belongs to α." But "x belongs to α"
is a statement containing no apparent variable, and is therefore a
predicative function of x. Hence if we assume the existence of
PM-VERBATIM-END PM1:INTRODUCTION-CH2-REDUCIBILITY-PP58B-60 -/

/- PM-FORMAL-GLOSS
The printed axiom of reducibility is historical text only. A future formalization must expose it as an explicit scoped structure or hypothesis, never as a silent global axiom.
-/

/- PM-VERBATIM-BEGIN PM1:INTRODUCTION-CH2-REDUCIBILITY-ALTERNATIVES-PP61-62
classes, the axiom of reducibility becomes unnecessary. The assumption
of the axiom of reducibility is therefore a smaller assumption than
the assumption that there are classes. This latter assumption has
hitherto been made unhesitatingly. However, both on the ground of the
contradictions, which require a more complicated treatment if classes
are assumed, and on the ground that it is always well to make the
smallest assumption required for proving our theorems, we prefer to
assume the axiom of reducibility rather than the existence of classes.
But in order to explain the use of the axiom in dealing with classes,
it is necessary first to explain the theory of classes, which is a
topic belonging to Chapter III. We therefore postpone to that Chapter
the explanation of the use of our axiom in dealing with classes.

It is worth while to note that all the purposes served by the axiom
of reducibility are equally well served if we assume that there is
always a function of the nth order (where n is fixed) which
is formally equivalent to φx̂, whatever may be the order
of φx̂. Here we shall mean by "a function of the nth
order" a function of the nth order relative to the arguments
to φx̂; thus if these arguments are
absolutely of the mth order, we assume the existence of a function
formally equivalent to φx̂ whose absolute order is the
m + nth. The axiom of reducibility in the form assumed above
takes n = 1, but this is not necessary to the use of the axiom.
It is also unnecessary that n should be the same for different
values of m; what is necessary is that n should be constant so
long as m is constant. What is needed is that, where extensional
functions of functions are concerned, we should be able to deal with
any a-function by means of some formally equivalent function of a
given type, so as to be able to obtain results which would otherwise
require the illegitimate notion of "all a-functions"; but it does
not matter what the given type is. It does not appear, however, that
the axiom of reducibility is rendered appreciably more plausible by
being put in the above more general but more complicated form.

The axiom of reducibility is equivalent to the assumption that "any
combination or disjunction of predicates [22] is equivalent to a
single predicate," i.e. to the assumption that, if we assert
that x has all the predicates that satisfy a function f(φ !ẑ)
there is some one predicate which x will have whenever
our assertion is true, and will not have whenever it is false, and
similarly if we assert that x has some one of the predicates that
satisfy a function f(φ ! ẑ). For by means of this
assumption, the order of a non-predicative function can be lowered by
one; hence, after some finite number of steps, we shall be able to get
from any non-predicative function to a formally equivalent predicative
function. It does not seem probable that the above assumption could
be substituted for the axiom of reducibility in symbolic deductions,
since its use would require the explicit introduction of the further
assumption that by a finite number of downward steps we can pass from
any function to a predicative function, and this assumption could not
well be made without developments that are scarcely possible at an
early stage. But on the above grounds it seems plain that in fact, if
the above alternative axiom is true, so is the axiom of reducibility.
The converse, which completes the proof of equivalence, is of course
evident.

VII. Reasons for Accepting the Axiom of Reducibility.
PM-VERBATIM-END PM1:INTRODUCTION-CH2-REDUCIBILITY-ALTERNATIVES-PP61-62 -/

/- PM-FORMAL-GLOSS
Alternative forms and reasons for accepting reducibility remain metatheoretical commentary; this block adds no Lean axiom.
-/

/- PM-VERBATIM-BEGIN PM1:INTRODUCTION-CH2-NOTE-18
Cf. Chapter III .
PM-VERBATIM-END PM1:INTRODUCTION-CH2-NOTE-18 -/

/- PM-VERBATIM-BEGIN PM1:INTRODUCTION-CH2-NOTE-19
When we speak of "values of φẑ" it is
φ, not z, that is to be assigned. This follows from the
explanation in the note on p. 42. When the function itself is the
variable, it is possible and simpler to write φ rather than
φẑ, except in positions where it is necessary to emphasize
that an argument must be supplied to secure significance.
PM-VERBATIM-END PM1:INTRODUCTION-CH2-NOTE-19 -/

/- PM-VERBATIM-BEGIN PM1:INTRODUCTION-CH2-NOTE-20
When a (finite) set of predicates is given by actual
enumeration, their disjunction is a predicate, because no predicate
occurs as apparent variable in the disjunction.
PM-VERBATIM-END PM1:INTRODUCTION-CH2-NOTE-20 -/

/- PM-VERBATIM-BEGIN PM1:INTRODUCTION-CH2-NOTE-21
Note that in this definition the second sign of equality
is to be regarded as combining with "Df" to form one symbol; what is
defined is the sign of equality not followed by the letters
"Df."
PM-VERBATIM-END PM1:INTRODUCTION-CH2-NOTE-21 -/

/- PM-VERBATIM-BEGIN PM1:INTRODUCTION-CH2-NOTE-22
Here the combination or disjunction is supposed to
be given intensionally. If given extensionally ( i.e. by
enumeration), no assumption is required; but in this case the number of
predicates concerned must be finite.
PM-VERBATIM-END PM1:INTRODUCTION-CH2-NOTE-22 -/

/- PM-EDITORIAL
No sic marker is required. Four Project Gutenberg errors and one Wikisource
error are digital-only. The printed axiom of reducibility is reproduced as
historical source text and is not declared in Lean.
-/

end PM.FirstEdition.Volume1.Introduction.Chapter2
