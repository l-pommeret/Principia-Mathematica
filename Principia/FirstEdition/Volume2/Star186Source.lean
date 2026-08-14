/-! Principia Mathematica, first edition, volume II, ✱186.
Source transcription from Project Gutenberg PG78255. -/

/- PM-VERBATIM-BEGIN PM2:✱186·01
μ exp rν =R̂ {(∃ P,Q).μ =N₀rʻP.ν =N₀rʻQ.R smor (P exp Q)} Df
PM-VERBATIM-END PM2:✱186·01 -/

/- PM-VERBATIM-BEGIN PM2:✱186·02
(NrʻP) exp rν =(N₀rʻP) exp rν Df
PM-VERBATIM-END PM2:✱186·02 -/

/- PM-VERBATIM-BEGIN PM2:✱186·03
μ exp r(NrʻQ)=μ exp r(N₀rʻQ) Df
PM-VERBATIM-END PM2:✱186·03 -/

/- PM-VERBATIM-BEGIN PM2:✱186·1
⊢ :R∈ μ exp rν .≡ .(∃ P,Q).μ =N₀rʻP.ν =N₀rʻQ.R smor (P exp Q) [(*186·01)]
PM-VERBATIM-END PM2:✱186·1 -/

/- PM-VERBATIM-BEGIN PM2:✱186·11
⊢ .∃ !μ exp rν .⊃ .μ ,ν ∈ N₀R.μ ,ν ∈ NR-ι ʻΛ
PM-VERBATIM-END PM2:✱186·11 -/

/- PM-VERBATIM-BEGIN PM2:✱186·111
⊢ :∼(μ ν ∈ N₀R).⊃ .μ exp rν =Λ
PM-VERBATIM-END PM2:✱186·111 -/

/- PM-VERBATIM-BEGIN PM2:✱186·12
⊢ :R∈ μ exp rν .≡ .(∃ P,Q).μ =N₀rʻP.ν =N₀rʻQ.R smor P^Q [*176·181.*186·1]
PM-VERBATIM-END PM2:✱186·12 -/

/- PM-VERBATIM-BEGIN PM2:✱186·13
⊢ .(NrʻP) exp r(NrʻQ) =(N₀rʻP) exp r(NrʻQ)=(NrʻP) exp r(N₀rʻQ) =(N₀rʻP) exp r(N₀rʻQ)=Nrʻ(P exp Q)=Nrʻ(P^Q) [Proof as in *180·3]
PM-VERBATIM-END PM2:✱186·13 -/

/- PM-VERBATIM-BEGIN PM2:✱186·14
⊢ :ν ≠ 0r.ϖ ≠ 0r.⊃ .μ exp r(ν +̇ ϖ )=(μ exp rν )×̇ (μ exp rϖ )
PM-VERBATIM-END PM2:✱186·14 -/

/- PM-VERBATIM-BEGIN PM2:✱186·15
⊢ :ϖ ⊂ RlʻJ.⊃ .μ exp r(ϖ ×̇ ν )=(μ exp rν ) exp rϖ )
PM-VERBATIM-END PM2:✱186·15 -/

/- PM-VERBATIM-BEGIN PM2:✱186·2
⊢ :μ ∈ N₀R⊃ .0r exp rμ =0r.μ exp r0r=0r [*176·151]
PM-VERBATIM-END PM2:✱186·2 -/

/- PM-VERBATIM-BEGIN PM2:✱186·21
⊢ .μ exp r2r=μ ×̇ μ
PM-VERBATIM-END PM2:✱186·21 -/

/- PM-VERBATIM-BEGIN PM2:✱186·22
⊢ .α exp r(β +̇ 1̇ )=(α exp rβ )×̇ α
PM-VERBATIM-END PM2:✱186·22 -/

/- PM-VERBATIM-BEGIN PM2:✱186·23
⊢ .α exp r(1̇ +̇ β )=α ×̇ (α exp rβ ) [Proof as in *186·22]
PM-VERBATIM-END PM2:✱186·23 -/

/- PM-VERBATIM-BEGIN PM2:✱186·3
⊢ :. Mult ax.⊃ :P∈ Rel²excl∩ NrʻR.CʻP⊂ NrʻS.⊃ . Π NrʻP=(NrʻP) exp r(NrʻS) [*185·29]
PM-VERBATIM-END PM2:✱186·3 -/

/- PM-VERBATIM-BEGIN PM2:✱186·31
⊢ :. Mult ax.⊃ :μ ,ν ∈ NR-ι ʻΛ .P∈ Rel²excl∩ μ .CʻP⊂ ν .⊃ . Π NrʻP=μ exp rν [*186·3]
PM-VERBATIM-END PM2:✱186·31 -/

/- PM-VERBATIM-BEGIN PM2:✱186·4
⊢ .NrʻPdf=2r exp r(NrʻP) [*177·13]
PM-VERBATIM-END PM2:✱186·4 -/

/- PM-VERBATIM-BEGIN PM2:✱186·5
⊢ :μ ,ν ∈ N₀R.ν ≠ 0r.⊃ .Cʻʻ(μ exp rν )=(Cʻʻμ )^Cʻʻν
PM-VERBATIM-END PM2:✱186·5 -/

/- WITNESS-TRAILER-BEGIN PM2:✱186
PART V.

SERIES.


SUMMARY OF PART V.

A RELATION is said to be serial, or to generate a
series, when it possesses three different properties, namely (1) being
contained in diversity, (2) transitiveness, (3) connexity, i.e.
the property that the relation or its converse holds between any two
different members of its field. Thus \(P\) is a serial relation if
(1) \(P\,\unicode{x2abd}\, J\) , (2) \(P^{2}\,\unicode{x2abd}\, P\) , (3) \(x,y\in CʻP.x\neq y.\supset _{x,y}:xPy.\lor.yPx\) .
The third characteristic, that of connexity, may be written more shortly
 \[ x\in CʻP.\supset _{x}.\overrightarrow{P}ʻx\cup \iota ʻx\cup \overleftarrow{P}ʻx=CʻP, \] 
i.e. \(x\in CʻP.\supset _{x}.\overleftrightarrow{P}ʻx=CʻP\) ,
using the notation of *97; and this, in virtue of *97·23, is equivalent
to
 \[ \overleftrightarrow{P}ʻʻCʻP\in 0\cup 1. \] 

In virtue of *50·47, the first two characteristics are equivalent to
 \[ P\dot{\cap} \breve{P} =\dot{\Lambda} .P^{2}\,\unicode{x2abd}\, P. \] 
When \(P\dot{\cap} \breve{P} =\dot{\Lambda}\) , we say that \(P\) is
"asymmetrical." Thus serial relations are such as are asymmetrical,
transitive, and connected.

It might be thought that a serial relation need not be contained
in diversity, since we commonly speak of series in which there are
repetitions, i.e. in which an earlier term is identical with a
later term. Thus, e.g.
 \[ a,\, b,\, c,\, a,\, e,\, f,\, b,\, g,\, h \] 
would be called a series of letters, although the letters \(a\) and
 \(b\) recur. But in all such cases, there is some means (in the above
case, position in space) by which one occurrence of a given
term is distinguished from another occurrence, and this will be found
to mean that there is some other series (in the above case, the
series of positions in a line) free from repetitions, with which our
pseudo-series has a one-many correlation. Thus, in the above instance,
we have a series of nine positions, which we may call
 \[ 1,\, 2,\, 3,\, 4,\, 5,\, 6,\, 7,\, 8,\, 9, \] 
which form a true series without repetitions; we have a one-many
relation, that of occupying these positions, by means of which
we distinguish occurrences of \(a\) , the first occurrence being a as
the correlate of 1, the second being[Pg 514] \(a\) as the correlate of 4. All
series in which there are repetitions (which we may call pseudo-series)
are thus obtained by correlation with true series, i.e, with series
in which there is no repetition. That is to say, a pseudo-series has
as its generating relation a relation of the form \(S^{;}P\) , where
 \(P\) is a serial relation, and \(S\) is a one-many relation whose
converse domain contains the field of \(P\) . Thus what we may call
self-subsistent series must be series without repetitions, i.e.
series whose generating relations are contained in diversity.

For our purposes, there is no use in distinguishing a series from
its generating relation. A series is not a class, since it has a
definite order, while a class has no order, but is capable of many
orders (unless it contains only one term or none). The generating
relation determines the order, and also the class of terms ordered,
since this class is the field of the generating relation. Hence the
generating relation completely determines the series, and may, for all
mathematical purposes, be taken to be the series.

When \(P\) is transitive, we have
 \[ P_{\text{po}}=P.P_{*}=P\unicode{x228d} I\upharpoonright CʻP. \] 
Hence all the propositions of Part II, Section E become greatly
simplified when applied to series.

Also, since the field of a connected relation consists of a single
family, a series has one first term or none, and one last term or none.

In the case of a serial relation \(P\) , the relation \(P_{1}\) (defined
in *121·02) becomes \(P\dot{-} P^{2}\) , i.e. the relation
"immediately preceding." In a discrete series, the terms in
general immediately precede other terms. A compact series, on
the contrary, is defined as one in which there are terms between any
two: in such a series, \(P_{1}=\dot{\Lambda}\) .

It very frequently occurs that we wish to consider the relations of
various series which are all contained in some one series; for example,
we may wish to consider various series of real numbers, all arranged
in order of magnitude. In such a case, if \(P\) is the series in which
all the others are contained, and \(\alpha\) , \(\beta\) , \(\gamma\) ,
... are the fields of the contained series, the contained series
themselves are \(P\unicode{x0294f}\alpha\) , \(P\unicode{x0294f}\beta\) ,
 \(P\unicode{x0294f}\gamma\) , .... Thus when series are given as
contained in a given series, they are completely determined by their
fields.

In what follows, Section A deals with the elementary properties of
series, including maximum and minimum points, sequent points and limits.


Section B will deal with the theory of segments and kindred topics;
in this section we shall define "Dedekindian" series, and shall prove
the important proposition that the series of segments of a series is
always Dedekindian, i.e. that every class of segments has either
a maximum or a limit.

Section C, which stands outside the main developments of the book,
is concerned with convergence and the limits of functions and the
definition of a continuous function. Its purpose is to show how these
notions can be expressed, and many of their properties established, in
a much more general way than is usually done, and without assuming that
the arguments or values of the functions concerned are either numerical
or numerically measurable.

Section D will deal with "well-ordered" series, i.e. series in
which every class containing members of the field has a first term. The
properties of well-ordered series are many and important; most of them
depend upon the fact that an extended variety of mathematical induction
is possible in dealing with well-ordered series. The term "ordinal
number" is confined by usage to the relation-number of a well-ordered
series; ordinal numbers will also be considered in our fourth section.

Section E will deal with finite and infinite. We shall show that the
distinction between "inductive" and "non-reflexive" does not arise in
well-ordered series.

Section F will deal with "compact" series, i.e. series in which
there is a term between any two, i.e. in which \(P^{2}=P\) . In
particular we shall consider "rational" series (i.e. series
like the series of rationals in order of magnitude) and continuous
series (i.e. series like the series of real numbers in order of
magnitude). Our treatment of this subject will follow Cantor closely.
WITNESS-TRAILER-END PM2:✱186 -/
