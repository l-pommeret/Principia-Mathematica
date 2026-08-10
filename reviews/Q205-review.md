# Audit Q205 — PM I, ✱2·15–✱2·18

Verdict: **A (préparation seulement)** — transcription diplomatique, portées,
dépendances et reconstruction formelle auditées; ne pas soumettre avant que
Q200 et Q202–Q204 soient intégrés et certifiés par le noyau dans GitHub CI.

Sources canoniques: Whitehead et Russell, *Principia Mathematica*, première
édition, volume I (1910), pp. 106–108, feuilles de scan 128–130:

- https://en.wikisource.org/wiki/Page:Russell,_Whitehead_-_Principia_Mathematica,_vol._I,_1910.djvu/128
- https://en.wikisource.org/wiki/Page:Russell,_Whitehead_-_Principia_Mathematica,_vol._I,_1910.djvu/129
- https://en.wikisource.org/wiki/Page:Russell,_Whitehead_-_Principia_Mathematica,_vol._I,_1910.djvu/130

Les dérivés d'image contrôlés portent respectivement les SHA-256 abrégés
`50de3f…2cb2`, `f7c69e…21cb` et `f869a9…a40`. Project Gutenberg ebook 78050
et la transcription Wikisource sont des témoins numériques de travail; le
fac-similé de 1910 fait seul autorité en cas de divergence.

## Couverture diplomatique

```text
✱2·15.  ⊢ : ∼p ⊃ q . ⊃ . ∼q ⊃ p

Dem.

 [✱2·05  (∼p, ∼(∼q))/(p, r)]
      ⊢ :. q ⊃ ∼(∼q) . ⊃ : ∼p ⊃ q . ⊃ . ∼p ⊃ ∼(∼q)          (1)
 [✱2·12  q/p]  ⊢ . q ⊃ ∼(∼q)                                (2)
 [(1).(2).✱1·11]
      ⊢ : ∼p ⊃ q . ⊃ . ∼p ⊃ ∼(∼q)                           (3)
 [✱2·03  (∼p, ∼q)/(p, q)]
      ⊢ : ∼p ⊃ ∼(∼q) . ⊃ . ∼q ⊃ ∼(∼p)                       (4)
 [✱2·05  (∼q, ∼(∼p), p)/(p, q, r)]
      ⊢ :. ∼(∼p) ⊃ p . ⊃ : ∼q ⊃ ∼(∼p) . ⊃ . ∼q ⊃ p          (5)
 [(5).✱2·14.✱1·11]
      ⊢ : ∼q ⊃ ∼(∼p) . ⊃ . ∼q ⊃ p                           (6)
 [✱2·05  (∼p ⊃ q, ∼p ⊃ ∼(∼q), ∼q ⊃ ∼(∼p))/(p, q, r)]
      ⊢ :: ∼p ⊃ ∼(∼q) . ⊃ . ∼q ⊃ ∼(∼p) : ⊃ :.
             ∼p ⊃ q . ⊃ . ∼p ⊃ ∼(∼q) : ⊃ :
             ∼p ⊃ q . ⊃ . ∼q ⊃ ∼(∼p)                       (7)
 [(4).(7).✱1·11]
      ⊢ :. ∼p ⊃ q . ⊃ . ∼p ⊃ ∼(∼q) : ⊃ :
             ∼p ⊃ q . ⊃ . ∼q ⊃ ∼(∼p)                       (8)
 [(3).(8).✱1·11]
      ⊢ : ∼p ⊃ q . ⊃ . ∼q ⊃ ∼(∼p)                           (9)
 [✱2·05  (∼p ⊃ q, ∼q ⊃ ∼(∼p), ∼q ⊃ p)/(p, q, r)]
      ⊢ :: ∼q ⊃ ∼(∼p) . ⊃ . ∼q ⊃ p : ⊃ :.
             ∼p ⊃ q . ⊃ . ∼q ⊃ ∼(∼p) : ⊃ :
             ∼p ⊃ q . ⊃ . ∼q ⊃ p                            (10)
 [(6).(10).✱1·11]
      ⊢ :. ∼p ⊃ q . ⊃ . ∼q ⊃ ∼(∼p) : ⊃ :
             ∼p ⊃ q . ⊃ . ∼q ⊃ p                            (11)
 [(9).(11).✱1·11]  ⊢ : ∼p ⊃ q . ⊃ . ∼q ⊃ p
```

La linéarisation ci-dessus conserve exactement les onze lignes logiques du
fac-similé, les substitutions et la hiérarchie des points; seuls l'alignement
typographique et les fractions ont été adaptés au texte brut.

Le texte anglais qui suit est lui aussi dans le périmètre éditorial:

> *Note on the proof of* ✱2·15. In the above proof, it will be seen that (3),
> (4), (6) are respectively of the forms `p₁ ⊃ p₂`, `p₂ ⊃ p₃`, `p₃ ⊃ p₄`,
> where `p₁ ⊃ p₄` is the proposition to be proved. From `p₁ ⊃ p₂`,
> `p₂ ⊃ p₃`, `p₃ ⊃ p₄` the proposition `p₁ ⊃ p₄` results by repeated
> applications of ✱2·05 or ✱2·06 (both of which are called “Syll.”). It is
> tedious and unnecessary to repeat this process every time it is used; it
> will therefore be abbreviated into “[Syll.] ⊢ .(a).(b).(c). ⊃ ⊢ .(d),”
> where (a) is of the form `p₁ ⊃ p₂`, (b) of the form `p₂ ⊃ p₃`, (c) of the
> form `p₃ ⊃ p₄`, and (d) of the form `p₁ ⊃ p₄`. The same abbreviation will
> be applied to a sorites of any length. Also where we have “⊢ .p₁ .⊃
> [etc.] ⊢ .p₂,” and p₂ is the proposition to be proved, it is convenient to
> write simply “⊢ .p₁ .⊃ [etc.] ⊢ .p₂,” where “etc.” will be a reference to
> the previous propositions in virtue of which the implication `p₁ ⊃ p₂`
> holds. This form embodies the use of ✱1·11 or ✱1·1, and makes many proofs
> at once shorter and easier to follow. It is used in the first two lines of
> the following proof.

```text
✱2·16.  ⊢ : p ⊃ q . ⊃ . ∼q ⊃ ∼p

Dem.

 [✱2·12]  ⊢ . q ⊃ ∼(∼q) . ⊃
 [✱2·05]  ⊢ : p ⊃ q . ⊃ . p ⊃ ∼(∼q)                         (1)
 [✱2·03  ∼q/q]
           ⊢ : p ⊃ ∼(∼q) . ⊃ . ∼q ⊃ ∼p                     (2)
 [Syll.]   ⊢ .(1).(2). ⊃ ⊢ : p ⊃ q . ⊃ . ∼q ⊃ ∼p
```

> *Note.* The proposition to be proved will be called “Prop,” and when a
> proof ends, like that of ✱2·16, by an implication between asserted
> propositions, of which the consequent is the proposition to be proved, we
> shall write “⊢ .etc. ⊃ ⊢ .Prop”. Thus “⊃ ⊢ .Prop” ends a proof, and more or
> less corresponds to “q.e.d.”

```text
✱2·17.  ⊢ : ∼q ⊃ ∼p . ⊃ . p ⊃ q

Dem.

 [✱2·03  (∼q, p)/(p, q)]
           ⊢ : ∼q ⊃ ∼p . ⊃ . p ⊃ ∼(∼q)                     (1)
 [✱2·14]  ⊢ : ∼(∼q) ⊃ q : ⊃
 [✱2·05]  ⊢ : p ⊃ ∼(∼q) . ⊃ . p ⊃ q                        (2)
 [Syll.]   ⊢ .(1).(2). ⊃ ⊢ .Prop

✱2·15, ✱2·16 and ✱2·17 are forms of the principle of transposition, and
will be all referred to as “Transp.”

✱2·18.  ⊢ : ∼p ⊃ p . ⊃ . p

Dem.

 [✱2·12]  ⊢ . p ⊃ ∼(∼p) . ⊃
 [✱2·05]  ⊢ . ∼p ⊃ p . ⊃ . ∼p ⊃ ∼(∼p)                      (1)
 [✱2·01  ∼p/p]
           ⊢ : ∼p ⊃ ∼(∼p) . ⊃ . ∼(∼p)                     (2)
 [Syll.]   ⊢ .(1).(2). ⊃ ⊢ : ∼p ⊃ p . ⊃ . ∼(∼p)            (3)
 [✱2·14]  ⊢ . ∼(∼p) ⊃ p                                   (4)
 [Syll.]   ⊢ .(3).(4). ⊃ ⊢ .Prop

This is the complement of the principle of the reductio ad absurdum. It
states that a proposition which follows from the hypothesis of its own
falsehood is true.
```

## Portées Lean et graphe exact

- ✱2·15: `(∼p ⊃ q) ⊃ (∼q ⊃ p)`; chaîne historique (3),(4),(6), développée
  par les instances explicites de Syll. données aux lignes (7)–(11).
- ✱2·16: `(p ⊃ q) ⊃ (∼q ⊃ ∼p)`; ✱2·12 puis ✱2·05 produisent (1), ✱2·03
  produit (2), puis syllogisme.
- ✱2·17: `(∼q ⊃ ∼p) ⊃ (p ⊃ q)`; ✱2·03 produit (1), ✱2·14 et ✱2·05
  produisent (2), puis syllogisme.
- ✱2·18: `(∼p ⊃ p) ⊃ p`; ✱2·12 et ✱2·05 donnent (1), Abs ✱2·01 donne
  (2), Syll. donne (3), puis ✱2·14 et Syll. concluent.

`PM.Derivation.detach` est la preuve métalinguistique de l'alternative entre
✱1·1 (contexte vide) et ✱1·11 (variables réelles); elle ne constitue ni un
axiome ni une nouvelle règle objet. Chaque « Syll. » doit être développé par
✱2·05/✱2·06 et des détachements, sans raisonnement sémantique moderne.

## Collation des témoins numériques — aucune leçon `[sic]`

Quatre défauts certains du `data-tex` de Project Gutenberg ont été contrôlés
contre le fac-similé dans la fenêtre nécessaire à Q205:

1. ✱2·13 Dem. (1), hors lot mais dépendance immédiatement antérieure: PG
   omet la virgule séparant les deux remplacements au numérateur; l'imprimé
   les sépare bien.
2. ✱2·15 Dem. (3): PG insère un `⊃` parasite immédiatement après le premier
   signe de portée `:`; il n'existe pas dans l'imprimé.
3. ✱2·15 Dem. (8): PG corrompt la référence en `[(4).(7).✱1·11]` en plaçant
   la parenthèse ouvrante avant `4` au lieu d'avant `(4)`.
4. ✱2·16 Dem. (2): PG omet `⊃` entre `p` et `∼(∼q)`; le scan imprime bien
   `p ⊃ ∼(∼q)`.

Ce sont exclusivement des erreurs du témoin numérique PG78050. Aucun
`[sic]`, `corr.` ou `conj.` ne doit être attaché au texte de 1910 pour ces
lectures. La transcription Wikisource demeure elle aussi un témoin dérivé,
non une autorité de remplacement.

## Porte de soumission

Q205 reste **prepared**, non **submitted**, jusqu'à ce que les corps de Q200,
Q202, Q203 et Q204 reproduits dans son prompt soient présents dans le fichier
canonique, vérifiés sans `sorry`, `admit`, axiome ajouté ou échappatoire
`unsafe`, et certifiés par GitHub CI. Confiance élevée sur les quatre énoncés,
les démonstrations, le sorite, les notes anglaises et les divergences PG.

## Audit du résultat Aristotle

Projet `4f862879-a48c-4ade-bc5f-4d829cd11c49`, tâche
`c9767f09-c065-47b7-b7e4-219df760cdab`, état terminal `COMPLETE`. L'archive
immuable `aristotle/results/Q205-final.tar.gz` porte le SHA-256
`404b741e8fcad61a2e25fd57f11eb2b9c872a95c2d01a474d2e0faa418019634`.

Couverture acceptée: les quatre énoncés exacts ✱2·15–✱2·18 et chaque ligne
imprimée de leurs démonstrations sont présents. Le fichier cible n'emploie ni
`sorry`, `admit`, nouvel axiome, déclaration `unsafe`, `Classical`, `by_cases`,
raisonnement sémantique, ni règle générique de substitution. Le fichier
`Main.lean` produit automatiquement par le service ouvre un scope `Classical`,
mais Q205 ne l'importe ni ne l'utilise; ce harnais n'est pas intégré.

Les dépendances directes des termes Lean ont été confrontées ligne par ligne
aux références imprimées. `PM.Derivation.detach` se normalise vers ✱1·11 dans
ce contexte de variables réelles; `Syll.` est développé par ✱2·06. Les triples
historique/Lean/normalisé sont consignés dans
`metadata/items/PM1-star-2-Q205.json`. Verdict final: **A, kernel-checked**.
Le noyau Lean et le contrôle anti-échappatoires ont réussi sur le commit
`4fea5580f72e4d9bba96e7fd3555602a9e1d6a94`, exécution GitHub Actions
https://github.com/l-pommeret/Principia-Mathematica/actions/runs/31417330606.
