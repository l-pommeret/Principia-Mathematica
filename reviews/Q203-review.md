# Audit Q203 — PM I, ✱2·06–✱2·1

Verdict: **A — texte, portée, dépendances, archive Aristotle et intégration
formelle audités; en attente de la certification par la CI GitHub**.

Sources canoniques: Whitehead et Russell, *Principia Mathematica*, première
édition, volume I (1910), pp. 104–105, feuilles de scan 126–127:

- https://en.wikisource.org/wiki/Page:Russell,_Whitehead_-_Principia_Mathematica,_vol._I,_1910.djvu/126
- https://en.wikisource.org/wiki/Page:Russell,_Whitehead_-_Principia_Mathematica,_vol._I,_1910.djvu/127

Témoins de travail indépendants: Project Gutenberg ebook 78050 et
transcription Wikisource. Le fac-similé fait autorité. La dérivée JPEG de la
page imprimée 105 contrôlée pour cet audit a le SHA-256
`353904a9208e3b27ec48340eeb42a809f770c99e797ddd1f4d306c7da7df29fb`.

## Couverture diplomatique exacte

```text
✱2·06.  ⊢ :. p ⊃ q . ⊃ : q ⊃ r . ⊃ . p ⊃ r

Dem.

        [Comm  (q ⊃ r, p ⊃ q, p ⊃ r)/(p, q, r)]
              ⊢ :: q ⊃ r . ⊃ : p ⊃ q . ⊃ . p ⊃ r :.
                   ⊃ :. p ⊃ q . ⊃ : q ⊃ r . ⊃ . p ⊃ r       (1)
        [✱2·05]  ⊢ :. q ⊃ r . ⊃ : p ⊃ q . ⊃ . p ⊃ r        (2)
        [(1).(2).✱1·11]
              ⊢ :. p ⊃ q . ⊃ : q ⊃ r . ⊃ . p ⊃ r
```

Le texte qui suit immédiatement au début de la page 105 appartient à
l'explication de cette démonstration:

> In the last line of this proof, “(1).(2).✱1·11” means that we are inferring
> in accordance with ✱1·11, having before us a proposition, namely
> `p ⊃ q . ⊃ : q ⊃ r . ⊃ . p ⊃ r`, which, by (1), is implied by
> `q ⊃ r . ⊃ : p ⊃ q . ⊃ . p ⊃ r`, which, by (2), is true. In general, in
> such cases, we shall omit the reference to ✱1·11.
>
> The above two propositions will both be referred to as the “principle of
> the syllogism” (shortened to “Syll.”), because, as will appear later, the
> syllogism in Barbara is derived from them.

La seconde phrase appelle « above two propositions » ✱2·05 et ✱2·06.

```text
✱2·07.  ⊢ : p . ⊃ . p ∨ p                    [✱1·3  p/q]
```

> Here we put nothing beyond “✱1·3 p/q,” because the proposition to be proved
> is what ✱1·3 becomes when p is written in place of q.

```text
✱2·08.  ⊢ . p ⊃ p

Dem.

        [✱2·05  (p ∨ p, p)/(q, r)]
              ⊢ :: p ∨ p . ⊃ . p : ⊃ :. p . ⊃ . p ∨ p : ⊃ . p ⊃ p   (1)
        [Taut]  ⊢ : p ∨ p . ⊃ . p                                   (2)
        [(1).(2).✱1·11]
              ⊢ :. p . ⊃ . p ∨ p : ⊃ . p ⊃ p                       (3)
        [2·07]  ⊢ : p . ⊃ . p ∨ p                                  (4)
        [(3).(4).✱1·11]  ⊢ . p ⊃ p

✱2·1.   ⊢ . ∼p ∨ p                              [Id. (✱1·01)]
```

Les espaces ajoutés dans les fractions de substitution ci-dessus rendent la
mise en ligne lisible; les symboles, l'ordre des substitutions, la hiérarchie
des points et les références reproduisent l'imprimé. Le scan imprime bien
`✱2·1` (avec astérisque), contrairement à certains rendus textuels qui perdent
ce signe. Aucun `sic`, `corr.` ou `conj.` n'est requis pour ces quatre items.

## Lecture de portée et cibles Lean

- ✱2·06:
  `(p ⊃ q) ⊃ ((q ⊃ r) ⊃ (p ⊃ r))`.
- ✱2·07: `p ⊃ (p ∨ p)`.
- ✱2·08: `p ⊃ p`.
- ✱2·1: `∼p ∨ p`.

Les deux occurrences de détachement dans ✱2·08 et celle dans ✱2·06 sont des
emplois de ✱1·1 ou ✱1·11 selon que le contexte de variables réelles est vide
ou non. Le lemme métalinguistique `PM.Derivation.detach` de Q200 ne remplace
pas ces règles: il effectue exactement cette analyse structurelle du contexte.

## Dépendances et reconstruction exacte

Ordre interne du lot: ✱2·06, ✱2·07, ✱2·08, ✱2·1.

- ✱2·06 utilise ✱2·04 (« Comm »), instancié par
  `p ↦ q ⊃ r`, `q ↦ p ⊃ q`, `r ↦ p ⊃ r`; puis ✱2·05 et un détachement.
- ✱2·07 est directement Add (✱1·3) avec `q ↦ p` (les deux arguments Lean
  valent donc `p`).
- ✱2·08 instancie ✱2·05 par `q ↦ p ∨ p`, `r ↦ p` (et conserve `p`), détache
  Taut (✱1·2), puis détache ✱2·07.
- ✱2·1 est uniquement la lecture de ✱2·08 par la définition ✱1·01:
  `p ⊃ p` est définitionnellement `∼p ∨ p`.

✱2·03 n'est pas mathématiquement nécessaire à ces quatre preuves, mais son
corps est conservé dans le prompt autonome avec ✱2·04–✱2·05 pour reproduire
sans trou le bloc antérieur Q202. Aucun résultat postérieur n'est permis.

## Audit du résultat Aristotle et porte CI

Q200 (`detach`) et Q202 (✱2·03–✱2·05) ont été intégrés et certifiés par la
CI avant la soumission de Q203. La tâche Aristotle
`012131af-25b4-48ca-94b6-1689fb56e3de`, dans le projet
`5f49ddc8-6fe3-45c6-b367-b7a44fb74e10`, s'est terminée avec l'état
`COMPLETE`. Son archive immuable `aristotle/results/Q203-final.tar.gz` a pour
SHA-256:

`a6d9cf0bea400680dc7b47df8012a1627b224c7029c346ec72c36ef067a095f4`.

Inspection indépendante de `RequestProject/Q203.lean`:

- les quatre cibles exactes ✱2·06, ✱2·07, ✱2·08 et ✱2·1 sont présentes,
  dans l'ordre demandé, sans paramètre ni conclusion modifiés;
- ✱2·06 détache exactement ✱2·05 de l'instance imprimée de Comm;
- ✱2·07 est l'instance directe d'Add;
- ✱2·08 conserve les deux détachements dans l'ordre Taut, puis ✱2·07;
- ✱2·1 est obtenu par réduction définitionnelle de ✱1·01;
- le fichier de preuve n'emploie ni `sorry`, ni `admit`, ni nouvel axiome,
  constructeur ou `unsafe`, ni `Classical`, `by_cases`, sémantique moderne ou
  règle générique de modus ponens.

Le `Main.lean` générique de l'environnement Aristotle ouvre plusieurs scopes
Mathlib, dont `Classical`, mais `Q203.lean` ne les importe ni ne les emploie;
aucun de ces scopes n'est intégré dans l'édition canonique. Les corps audités
sont maintenant intégrés avec l'état **awaiting-ci**. Ils ne deviendront
`kernel-checked` qu'après une exécution GitHub Actions réussie portant sur le
commit exact d'intégration.

Confiance: élevée pour la transcription, les portées, les substitutions et le
graphe de dépendances, sur inspection directe des deux pages canoniques.
