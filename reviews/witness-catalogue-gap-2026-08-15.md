# Quatre propositions imprimées qui n'avaient aucune entrée au catalogue

15 août 2026.

## Ce qui a été mesuré

Énumération déterministe des deux témoins Gutenberg, sans modèle : une
proposition est reconnue à un numéro en tête de ligne, à deux composantes
exactement, immédiatement suivi de mathématiques.

    tome I    3368 énoncés imprimés relevés
    tome II   3874 énoncés imprimés relevés

Comparé aux 6203 entrées de `metadata/items`, le tome I était court de quatre
propositions et le tome II de 1493.

## Les quatre du tome I

| proposition | page | lecture imprimée |
|---|---|---|
| ✱33·151 | 263 | ⊢. R⃖ʻx ⊂ ᗡʻR |
| ✱40·38  | 319 | ⊢ . Rʻʻsʻκ = sʻRʻʻʻκ |
| ✱71·28  | 454 | ⊢:R ∈ 1→ Cls.⊃.β↿R↾ γ ∈ 1→ Cls |
| ✱92·2   | 611 | ⊢:α ∈ genʻP.≡.(∃T).T ∈ PotidʻP.α=min⃗_PʻᗡʻT |

Elles sont entrées au catalogue dans `PM1-witness-gap-closure-01.json`.

✱40·38 porte dans le livre la mention « This proposition is very often used in
arithmetic » : ce n'est pas une proposition marginale. ✱71·28 était déjà
*citée* par des entrées déjà cataloguées (`PM1-star-71-catalogue-15.json`) sans
avoir d'entrée à elle — une référence pendante que rien ne signalait.

## Pourquoi elles avaient été ratées

Deux causes distinctes, et une seule est établie.

**Établie, pour ✱33·151 et ✱71·28.** Le compositeur des *Principia* règle une
minorité de numéros avec un point ordinaire — `*33.151.`, `*71.28.` — là où le
reste du livre porte le point médian `·`. Toute passe qui filtre sur `·` les
saute sans rien émettre. Le défaut ne se limite pas à la passe de catalogage :
`WITNESS_RE` dans `verify_printed_against_witness.py` s'écrit encore
`^\*(\d+(?:·\d+)+)\.` et souffre exactement du même aveuglement.

Élargir ce motif n'a **pas** été fait ici, et c'est délibéré : plus de 210
fichiers de `Principia/FirstEdition/` emploient les commandes concernées, et
faire voir au gate témoin des lectures qu'il ignorait ferait basculer des blocs
de « notation non supportée », signalée et non bloquante, vers « comparée »,
où le moindre écart devient un échec. C'est un chantier éditorial à part
entière, à mener quand la CI n'est pas l'objectif immédiat.

**Non établie, pour ✱40·38 et ✱92·2.** Leur numéro est parfaitement régulier.

Une hypothèse a été formée puis **rejetée par la mesure** : aucune des quatre
ne porte de bloc `Dem.`, et l'on pouvait croire qu'une passe reconnaissant les
propositions à leur démonstration les avait sautées. Mais le témoin compte 2541
énoncés sans `Dem.`, dont 2537 étaient correctement catalogués. L'absence de
démonstration n'explique donc rien.

Aucune cause systématique n'a été trouvée pour ces deux-là : deux omissions
isolées sur 3368 énoncés. Il n'est pas nécessaire de l'établir pour s'en
protéger — le gate les rattrape quelle qu'en soit la raison, et c'est
précisément ce qu'on attend d'un contrôle plutôt que d'une relecture.

## Le gate

`scripts/verify_catalogue_completeness.py` ferme le trou par l'autre côté : le
gate témoin juge le *texte* des blocs déjà catalogués et ne peut donc rien dire
d'une proposition jamais cataloguée — une absence ne produit ni divergence, ni
notation non supportée, ni ligne de rapport. Un catalogue plus court que le
livre ressemble trait pour trait à un catalogue qui s'accorde avec lui.

Le gate échoue sur les volumes listés dans `CERTIFIED_VOLUMES`, aujourd'hui le
seul tome I. Le déficit du tome II est compté et imprimé à chaque exécution :
c'est une dette mesurée, pas un échec étouffé. Un gate rouge de 1493 items sur
un travail que personne n'a commencé cesse de rapporter quoi que ce soit,
puisqu'il est rouge quoi qu'il arrive.
