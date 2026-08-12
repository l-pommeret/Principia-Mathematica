import Principia.Architecture.CanonicalOrderedAdapters

namespace PM.Architecture.CanonicalNormalization

open PM.CanonicalOrderedFormula

/-- Source-labelled scope normalizations for the printed ✱9 definition chain.
This is syntax evidence only: it introduces no assertion or derivation. -/
inductive NormalizesScoped : Raw Γ → Raw Γ → Prop where
  | refl (p) : NormalizesScoped p p
  | negAlways (p) :
      NormalizesScoped (.neg (.quantified .always p))
        (.quantified .sometimes (.neg p))
  | negSometimes (p) :
      NormalizesScoped (.neg (.quantified .sometimes p))
        (.quantified .always (.neg p))
  /-- ✱9·06 in the orientation used in line (4)→(5) of ✱9·21.  The
  antecedent is explicitly weakened below the existential binder before that
  binder is moved into the consequent. -/
  | star_9_06_imp (p q) :
      NormalizesScoped (.quantified .sometimes
        (.disj (.neg (weakenBound p)) q))
        (.disj (.neg p) (.quantified .sometimes q))
  /-- The displayed ✱9·08 occurrence in line (5)→(6) of ✱9·21.  This is a
  closed source-labelled scope certificate, rather than a new judgement rule:
  its two endpoints are the independently collated Raw displays. -/
  | star_9_21_line5_line6 (φ ψ : Apparent Γ [.elementaryProposition]) :
      NormalizesScoped
        (CanonicalOrderedAdapters.star_9_21_line5_raw φ ψ)
        (CanonicalOrderedAdapters.star_9_21_line6_raw φ ψ)
  | disjRight (q p r) :
      NormalizesScoped (.disj (.quantified q p) r)
        (.quantified q (.disj p (weakenBound r)))
  | disjLeft (q p r) :
      NormalizesScoped (.disj r (.quantified q p))
        (.quantified q (.disj (weakenBound r) p))
  /-- ✱9·07: universal-left/existential-right, retaining `x` outside `y`.
  The existential body already binds `y`, so it is shifted at cutoff one
  rather than weakened at cutoff zero. -/
  | disjAlwaysSometimes (p q) :
      NormalizesScoped (.disj (.quantified .always p) (.quantified .sometimes q))
        (.quantified .always (.quantified .sometimes
          (.disj (weakenBound p) (shiftBoundAt 1 q))))
  /-- ✱9·08: existential-left/universal-right, with the same printed binder
order after the scope normalization.  The existential body is shifted past
the added outer universal while preserving its own inner binder. -/
  | disjSometimesAlways (p q) :
      NormalizesScoped (.disj (.quantified .sometimes p) (.quantified .always q))
        (.quantified .always (.quantified .sometimes
          (.disj (weakenBound q) (shiftBoundAt 1 p))))
  | alwaysCongr : NormalizesScoped p q →
      NormalizesScoped (.quantified .always p) (.quantified .always q)
  | sometimesCongr : NormalizesScoped p q →
      NormalizesScoped (.quantified .sometimes p) (.quantified .sometimes q)
  | negCongr : NormalizesScoped p q →
      NormalizesScoped (.neg p) (.neg q)
  | disjCongr : NormalizesScoped p q → NormalizesScoped r s →
      NormalizesScoped (.disj p r) (.disj q s)
  | trans : NormalizesScoped p q → NormalizesScoped q r → NormalizesScoped p r

theorem normalizesSmartNeg (p : Raw Γ) :
    NormalizesScoped (.neg p) (smartNeg p) := by
  induction p with
  | quantified quantifier body ih =>
      cases quantifier
      · exact .trans (.negAlways body) (.sometimesCongr ih)
      · exact .trans (.negSometimes body) (.alwaysCongr ih)
  | _ => exact .refl _

/-- Depth-indexed companion used by capture-safe smart constructors.  The
historical `NormalizesScoped` relation remains unchanged. -/
inductive NormalizesScopedAt : Nat → Raw Γ → Raw Γ → Prop where
  | refl (depth) (p) : NormalizesScopedAt depth p p
  | negAlways (depth) (p) :
      NormalizesScopedAt depth (.neg (.quantified .always p))
        (.quantified .sometimes (.neg p))
  | negSometimes (depth) (p) :
      NormalizesScopedAt depth (.neg (.quantified .sometimes p))
        (.quantified .always (.neg p))
  | disjRight (depth) (q) (p r) :
      NormalizesScopedAt depth (.disj (.quantified q p) r)
        (.quantified q (.disj p (shiftBoundAt depth r)))
  | disjLeft (depth) (q) (p r) :
      NormalizesScopedAt depth (.disj r (.quantified q p))
        (.quantified q (.disj (shiftBoundAt depth r) p))
  | disjAlwaysSometimes (depth) (p q) :
      NormalizesScopedAt depth
        (.disj (.quantified .always p) (.quantified .sometimes q))
        (.quantified .always (.quantified .sometimes
          (.disj (shiftBoundAt (depth + 1) p)
            (shiftBoundAt (depth + 1) q))))
  | disjSometimesAlways (depth) (p q) :
      NormalizesScopedAt depth
        (.disj (.quantified .sometimes p) (.quantified .always q))
        (.quantified .always (.quantified .sometimes
          (.disj (shiftBoundAt (depth + 1) p)
            (shiftBoundAt (depth + 1) q))))
  | quantifiedCongr (depth) (q) : NormalizesScopedAt (depth + 1) p r →
      NormalizesScopedAt depth (.quantified q p) (.quantified q r)
  /-- A completed local normalization may subsequently be packaged by a
  binder; its local cutoff remains zero because the normalization has already
  been performed before packaging. -/
  | quantifiedClosedCongr (q) : NormalizesScopedAt 0 p r →
      NormalizesScopedAt 0 (.quantified q p) (.quantified q r)
  | negCongr (depth) : NormalizesScopedAt depth p q →
      NormalizesScopedAt depth (.neg p) (.neg q)
  | disjCongr (depth) : NormalizesScopedAt depth p q →
      NormalizesScopedAt depth r s →
      NormalizesScopedAt depth (.disj p r) (.disj q s)
  | trans : NormalizesScopedAt depth p q → NormalizesScopedAt depth q r →
      NormalizesScopedAt depth p r

def smartDisjScopedCertifiedAux (depth : Nat) :
    (fuel : Nat) → (p q : Raw Γ) →
      { r : Raw Γ // NormalizesScopedAt depth (.disj p q) r }
  | 0, p, q => ⟨.disj p q, .refl _ _⟩
  | fuel + 1, .quantified .always p, .quantified .sometimes q =>
      let recursive := smartDisjScopedCertifiedAux (depth + 2) fuel
        (shiftBoundAt (depth + 1) p) (shiftBoundAt (depth + 1) q)
      ⟨.quantified .always (.quantified .sometimes recursive.1),
        .trans (.disjAlwaysSometimes depth p q)
          (.quantifiedCongr depth .always
            (.quantifiedCongr (depth + 1) .sometimes recursive.2))⟩
  | fuel + 1, .quantified .sometimes p, .quantified .always q =>
      let recursive := smartDisjScopedCertifiedAux (depth + 2) fuel
        (shiftBoundAt (depth + 1) p) (shiftBoundAt (depth + 1) q)
      ⟨.quantified .always (.quantified .sometimes recursive.1),
        .trans (.disjSometimesAlways depth p q)
          (.quantifiedCongr depth .always
            (.quantifiedCongr (depth + 1) .sometimes recursive.2))⟩
  | fuel + 1, .quantified quantifier p, q =>
      let recursive := smartDisjScopedCertifiedAux (depth + 1) fuel p
        (shiftBoundAt depth q)
      ⟨.quantified quantifier recursive.1,
        .trans (.disjRight depth quantifier p q)
          (.quantifiedCongr depth quantifier recursive.2)⟩
  | fuel + 1, p, .quantified quantifier q =>
      let recursive := smartDisjScopedCertifiedAux (depth + 1) fuel
        (shiftBoundAt depth p) q
      ⟨.quantified quantifier recursive.1,
        .trans (.disjLeft depth quantifier q p)
          (.quantifiedCongr depth quantifier recursive.2)⟩
  | _ + 1, p, q => ⟨.disj p q, .refl _ _⟩

theorem smartDisjScopedCertifiedAux_value
    (depth fuel : Nat) (p q : Raw Γ) :
    (smartDisjScopedCertifiedAux depth fuel p q).1 =
      smartDisjScopedAux depth fuel p q := by
  induction fuel generalizing depth p q with
  | zero => rfl
  | succ fuel ih =>
      cases p <;> cases q <;> try rfl
      all_goals try { cases ‹Quantifier› }
      all_goals try { cases ‹Quantifier› }
      all_goals try { simp [smartDisjScopedCertifiedAux, smartDisjScopedAux, ih] }
      case quantified.quantified qp p qq q =>
        cases qp <;> cases qq <;>
          simp [smartDisjScopedCertifiedAux, smartDisjScopedAux, ih]

theorem normalizesSmartDisjScopedAux
    (depth fuel : Nat) (p q : Raw Γ) :
    NormalizesScopedAt depth (.disj p q)
      (smartDisjScopedAux depth fuel p q) := by
  rw [← smartDisjScopedCertifiedAux_value depth fuel p q]
  exact (smartDisjScopedCertifiedAux depth fuel p q).property

theorem normalizesSmartDisjScoped (p q : Raw Γ) :
    NormalizesScopedAt 0 (.disj p q) (smartDisjScoped p q) := by
  exact normalizesSmartDisjScopedAux 0 (rawSize p + rawSize q) p q

theorem normalizesSmartNegAt (depth : Nat) (p : Raw Γ) :
    NormalizesScopedAt depth (.neg p) (smartNeg p) := by
  induction p generalizing depth with
  | quantified quantifier body ih =>
      cases quantifier
      · exact .trans (.negAlways depth body)
          (.quantifiedCongr depth .sometimes (ih (depth + 1)))
      · exact .trans (.negSometimes depth body)
          (.quantifiedCongr depth .always (ih (depth + 1)))
  | _ => exact .refl _ _

theorem normalizesFirstOrderMatrixRedexScoped
    (matrix : FirstOrderMatrix Γ Δ) :
    NormalizesScopedAt 0
      (CanonicalOrderedAdapters.ofFirstOrderMatrixRedex matrix)
      (CanonicalOrderedAdapters.ofFirstOrderMatrixScoped matrix) := by
  induction matrix with
  | quantified proposition => exact .refl _ _
  | neg matrix ih =>
      exact .trans (.negCongr 0 ih)
        (normalizesSmartNegAt 0 _)
  | disj left right ihLeft ihRight =>
      exact .trans (.disjCongr 0 ihLeft ihRight)
        (normalizesSmartDisjScoped _ _)

/-- Stability witness for the one closed, source-labelled line-(5)→line-(6)
certificate of ✱9·21.  It stays an explicit parameter: substitution must not
turn this source-specific certificate into a generic logical rule. -/
def Star921Line5Line6Stable : Prop :=
  ∀ {Γ Ξ} (σ : Substitution Γ Ξ)
    (φ ψ : Apparent Γ [.elementaryProposition]),
    NormalizesScoped
      (substitute σ (CanonicalOrderedAdapters.star_9_21_line5_raw φ ψ))
      (substitute σ (CanonicalOrderedAdapters.star_9_21_line6_raw φ ψ))

theorem NormalizesScoped.substitute
    (stable921 : Star921Line5Line6Stable)
    {p q : Raw Γ} (certificate : NormalizesScoped p q) (σ : Substitution Γ Ξ) :
    NormalizesScoped (CanonicalOrderedFormula.substitute σ p)
      (CanonicalOrderedFormula.substitute σ q) := by
  induction certificate generalizing Ξ with
  | refl p => exact .refl _
  | negAlways p => exact .negAlways _
  | negSometimes p => exact .negSometimes _
  | star_9_06_imp p q =>
      simpa [CanonicalOrderedFormula.substitute,
        CanonicalOrderedFormula.substitute_lift_weakenBound] using
        NormalizesScoped.star_9_06_imp (CanonicalOrderedFormula.substitute σ p)
          (CanonicalOrderedFormula.substitute (Substitution.lift σ) q)
  | star_9_21_line5_line6 φ ψ => exact stable921 σ φ ψ
  | disjRight quantifier p r =>
      simpa [CanonicalOrderedFormula.substitute,
        CanonicalOrderedFormula.substitute_lift_weakenBound] using
        NormalizesScoped.disjRight quantifier
          (CanonicalOrderedFormula.substitute (Substitution.lift σ) p)
          (CanonicalOrderedFormula.substitute σ r)
  | disjLeft quantifier p r =>
      simpa [CanonicalOrderedFormula.substitute,
        CanonicalOrderedFormula.substitute_lift_weakenBound] using
        NormalizesScoped.disjLeft quantifier
          (CanonicalOrderedFormula.substitute (Substitution.lift σ) p)
          (CanonicalOrderedFormula.substitute σ r)
  | disjAlwaysSometimes p q =>
      have commute := CanonicalOrderedFormula.substitute_liftN_shiftBoundAt σ 1 q
      simp only [Substitution.liftN_succ, Substitution.liftN_zero] at commute
      simp only [CanonicalOrderedFormula.substitute]
      rw [commute]
      simpa [CanonicalOrderedFormula.substitute_lift_weakenBound] using
        NormalizesScoped.disjAlwaysSometimes
          (CanonicalOrderedFormula.substitute (Substitution.lift σ) p)
          (CanonicalOrderedFormula.substitute (Substitution.lift σ) q)
  | disjSometimesAlways p q =>
      have commute := CanonicalOrderedFormula.substitute_liftN_shiftBoundAt σ 1 p
      simp only [Substitution.liftN_succ, Substitution.liftN_zero] at commute
      simp only [CanonicalOrderedFormula.substitute]
      rw [commute]
      simpa [CanonicalOrderedFormula.substitute_lift_weakenBound] using
        NormalizesScoped.disjSometimesAlways
          (CanonicalOrderedFormula.substitute (Substitution.lift σ) p)
          (CanonicalOrderedFormula.substitute (Substitution.lift σ) q)
  | alwaysCongr certificate ih =>
      simpa [CanonicalOrderedFormula.substitute] using
        NormalizesScoped.alwaysCongr (ih (Substitution.lift σ))
  | sometimesCongr certificate ih =>
      simpa [CanonicalOrderedFormula.substitute] using
        NormalizesScoped.sometimesCongr (ih (Substitution.lift σ))
  | negCongr certificate ih => exact .negCongr (ih σ)
  | disjCongr left right ihLeft ihRight => exact .disjCongr (ihLeft σ) (ihRight σ)
  | trans first second ihFirst ihSecond => exact .trans (ihFirst σ) (ihSecond σ)

end PM.Architecture.CanonicalNormalization
