namespace PM.Architecture.Star37ConsecutiveKernel

abbrev Class (α : Sort u) := α → Prop
abbrev Relation (α : Sort u) (β : Sort v) := α → β → Prop

def Included (A B : Class α) : Prop := ∀ x, A x → B x
def relationIncluded (P Q : Relation α β) : Prop := ∀ x y, P x y → Q x y
def inter (A B : Class α) : Class α := fun x => A x ∧ B x
def union (A B : Class α) : Class α := fun x => A x ∨ B x
def relationInter (P Q : Relation α β) : Relation α β := fun x y => P x y ∧ Q x y
def relationUnion (P Q : Relation α β) : Relation α β := fun x y => P x y ∨ Q x y
def image (P : Relation α β) (A : Class β) : Class α :=
  fun x => ∃ y, A y ∧ P x y

/-- PM I ✱37·2. -/
theorem star_37_2 (P : Relation α β) (A B : Class β) :
    Included A B → Included (image P A) (image P B) := by
  rintro inclusion x ⟨y, member, related⟩
  exact ⟨y, inclusion y member, related⟩

/-- PM I ✱37·201. -/
theorem star_37_201 (P Q : Relation α β) (A : Class β) :
    relationIncluded P Q → Included (image P A) (image Q A) := by
  rintro inclusion x ⟨y, member, related⟩
  exact ⟨y, member, inclusion x y related⟩

/-- PM I ✱37·202. -/
theorem star_37_202 (P Q : Relation α β) (A B : Class β) :
    Included A B → relationIncluded P Q → Included (image P A) (image Q B) := by
  intro classInclusion relationInclusion
  exact fun x member => star_37_201 P Q B relationInclusion x
    (star_37_2 P A B classInclusion x member)

/-- PM I ✱37·21. -/
theorem star_37_21 (P : Relation α β) (A B : Class β) :
    Included (image P (inter A B)) (inter (image P A) (image P B)) := by
  rintro x ⟨y, ⟨memberA, memberB⟩, related⟩
  exact ⟨⟨y, memberA, related⟩, ⟨y, memberB, related⟩⟩

/-- PM I ✱37·211. -/
theorem star_37_211 (P Q : Relation α β) (A : Class β) :
    Included (image (relationInter P Q) A) (inter (image P A) (image Q A)) := by
  rintro x ⟨y, member, relatedP, relatedQ⟩
  exact ⟨⟨y, member, relatedP⟩, ⟨y, member, relatedQ⟩⟩

/-- PM I ✱37·212, with the four displayed intersections left-associated. -/
theorem star_37_212 (P Q : Relation α β) (A B : Class β) :
    Included (image (relationInter P Q) (inter A B))
      (inter (inter (inter (image P A) (image P B)) (image Q A)) (image Q B)) := by
  rintro x ⟨y, ⟨memberA, memberB⟩, relatedP, relatedQ⟩
  exact ⟨⟨⟨⟨y, memberA, relatedP⟩, ⟨y, memberB, relatedP⟩⟩,
    ⟨y, memberA, relatedQ⟩⟩, ⟨y, memberB, relatedQ⟩⟩

/-- PM I ✱37·22. -/
theorem star_37_22 (P : Relation α β) (A B : Class β) :
    image P (union A B) = union (image P A) (image P B) := by
  funext x
  apply propext
  constructor
  · rintro ⟨y, memberA | memberB, related⟩
    · exact Or.inl ⟨y, memberA, related⟩
    · exact Or.inr ⟨y, memberB, related⟩
  · rintro (⟨y, member, related⟩ | ⟨y, member, related⟩)
    · exact ⟨y, Or.inl member, related⟩
    · exact ⟨y, Or.inr member, related⟩

/-- PM I ✱37·221. -/
theorem star_37_221 (P Q : Relation α β) (A : Class β) :
    image (relationUnion P Q) A = union (image P A) (image Q A) := by
  funext x
  apply propext
  constructor
  · rintro ⟨y, member, relatedP | relatedQ⟩
    · exact Or.inl ⟨y, member, relatedP⟩
    · exact Or.inr ⟨y, member, relatedQ⟩
  · rintro (⟨y, member, related⟩ | ⟨y, member, related⟩)
    · exact ⟨y, member, Or.inl related⟩
    · exact ⟨y, member, Or.inr related⟩

/-- PM I ✱37·222, with the four displayed unions left-associated. -/
theorem star_37_222 (P Q : Relation α β) (A B : Class β) :
    image (relationUnion P Q) (union A B) =
      union (union (union (image P A) (image P B)) (image Q A)) (image Q B) := by
  funext x
  apply propext
  constructor
  · rintro ⟨y, memberA | memberB, relatedP | relatedQ⟩
    · exact Or.inl (Or.inl (Or.inl ⟨y, memberA, relatedP⟩))
    · exact Or.inl (Or.inr ⟨y, memberA, relatedQ⟩)
    · exact Or.inl (Or.inl (Or.inr ⟨y, memberB, relatedP⟩))
    · exact Or.inr ⟨y, memberB, relatedQ⟩
  · rintro (((⟨y, member, related⟩ | ⟨y, member, related⟩) |
      ⟨y, member, related⟩) | ⟨y, member, related⟩)
    · exact ⟨y, Or.inl member, Or.inl related⟩
    · exact ⟨y, Or.inr member, Or.inl related⟩
    · exact ⟨y, Or.inl member, Or.inr related⟩
    · exact ⟨y, Or.inr member, Or.inr related⟩

end PM.Architecture.Star37ConsecutiveKernel
