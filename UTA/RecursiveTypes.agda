open import BasicLogic
open import BasicDatatypes
open import Decidable
open import SetOperations
open LogicOps
-- open import FiniteAutomata

module RecursiveTypes where

  data ∃ {A : Set} (B : A → Set) : Set where
    exists : ∀ (x : A) → x ∈ B → ∃ B

  -- Takes a Fin n and a Fin n+1, say f₁ and f₂.
  -- f₁ is mapped into Fin n+1 in such a way that it will not equal f₂, so f₂ is 'skipped'
  -- in the mapping from Fin n to Fin n+1.
  skip : ∀ {n} → Fin (succ n) → Fin n → Fin (succ n)
  skip (here _) x = down x
  skip (down v) (here n) = here (succ n)
  skip (down v) (down x) = down (skip v x)

  -- Arguments:
  -- f : Fin n → A, a mapping from Fin n into some set A.
  -- x : Fin (succ n), an element of Fin (succ n).
  -- a : An element of some set A
  -- y : Fin (succ n)
  -- Returns:
  -- An element of A.
  -- Notes:
  -- The partial application of this function that ommits y is a function from Fin (succ n) to A, call it f'.
  -- f' can be though of as the result of adding an element to the domain of f. This is accomplished by defining f'
  -- in such a way that f'(x) = a, but for any other y, f'(y) is derived from f(y') where y' is a corresponding
  -- element of Fin n.
  elimFin : ∀ {n} {A : Set} → (Fin n → A) → Fin (succ n) → A → (Fin (succ n) → A)
  elimFin {n} f (here n) a (here n) = a
  elimFin {n} f (here n) a (down y) = f y
  elimFin {(succ n)} f (down x) a (here (succ n)) = f (here n)
  elimFin {succ n} f (down x) a (down y) = elimFin (f ∘ down) x a y

  Env : ℕ → Set₁
  Env n = Fin n → Set

  -- _⅋_:=_ : ∀ {n} → Env n → Fin (succ n) → Set → Env (succ n)
  -- Γ ⅋ x := A = elimFin Γ x A

  -- Types are either Atoms (represented by elements of Fin n) or function types
  data 𝕋 (n : ℕ) : Set where
    α : Fin n → 𝕋 n
    _⇒_ : 𝕋 n → 𝕋 n → 𝕋 n

  -- Congruence Lemma
  _≡⇒≡_ : ∀ {n} {A B C D : 𝕋 n} → A ≡ B → C ≡ D → (A ⇒ C) ≡ (B ⇒ D)
  refl A ≡⇒≡ refl B = refl (A ⇒ B)

  -- Arguments:
  -- a: Fin (succ n), an atom to be added to our algebra
  -- τ: 𝕋 n, a type in our algebra
  -- Returns:
  -- The result of mapping τ into 𝕋 (succ n) by lifting all of it's atoms into Fin (succ n) by skipping a.
  wk : ∀ {n} → Fin (succ n) → 𝕋 n → 𝕋 (succ n)
  wk a (α x) = α (skip a x)
  wk a (τ₁ ⇒ τ₂) = (wk a τ₁) ⇒ (wk a τ₂)

  -- Record representing equations between types
  record 𝕋= (n : ℕ) : Set where
    constructor con
    field
      lhs : 𝕋 n
      rhs : 𝕋 n

  -- A list of equations between types
  𝕋=* : ℕ → Set
  𝕋=* n = List (𝕋= n)

  -- A list of pairs of atoms and types, generally used to represent equations where one side is an atom
  𝕋Sub : ℕ → Set
  𝕋Sub n = List (Fin n ∧ 𝕋 n)

  -- A solution to the unification problem, a mapping from
  Unifier : ℕ → Set
  Unifier n = Fin n → 𝕋 n

  SubList : ℕ → Set
  SubList n = Fin n → List (𝕋 n)

  -- Arguments:
  -- T : 𝕋= n, a datatype representing an equation between types
  -- Returns:
  -- A list of 𝕋Sub n ({Fin n, 𝕋 n} pairs) derived by recursively pairing up congruent terms
  -- in T
  invertLemma : ∀ {n : ℕ} → 𝕋= n → 𝕋Sub n
  invertLemma (con (α x) (α y)) = (x , α y ) ∷ []
  invertLemma (con (α x) t@(rhs1 ⇒ rhs2)) = (x , t ) ∷ []
  invertLemma (con l@(lhs1 ⇒ lhs2) (α x)) = (x , l) ∷ []
  invertLemma (con (lhs1 ⇒ lhs2) (rhs1 ⇒ rhs2)) = invertLemma (con lhs1 rhs1) ++ invertLemma (con lhs2 rhs2)

  -- Takes a list of 𝕋= and creates a single concatenated 𝕋Sub list using invertLemma
  invertAll : ∀ {n : ℕ} → 𝕋=* n → 𝕋Sub n
  invertAll = bindList invertLemma

  -- Arguments:
  -- x : Fin n
  -- L : 𝕋Sub n
  -- Returns:
  -- A list of types for which the LHS in L is equal to x.
  -- Note that this uses the elimFin function. elimFin will return the recursive call whenever x != y,
  -- but when x == y it will return (c ∷ rc)
  lookup : ∀ {n} → (x : Fin n) → 𝕋Sub n → List (𝕋 n)
  lookup x [] = []
  lookup {succ n} x ((y , c) ∷ cs) = elimFin (λ _ → rc) (x) (c ∷ rc) (y)
    where rc = lookup x cs

  --
  𝕋Sub→SubList : ∀ {n} → 𝕋Sub n → SubList n
  𝕋Sub→SubList ts = λ x → lookup x ts

  --
  filterAtom : ∀ {n} → Fin n → List (𝕋 n) → List (𝕋 n)
  filterAtom x [] = []
  filterAtom x (α y ∷ as) = case (λ _ → filterAtom x as) (λ _ → α y ∷ filterAtom x as) (decFin x y)
  filterAtom x ((a ⇒ b) ∷ as) = (a ⇒ b) ∷ filterAtom x as

  filterRefl : ∀ {n} → SubList n → SubList n
  filterRefl s = λ x → filterAtom x (s x)

  -- THE KEY PREPARATION FUNCTION
  prepSub : ∀ {n} → 𝕋=* n → SubList n
  prepSub eqs = filterRefl (𝕋Sub→SubList (invertAll eqs))

  dupAtom : ∀ {n : ℕ} → Fin n ∧ 𝕋 n → 𝕋Sub n → List (𝕋= n)
  dupAtom (x , τ) [] = []
  dupAtom s@(x₁ , τ₁) ((x₂ , τ₂) ∷ eqs) = case (λ _ → con τ₁ τ₂ ∷ []) (λ _ → dupAtom s eqs) (decFin x₁ x₂)

  -- Stuff for normal form translation
  getAtomicSub : ∀ (n : ℕ) → 𝕋Sub n → List (Fin n ∧ 𝕋 n)
  getAtomicSub n [] = []
  getAtomicSub n (s@(x , α x₁) ∷ eqs) = s ∷ []
  getAtomicSub n ((x , (τ₁ ⇒ τ₂)) ∷ eqs) = getAtomicSub n eqs

  data Occurs𝕋 {n : ℕ} (v : Fin n) : 𝕋 n → Set where
    inAtom : Occurs𝕋 v (α v)
    inLeft : ∀ {t1} → Occurs𝕋 v t1 → ∀ t2 → Occurs𝕋 v (t1 ⇒ t2)
    inRight : ∀ t1 {t2} → Occurs𝕋 v t2 → Occurs𝕋 v (t1 ⇒ t2)

  -- Takes an atom and a type and returns a boolean based on whether or not that atom occurs
  -- in that type
  atomOccurs : ∀ {n : ℕ} → (a : Fin n) → 𝕋 n → 𝔹
  atomOccurs a₁ (α a₂) = case (λ _ → true) (λ _ → false) (decFin a₁ a₂)
  atomOccurs a (τ ⇒ τ₁) = or (atomOccurs a τ) (atomOccurs a τ₁)

  -- Proof that atomOccurs is a decision algorithm for the Occurs𝕋 type, which axiomatizes
  -- membership of an atom in a type.
  atomOccursCorrect : ∀ {n} (v : Fin n) → decBy (Occurs𝕋 v) (atomOccurs v)
  atomOccursCorrect v (α x) with decFin v x
  ... | in1 v=x rewrite v=x = (λ _ → inAtom) , (λ x₂ → refl true)
  ... | in2 v≠x = (λ t≡f → exFalso (¬t≡f (~ t≡f))) , λ {inAtom → exFalso (v≠x (refl v))}
  atomOccursCorrect v t@(τ ⇒ τ₁) with atomOccurs v τ in p
  ... | true  = (λ x → inLeft ((pr1 (atomOccursCorrect v τ)) p) τ₁) , λ x → refl true
  ... | false = (λ x → inRight τ (((pr1 (atomOccursCorrect v τ₁)) x))) , λ {(inLeft x .τ₁) → exFalso (t≢f (atomOccurs v τ) ((pr2 (atomOccursCorrect v τ)) x) p)
                                                                          ; (inRight .τ x) → (pr2 (atomOccursCorrect v τ₁)) x}

  atomOccursDec : ∀ {n} (x : Fin n) → dec (λ A → Occurs𝕋 x A)
  atomOccursDec x = decBy2dec (λ A → Occurs𝕋 x A) (atomOccurs x) (atomOccursCorrect x)

  -- Arguments:
  -- x : Fin (succ n)
  -- y : Fin (succ n)
  -- Returns:
  -- A lemma showing that for x,y ∈ Fin (n+1) either x ≡ y or there is some z ∈ Fin n for which y ≡ skip x z.
  -- Notes:
  -- This lemma can be thought of as checking whether or not x occurs in y, i.e. the two are equal, in which case it
  -- provides a proof of this fact. If x and y are not equal, then y will not be "skipped" in the mapping (skip x),
  -- We provide a proof that there is some value in Fin n for which skip x z ≡ y, which we use in our proof of occCheck.
  occCheckVar : ∀ {n} (x y : Fin (succ n)) → x ≡ y ∨ ∃ (λ z → (y ≡ skip x z))
  occCheckVar (here _) (here _) = in1 (refl (here _))
  occCheckVar (here _) (down y) = in2 (exists y (refl (down y)) )
  occCheckVar {.(succ n)} (down x) (here (succ n)) = in2 (exists (here n) (refl (here (succ n)) ) )
  occCheckVar {succ n} (down x) (down y) =
    case (λ xy → in1 (ext down xy))
         (λ { (exists z y=sxz) → in2 (exists (down z) (ext down y=sxz) ) })
         (occCheckVar x y)

  -- Either x occurs in the given type A, or the type A is the weakening (by x) of some type B.
  -- Arguments:
  -- x : Fin (succ n), an element of the underlying set for our type algebra
  -- A : 𝕋 (succ n), an element of our type algebra
  -- Returns:
  -- A proof that either x occurs in A, or that A is a weakening of some other type B. This formulation means that
  -- we also get the type B which is a strengthening of A.
  occCheck : ∀ {n} (x : Fin (succ n)) (A : 𝕋 (succ n)) → Occurs𝕋 x A ∨ ∃ (λ B → A ≡ wk x B)
  occCheck x (α y) = case (λ {(refl .x) → in1 (inAtom )})
                          (λ {(exists z y=wkz) → in2 (exists (α z) (ext α y=wkz) ) } )
                          (occCheckVar x y)
  occCheck x (A1 ⇒ A2) with occCheck x A1 | occCheck x A2
  ... | in1 oc | oc2 = in1 (inLeft oc A2)
  ... | in2 ex | in1 oc = in1 (inRight A1 oc)
  ... | in2 (exists B1 e1) | in2 (exists B2 e2) = in2 (exists (B1 ⇒ B2) (e1 ≡⇒≡ e2) )

  -- Arguments:
  -- x : Fin (succ n), an element of the underlying set for our type algebra
  -- As : List (𝕋 (succ n)), a list of elements of our algebra
  -- Returns:
  -- A
  -- Notes:
  -- This is a predicate that admits pairs of x and As s.t. x appears in an element of As in accordance with
  -- the Occurs𝕋 datatype
  atomOccursInList : ∀ {n} → Fin (succ n) → List (𝕋 (succ n)) → Set
  atomOccursInList x As = ∃ (λ A → occurs A As ∧ Occurs𝕋 x A)

  -- Arguments:
  -- x : Fin (succ n), an element of the underlying set of the type algebra
  -- As : List (𝕋 (succ n)), a list of types in the algebra
  -- Returns:
  -- A proof that either x does occur in some type in As or that the entire list can be strengthened
  occCheckList : ∀ {n} (x : Fin (succ n)) (As : List (𝕋 (succ n)))
                 → atomOccursInList x As ∨ ∃ (λ Bs → map (wk x) Bs ≡ As)
  occCheckList x [] = in2 (exists [] (refl []) )
  occCheckList x (A ∷ As) = case
    (λ x∈A → in1 (exists A (atHead As , x∈A ) ) )
    (λ {(exists B mapB=A) →
          case (λ {(exists B (B∈As , x∈B))→ in1 (exists B (inTail A As B∈As , x∈B))})
               (λ {(exists Bs mapwkBs=As) → in2 (exists (B ∷ Bs) (cons≡ (~ mapB=A) mapwkBs=As))})
               (occCheckList x As)} )
    (occCheck x A)



  List∀ : ∀ {A : Set} (P : A → Set) → List A → Set
  List∀ P [] = ⊤
  List∀ P (x ∷ xs) = P x ∧ List∀ P xs

  List∀map : ∀ {A B : Set} (f : A → B) (P : B → Set) (xs : List A)
            → List∀ P (map f xs) → List∀ (λ z → P (f z)) xs
  List∀map f P [] ps = tt
  List∀map f P (x ∷ xs) (p , ps) = (p , List∀map f P xs ps )

  List∀dec : ∀ {A : Set} (P : A → Set) → dec P → dec (List∀ P)
  List∀dec P decP [] = in1 tt
  List∀dec P decP (x ∷ xs) with decP x
  ... | in1 Px = case (λ ∀Px → in1 (Px , ∀Px))
                      (λ ¬∀Px → in2 λ {(Px' , ∀Px) → ¬∀Px ∀Px})
                      (List∀dec P decP xs)
  ... | in2 ¬Px = in2 (λ {(Px , ∀Px) → ¬Px Px})

  List∀Instantiate : ∀ {A : Set} (P : A → Set) → (As : List A)
                     → (a : A) → (List∀ P As) → (occurs a As) → P a
  List∀Instantiate p as a (pa , ∀pas) (atHead xs) = pa
  List∀Instantiate p as a (pb , ∀pas') (inTail b as' a∈as') = List∀Instantiate p as' a ∀pas' a∈as'

  List∃ : ∀ {A : Set} (P : A → Set) → List A → Set
  List∃ P [] = ⊥
  List∃ P (x ∷ xs) = P x ∨ List∃ P xs

  occursList∃ : ∀ {A : Set} (P : A → Set) (x : A) (xs : List A)
                → occurs x xs → P x → List∃ P xs
  occursList∃ P x .(x ∷ xs) (atHead xs) Px = in1 Px
  occursList∃ P x .(b ∷ xs) (inTail b xs x∈xs) Px = in2 (occursList∃ P x xs x∈xs Px)

  List∃dec : ∀ {A : Set} (P : A → Set) → dec P → dec (List∃ P)
  List∃dec p ¬p∨p [] = in2 (λ x → x)
  List∃dec p ¬p∨p (x ∷ xs) with ¬p∨p x
  ... | in1 px  = in1 (in1 px)
  ... | in2 ¬px = case (λ ∃ → in1 (in2 ∃)) (λ ¬∃ → in2 (λ {(in1 px) → ¬px px
                                                         ; (in2 ∃) → ¬∃ ∃})) (List∃dec p ¬p∨p xs)

  List∃Instantiate : ∀ {A : Set} (P : A → Set) → (As : List A)
                     → (List∃ P As) → ∃ (λ x → (occurs x As) ∧ P x)
  List∃Instantiate P (x ∷ xs) (in1 Px) = exists x ((atHead xs) , Px)
  List∃Instantiate P (x ∷ xs) (in2 ∃xs) with List∃Instantiate P xs ∃xs
  ... | exists x' (x'∈xs , Px') = exists x' ((inTail x xs x'∈xs) , Px')

  -- Arguments:
  -- x : Fin (succ n), an element of the underlying set for the algebra
  -- As : List (𝕋 (succ n)), a list of Types from our algebra
  -- Returns:
  -- A proof that either there is a type A in As for which x does not occur in A, or a proof that
  -- each type in the list contains an occurance of x.
  decOccAtomList : ∀ {n} (x : Fin (succ n)) (As : List (𝕋 (succ n)))
                     → (∃ (λ A → occurs A As ∧ ¬ (Occurs𝕋 x A))) ∨ List∀ (Occurs𝕋 x) As
  decOccAtomList x [] = in2 tt
  decOccAtomList x (x₁ ∷ As) with atomOccurs x x₁ in ao
  ... | true  = case (λ {(exists x (p₁ , p₂)) → in1 (exists x ((inTail x₁ As p₁) , p₂))})
                     (λ x₃ → in2 ((pr1 (atomOccursCorrect x x₁) ao) , x₃))
                     (decOccAtomList x As)
  ... | false = in1 (exists x₁ (atHead As , λ x₂ → t≢f (atomOccurs x x₁)
                                                       (pr2 (atomOccursCorrect x x₁) x₂)
                                                        ao))

  SR : ℕ → Set
  SR 0 = ⊥
  SR (succ n) = ∃ (λ (s : SubList (succ n)) → ∀ (x : Fin (succ n)) → atomOccursInList x (s x))

  -- Arguments:
  -- s : SubList n, An SR
  -- x : Fin n, an "atom"
  -- Returns:
  -- A type admitting s and x pairs such that x occurs in each of the types that s
  -- relates x to.
  properPred : ∀ {n} → SubList n → Fin n → Set
  properPred s x = List∀ (Occurs𝕋 x) (s x)

  -- Arguments:
  -- s : SubList n, an SR
  -- Returns:
  -- A type admitting s, s.t. for each x ∈ Dom(s), s x is properPred. An SR for which
  -- this is the case is called Proper
  isProperSR : ∀ {n} → SubList n → Set
  isProperSR {0} _ = ⊥
  isProperSR {succ n} s = ∀ x → properPred s x

  -- Simple list type for fin
  Fin* : ∀ (n : ℕ) → Set
  Fin* n = List (Fin n)

  -- Arguments:
  -- n : ℕ, a natural number
  -- Returns:
  -- The list containing all elements of Fin (succ n)
  enumFin : (n : ℕ) → Fin* (n)
  enumFin 0 = []
  enumFin (succ n) = here n ∷ (map down (enumFin n))

  enumFinCorrect : {n : ℕ} → (x : Fin n) → occurs x (enumFin n)
  enumFinCorrect {succ n} (here n) = atHead (map down (enumFin n))
  enumFinCorrect {succ n} (down f) = inTail (here n)
                                            (map down (enumFin n))
                                            (occursMap (enumFin n) (down) (enumFinCorrect f))

  enumFin' : {n : ℕ} (L : List (Fin n)) → Set
  enumFin' {n} L = (∀ (f : Fin n) → occurs f L)

  -- decProper : ∀ {n} → (s : SubList (succ n)) ->
  --                     isProperSR s ∨
  --                     ∃ (λ x → ∃ (λ A → occurs A (s x) ∧ ¬ Occurs𝕋 x A))
  -- decProper {n} SR = case {!   !}
  --                         {!   !}
  --                         {!   !}

  -- head : {A : Set} → (xs : List A) → ¬ (xs ≡ []) → A
  -- head [] ¬e = exFalso (¬e (refl _))
  -- head (x ∷ xs) ¬e = x

  -- unify1 : ∀ {n m} → n ≤ m → Unifier m → (s : SubList n) →
  --                            (isProperSR s ∨ ∃ (λ s' → s' ≡ WkSR s)) ∧ Unifier m



  -- subst𝕋 a A B = B[A/a]
  subst𝕋 : ∀ {n} → Fin (succ n) → 𝕋 n → 𝕋 (succ n) → 𝕋 n
  subst𝕋 a A (α b) = elimFin α a A b
  subst𝕋 a A (τ₁ ⇒ τ₂) = (subst𝕋 a A τ₁) ⇒ (subst𝕋 a A τ₂)

  -- subst[𝕋] x B [A1,..,Ak] = [A1[B/x],...,Ak[B/x]]
  subst[𝕋] : ∀ {n} → Fin (succ n) → 𝕋 n → List (𝕋 (succ n)) → List (𝕋 n)
  subst[𝕋] x A L = map (subst𝕋 x A) L

  substSubList : ∀ {n} → Fin (succ n) → 𝕋 n → SubList (succ n) → SubList n
  substSubList x B s = λ y → subst[𝕋] x B (s (skip x y))

  substVarList : ∀ {n} → Fin (succ n) → 𝕋 n → SubList (succ n) → SubList n
  substVarList x B s = prepSub (map (con B) (subst[𝕋] x B (s x)))
    -- let xList  = subst[𝕋] x B (s x)
    --     eqList = map (con B) xList
    --  in  prepSub eqList

  ++SubList : ∀ {n} → SubList n → SubList n → SubList n
  ++SubList cs1 cs2 = λ z → cs1 z ++ cs2 z

  {-
  -- subst𝕋list a [A1,..,Ak] B = [B[A1/a],..,B[Ak/a]]
  subst𝕋list : ∀ {n} → Fin (succ n) → List (𝕋 n) → 𝕋 (succ n) → List (𝕋 n)
  subst𝕋list x As B = map (λ A → subst𝕋 x A B) As

  -- subst[𝕋]list x [A1,..,Ak] [B1,..,Bl]
  -- = [B1[A1/x],..,B1[Ak/x], B2[A1/x],..,B2[Ak/x], ... ,Bl[A1/x],..,Bl[Ak/x]]
  subst[𝕋]list : ∀ {n} → Fin (succ n) → List (𝕋 n) → List (𝕋 (succ n)) → List (𝕋 n)
  subst[𝕋]list x As = bindList (subst𝕋list x As)
  -}
  -- unify1 : ∀ {n} → (s : SubList (succ n)) → isProperSR s ∨ ∃ (λ s' → )

  -- Arguments:
  -- s : SubList (succ n)
  -- x : Fin (succ n)
  -- Returns:
  -- If s is proper w.r.t. x, returns a proof that this is the case.
  -- Otherwise there is a type in s x s.t.
  solverStep1 : ∀ {n} → (s : SubList (succ n)) → (x : Fin (succ n))
                      → List∀ (Occurs𝕋 x) (s x) ∨ (𝕋 n ∧ SubList n)
  solverStep1 {n} s x with decOccAtomList x (s x)
  ... | in1 (exists A (A∈sx , x∉A)) =
    case (λ x∈A → exFalso (x∉A x∈A) )
         (λ {(exists B A≡wkB) → in2 (B , ++SubList (substSubList x B s) (substVarList x B s) )} )
         (occCheck x A)
  ... | in2 yes = in1 yes

  elimFin¬Occ : ∀ {n : ℕ} (L : List (Fin (succ n))) → (f : (Fin (succ n)))
                          → ¬ (occurs f L) → List (Fin n)
  elimFin¬Occ [] f ¬occ = []
  elimFin¬Occ {n} (x ∷ L) f ¬occ with decFin x f
  ... | in1 x≡f rewrite x≡f = exFalso (¬occ (atHead L))
  elimFin¬Occ {zero} (x ∷ L) f ¬occ | in2 ¬x≡f = []
  elimFin¬Occ {succ n} L@(here .(succ n) ∷ L') f ¬occ | in2 ¬x≡f = map (elimFin (λ x → x) f (here n)) L
  elimFin¬Occ {succ n} L@(down x' ∷ L') f ¬occ | in2 ¬x≡f = map (elimFin (λ x → x) f x') L

  -- elimFin¬OccCorrect : ∀ {n : ℕ} (L : List (Fin (succ n))) → (f : (Fin (succ n)))
  --                                 → (¬occ : ¬ (occurs f L)) → map (skip f) (elimFin¬Occ L f ¬occ) ≡ L
  -- elimFin¬OccCorrect L f ¬occ = {!   !}
  --
  -- {-  #TODOLIST#
  --     1: Need to show that there are no dups in L s.t. enumFin' L
  --     2: Need to then show that with f∈(f∷fs) and f∈fs we have a contradiction
  -- -}
  -- finListLemma : ∀ {n : ℕ} → (P : (Fin n → Set)) → dec P
  --                          → (L : List (Fin n)) → (enumFin' L)
  --                          → (List∀ P L) ∨ ∃ (λ f' → ¬ (P f'))
  -- finListLemma p ¬p∨p [] ∀f∈fs = in1 tt
  -- finListLemma {succ n} p ¬p∨p (f ∷ fs) ∀f∈fs = case (case (λ pf ∀pfs → in1 (pf , {!  !})) (λ ¬pf _ → in2 (exists f ¬pf)) (¬p∨p f))
  --     (λ {(exists x ¬px) → in2 (exists (skip f x) ¬px)})
  --     (finListLemma p' ¬p∨p' (elimFin¬Occ fs f λ x → {!   !}) λ f₁ → {!  !})
  --     where p' : Fin n → Set
  --           p' = λ x → p (skip f x)
  --           ¬p∨p' : dec p'
  --           ¬p∨p' = λ x → case (λ p → in1 p) (λ ¬p → in2 ¬p) (¬p∨p (skip f x))

  DecP→-P : ∀ {A : Set} → (P : A → Set) → dec P → dec (- P)
  DecP→-P p ¬p∨p x with ¬p∨p x
  ... | in1 px  = in2 (λ ¬px → ¬px px)
  ... | in2 ¬px = in1 ¬px

  DMList∀∃ : ∀ {A : Set} (xs : List A)
             → (P : A → Set) → dec P → ¬ List∀ P xs
             → List∃ (- P) xs
  DMList∀∃ [] P ¬P∨P ¬∀ = ¬∀ tt
  DMList∀∃ (x ∷ xs) P ¬P∨P ¬∀ with ¬P∨P x
  ... | in1 Px = in2 (DMList∀∃ xs P ¬P∨P (λ ∀x → ¬∀ (Px , ∀x)))
  ... | in2 ¬Px = in1 ¬Px


  step1 : ∀ {n} → (s : SubList (succ n)) →
                isProperSR s ∨ ∃ (λ (x : Fin (succ n)) → List∃ (- (Occurs𝕋 x)) (s x))
  step1 {n} s with List∃dec
                         (λ x → List∃ (- (Occurs𝕋 x)) (s x))
                         (λ x → List∃dec (- (Occurs𝕋 x)) (DecP→-P (Occurs𝕋 x) (atomOccursDec x)) (s x))
                         (enumFin (succ n))
  ... | in2 ¬∃ = in1 f where
     f : ∀ x → List∀ (Occurs𝕋 x) (s x)
     f x with List∀dec (Occurs𝕋 x) (atomOccursDec x) (s x)
     ... | in1 ∀occ  = ∀occ
     ... | in2 ¬∀occ with DMList∀∃ (s x) (Occurs𝕋 x) (atomOccursDec x) ¬∀occ
     ... | ∃ with List∃Instantiate (λ 𝕥 → Occurs𝕋 x 𝕥 → ⊥) (s x) ∃
     f (here .n) | in2 ¬∀occ | ∃ | exists 𝕥 (occ , ¬occ) = exFalso (¬∃ (in1 ∃))
     f (down x) | in2 ¬∀occ | ∃ | exists 𝕥 (occ , ¬occ) =
      exFalso (¬∃ (in2 (occursList∃ (λ z → List∃ (λ z₁ → (x : Occurs𝕋 z z₁) → ⊥) (s z)) (down x) (map down (enumFin n))
        (occursMap (enumFin n) down (enumFinCorrect x )) ∃)))
  ... | in1 occ with List∃Instantiate (λ x → List∃ (λ x₁ → Occurs𝕋 x x₁ → ⊥) (s x)) (enumFin (succ n)) occ
  ... | exists x (x₁ , x₂) = in2 (exists x x₂)

  step2 :  ∀ {n} → (s : SubList (succ n)) (x : Fin (succ n)) (A : 𝕋 (succ n))
                 → ¬ Occurs𝕋 x A → occurs A (s x) → (𝕋 n ∧ SubList n)
  step2 s x A x∉A A∈sx with occCheck x A
  ... | in1 x∈A = exFalso (x∉A x∈A)
  ... | in2 (exists B A=wkB) = (B , ++SubList (substSubList x B s) (substVarList x B s) )

  step3 : ∀ {n} {m} → (s : SubList (succ n)) → (Fin m → 𝕋 (succ n))
                → (isProperSR s) ∨ ((Fin (succ m) → 𝕋 n) ∧ SubList n)
  step3 {n} s sub with step1 s
  ... | in1 sIsProperSR = in1 sIsProperSR
  ... | in2 (exists x x∈sx) with List∃Instantiate _ _ x∈sx
  ... | exists A (A∈sx , x∉A) with step2 s x A x∉A A∈sx
  ... | (B , s') = in2 (elimFin (subst𝕋 x B ∘ sub) (here _) B  , s')

  -- step4 : ∀ {n} {m} → (s : SubList (succ n)) → (Fin m → 𝕋 (succ n))

  -- solverStep4 : Set
  -- solverStep4 = {! con  !}

  elemFinN : ∀ n → List (Fin n)
  elemFinN zero = []
  elemFinN (succ n) = here n ∷ map down (elemFinN n)

  elemFinNtotal : ∀ {n} → (P : Fin n → Set) → List∀ P (elemFinN n) → ∀ (x : Fin n) → P x
  elemFinNtotal {succ n} P (p , ps) (here .n) = p
  elemFinNtotal {succ n} P (p , ps) (down x) = elemFinNtotal (λ z → P (down z))
          (List∀map down P (elemFinN n) ps ) x

  solutionSub : ℕ → Set
  solutionSub zero = ⊥
  solutionSub (succ n) = Fin (succ n) ∧ 𝕋 n

  -- solverStep2 : ∀ {n} → (s : SubList (succ n)) → (xs : List (Fin n))
  --                 → List∀ (properPred s) xs
  --                 ∨ ∃ (λ x → occurs x xs ∧ ? ) (solutionSub n ∧ 𝕋= n)
  -- solverStep2 s = {!   !}










  -- These two functions get any instance of atoms in a SubList which have (non reflexive)
  -- equationson in their RHS
  getPopAtomsHelper : ∀ {n} → Fin (succ n) → SubList (succ n) → List (Fin (succ n))
  getPopAtomsHelper f s with s f
  ... | [] = []
  ... | x ∷ w = f ∷ []

  -- test = {! elemFinN 1  !}

  getPopAtoms : ∀ {n} → SubList (succ n) → List (Fin (succ n))
  getPopAtoms {n} s = bindList (λ f → getPopAtomsHelper f s) (elemFinN (succ n))

  -- NF in this context means no atom with equations appears on the RHS and each atom
  -- has one or less RHS equations, and they must be arrow types
  -- isNormalForm : ∀ {n} → SubList (succ n) → Set
  -- isNormalForm {n} s = {!   !} ∧ {!   !} ∧ {!   !}

  -- subWK : ∀ {n} → SubList n → List (𝕋 (succ n)) → SubList (succ n)
  -- subWK = {!    !}

  -- unify2 : ∀ {n} → (s : SubList (succ n)) → isNormalForm s ∨ ∃ (λ s' → )







{-
  incFin : ∀ (n : ℕ) → Fin n → Fin n
  incFin .(succ n) (here n) = here n
  incFin .(succ (succ n)) (down (here n)) = here (succ n)
  incFin (succ (succ n)) (down (down f)) = down (incFin (succ n) (down f))

  shiftUp : ∀ {n : ℕ} → Fin n → Fin n → Fin n
  shiftUp (here n) (here .n) = here n
  shiftUp (here n) (down g) = here n
  shiftUp (down t) (here _) = incFin _ (down t)
  shiftUp (down t) (down g) = down (shiftUp t g)

  liftDown : ∀ (n : ℕ) → ¬ (n ≡ 0) → Fin (succ n) → Fin n
  liftDown zero nne (here .zero) = exFalso (nne (refl _))
  liftDown (succ n) nne (here .(succ n)) = here n
  liftDown n nne (down f) = f

  noccursWeak : ∀ {n} (a : Fin (succ n)) (A : 𝕋 (succ n)) → ¬ (Occurs𝕋 a A) → 𝕋 n
  noccursWeak {zero} a@(here 0) A@(α x@(here 0)) ¬occ = subst a A (α (liftDown 0 (λ x₁ → ¬occ inAtom) (shiftUp x a)))
  noccursWeak {succ n} a A@(α x) ¬occ = subst a A (α (liftDown ((succ n)) (λ {()}) (shiftUp x a)))
  noccursWeak a (A ⇒ A₁) ¬occ = noccursWeak a A (λ x → ¬occ (inLeft x A₁))
                                ⇒ noccursWeak a A₁ (λ x → ¬occ (inRight A x))

  noV=noT : 𝕋 0 → ⊥
  noV=noT (t ⇒ t₁) = noV=noT t

  ⇒cong : ∀ {n} {A A' B B' : 𝕋 n} → A ≡ A' → B ≡ B' → A ⇒ B ≡ A' ⇒ B'
  ⇒cong (refl _) (refl _) = refl _

  occursVar : ∀ {n} (a b : Fin n) → Occurs𝕋 a (α b) → a ≡ b
  occursVar a .a inAtom = refl a

  fin1ref : ∀ (a b : Fin 1) → a ≡ b
  fin1ref (here .0) (here .0) = refl _

  noccursVar : ∀ {n} (a b : Fin (succ n)) → (ne : ¬ (a ≡ b)) → wk a (noccursWeak a (α b)  (ne ∘ occursVar a b)) ≡ α b
  noccursVar {zero} a b ne = exFalso (ne (fin1ref a b))
  noccursVar {succ n} (here .(succ n)) (here .(succ n)) ne = exFalso (ne (refl _))
  noccursVar {succ n} (here .(succ n)) (down b) ne = refl _
  noccursVar {succ n} (down a) (here .(succ n)) ne = refl _
  noccursVar {succ n} (down a) (down b) ne = {!   !}

  noccursWeakEq : ∀ {n} (a : Fin (succ n)) (A : 𝕋 (succ n)) → (ne : ¬ (Occurs𝕋 a A)) → wk a (noccursWeak a A ne) ≡ A
  noccursWeakEq {zero} a A ne with noccursWeak a A ne
  ... | d = exFalso (noV=noT d)
  noccursWeakEq {succ n} (here .(succ n)) (α (here .(succ n))) ne = exFalso (ne inAtom)
  noccursWeakEq {succ n} (down a) (α (here .(succ n))) ne = refl _
  noccursWeakEq {succ n} (here .(succ n)) (α (down x)) ne = refl _
  noccursWeakEq {succ n} (down a) (α (down x)) ne = noccursVar (down a) (down x) λ {(refl .(down a)) → ne  inAtom  }
  noccursWeakEq {succ n} a (A ⇒ A₁) ne = ⇒cong (noccursWeakEq a A (λ x → ne (inLeft x A₁)))
                                               (noccursWeakEq a A₁ (λ x → ne (inRight A x)))


  occursCheck : ∀ {n} (a : Fin (succ n)) (A : 𝕋 (succ n)) → Occurs𝕋 a A ∨ ∃ (λ B → A ≡ wk a B)
  occursCheck {n} a A with atomOccurs a A in p
  ... | true = in1 ((pr1 (atomOccursCorrect a A)) p)
  ... | false = in2 (exists (noccursWeak a A λ x → t≢f (atomOccurs a A) ((pr2 (atomOccursCorrect a A)) x) p)
                            (~ (noccursWeakEq a A (λ x → t≢f (atomOccurs a A) ((pr2 (atomOccursCorrect a A)) x) p))))


  -- Represent atoms by Fin, then should be able to kind of lift down the Fins for each step
  -- of substitution towards our NF, since there will always be a decreasing number of unique
  -- atoms on the right hand side of our equations.

  record SR : Set where
    field
      num : ℕ
      eq : Fin num → 𝕋 num

  -- occursCheck : ∀ {n : ℕ} → 𝕋Sub n → 𝔹
  -- occursCheck [] = false
  -- occursCheck ((a , τ) ∷ eqs) = or (atomOccurs a τ) (occursCheck eqs)



  -- Normal Form and nf helpers
  -- nfHelper : ∀ (n i : ℕ) → 𝕋Sub n → 𝕋Sub n
  -- nfHelper n zero eqs = eqs
  -- nfHelper n (succ zero) eqs = {!   !}
  -- nfHelper n (succ (succ i)) eqs = {!   !}

  -- countXs : ∀ (n : ℕ) → 𝕋=* n → ℕ
  -- countXs m eqs = {!   !}

  -- nf : ∀ (n : ℕ) → 𝕋=* n → 𝕋Sub n
  -- nf n eqs = nfHelper n (countXs n eqs) (lemma1 eqs)


  -- Stuff for handling the decrease in atoms when atomic substitutions are done
  pred : ℕ → ℕ
  pred zero = zero
  pred (succ x) = x

  -- t for target g for gone
  shiftDown : ∀ (n : ℕ) → Fin n → Fin n → Fin n
  shiftDown .(succ n) (here n) (here .n) = here n
  shiftDown .(succ (succ n)) (here (succ n)) (down g) = down (here n)
  shiftDown .(succ _) (down t) (here _) = down t
  shiftDown .(succ _) (down t) (down g) = down (shiftDown _ t g)

  shiftUp𝕋 : ∀ (n : ℕ) → Fin n → 𝕋 n → 𝕋 n
  shiftUp𝕋 n g (α x) = α (shiftUp x g)
  shiftUp𝕋 n g (t ⇒ t₁) = shiftUp𝕋 n g t ⇒ shiftUp𝕋 n g t₁

  liftDown𝕋 : ∀ (n : ℕ) → ¬ (n ≡ 0) → 𝕋 (succ n) → 𝕋 n
  liftDown𝕋 zero ne (α x) = exFalso (ne (refl _))
  liftDown𝕋 (succ n) ne (α x) = α (liftDown (succ n) ne x)
  liftDown𝕋 n ne (τ ⇒ τ₁) = liftDown𝕋 n ne τ ⇒ liftDown𝕋 n ne τ₁

  unDown𝕋Sub : ∀ (n : ℕ) → 𝕋Sub (succ n) → 𝕋Sub n
  unDown𝕋Sub n [] = []
  unDown𝕋Sub zero ((x , τ) ∷ eqs) = []
  unDown𝕋Sub (succ n) ((x , τ) ∷ eqs) = (liftDown (succ n) (λ ()) x , liftDown𝕋 ((succ n)) ((λ ())) τ)
                                        ∷ unDown𝕋Sub (succ n) eqs

  -- ⊢ is \|-
  -- data _⊢_ {𝔸 : Set} (ℰ : 𝕋=* 𝔸) : 𝕋= 𝔸 → Set where
  --   -- ℰ is \McE
  --   ax : ∀ (c : 𝕋= 𝔸) → occurs c ℰ → ℰ ⊢ c
  --   refl : ∀ (t : 𝕋 𝔸) → ℰ ⊢ (con t t)
  --   symm : ∀ (A B : 𝕋 𝔸) → ℰ ⊢ (con B A) → ℰ ⊢ (con A B)
  --   tran : ∀ (A B C : 𝕋 𝔸) → ℰ ⊢ (con A C) → ℰ ⊢ (con C B) → ℰ ⊢ (con A B)
  --   con→ : ∀ (A A' B B' : 𝕋 𝔸) → ℰ ⊢ (con A A') → ℰ ⊢ (con B B') → ℰ ⊢ con (A ⇒ B) (A' ⇒ B')

  test : 𝕋= 3
  test = con
             (α (here 2)) -- lhs
             ((α (here 2)) ⇒ (α (down (here 1)))) -- rhs

  a : Fin 5
  a = (down (down (down (down (here 0)))))

  b : Fin 5
  b = (down (down (down (here 1))))

  c : Fin 5
  c = (down (down (here 2)))

  d : Fin 5
  d = (down (here 3))

  e : Fin 5
  e = here 4

  test2 : 𝕋=* 5
  test2 = con ((α a) ⇒ ((α b) ⇒ (α c)))
              ((α c) ⇒ ((α a) ⇒ ((α d) ⇒ (α e)))) ∷
          con ((α d) ⇒ (α c))
              ((α d) ⇒ (α b)) ∷ []

  -- test3 = {! lemma1 test2  !}

module IntersectionTypes where
  data 𝕋∩ (𝔸 : Set) : Set where
    atom∩ : 𝔸 → 𝕋∩ 𝔸
    fun∩  : 𝕋∩ 𝔸 → 𝕋∩ 𝔸 → 𝕋∩ 𝔸 -- _⇒_
    meet∩ : 𝕋∩ 𝔸 → 𝕋∩ 𝔸 → 𝕋∩ 𝔸 -- _⊓_

  -- data Sub {𝔸 : Set} : 𝕋∩ 𝔸 → 𝕋∩ 𝔸 → Set where
  --   refl : ∀ t → Sub t t
  --   tran : ∀ s t u → Sub s t → Sub t u → Sub s u
  --   lb1 : ∀ s t → Sub s (meet s t)
  --   lb2 : ∀ s t → Sub t (meet s t)
  --   glb : ∀ l s t → Sub l s → Sub l t → Sub l (meet s t)
  --   contr : ∀ {s s' t t'} → Sub s' s → Sub t t' → Sub (fun s t) (fun s' t')
  --   dist : ∀ {a b c} → Sub (meet (fun a b) (fun a c)) (fun a (meet b c))
  --   idem : ∀ {t} → Sub t (meet t t)

  -- mono : ∀ 𝔸 {s s' t t' : 𝕋∩ 𝔸} → Sub s t → Sub s' t' → Sub (meet s s') (meet t t')
   -- mono st st' = {!   !}
-}
