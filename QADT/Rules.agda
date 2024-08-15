-- Groupoid operations
!! : ∀ {n} {a : ADT n}   → Iso a a
!! = refl≃ _
~~ : ∀ {n} {a b : ADT n} → Iso a b → Iso b a
~~ = symm≃
_=!=_ : ∀ {n} {a b c : ADT n} → Iso a b → Iso b c → Iso a c
ab =!= bc = tran≃ ab bc
_~!~_ : ∀ {n} {a b c : ADT n} → Iso b a → Iso c b → Iso a c
ba ~!~ cb = (~~ ba) =!= (~~ cb)
_~!=_ : ∀ {n} {a b c : ADT n} → Iso b a → Iso b c → Iso a c
ba ~!= bc = ~~ ba =!= bc
-- _~!=_ = _=!=_ ∘ ~~
_=!~_ : ∀ {n} {a b c : ADT n} → Iso a b → Iso c b → Iso a c
ab =!~ cb = ab =!= (~~ cb)
-- _=!~_ = _~!~_ ∘ ~~

--- Congruence laws
cong+ :  ∀ {n} {a b c d : ADT n} → Iso a b → Iso c d → Iso (a ⊔ c) (b ⊔ d)
cong+ ab cd = ∨≃ ab cd
cong× :  ∀ {n} {a b c d : ADT n} → Iso a b → Iso c d → Iso (a × c) (b × d)
cong× ab cd = ∧≃ ab cd

cong+= :  ∀ {n} {a b c d e : ADT n} → Iso a b → Iso c d → Iso (b ⊔ d) e → Iso (a ⊔ c) e
cong+= ab cd bde = cong+ ab cd =!= bde
cong×= :  ∀ {n} {a b c d e : ADT n} → Iso a b → Iso c d → Iso (b × d) e → Iso (a × c) e
cong×= ab cd bde = cong× ab cd =!= bde

!+ :  ∀ {n} {a b c : ADT n} → Iso b c → Iso (a ⊔ b) (a ⊔ c)
!+ i = cong+ !! i
+! :  ∀ {n} {a b c : ADT n} → Iso b c → Iso (b ⊔ a) (c ⊔ a)
+! i = cong+ i !!
!× :  ∀ {n} {a b c : ADT n} → Iso b c → Iso (a × b) (a × c)
!× i = cong× !! i
×! :  ∀ {n} {a b c : ADT n} → Iso b c → Iso (b × a) (c × a)
×! i = cong× i !!

!+= :  ∀ {n} {a b c d : ADT n} → Iso b c → Iso (a ⊔ c) d → Iso (a ⊔ b) d
!+= bc acd = !+ bc =!= acd
+!= :  ∀ {n} {a b c d : ADT n} → Iso b c → Iso (c ⊔ a) d → Iso (b ⊔ a) d
+!= bc cad = +! bc =!= cad
×!= :  ∀ {n} {a b c d : ADT n} → Iso b c → Iso (a × c) d → Iso (a × b) d
×!= bc acd = !× bc =!= acd
!×= :  ∀ {n} {a b c d : ADT n} → Iso b c → Iso (c × a) d → Iso (b × a) d
!×= bc cad = ×! bc =!= cad

-- Semiring Axioms
-- Associativity, commutativity, and identity
a× : ∀ {n} {a b c : ADT n} → Iso ((a × b) × c) (a × (b × c))
a× {n} {a} {b} {c} = ~~ (assoc×≃ a b c)
a+ : ∀ {n} {a b c : ADT n} → Iso ((a ⊔ b) ⊔ c) (a ⊔ (b ⊔ c))
a+ {n} {a} {b} {c} = ~~ (assoc⊔≃ a b c)
c× : ∀ {n} {a b : ADT n} → Iso (a × b) (b × a)
c× {n} {a} {b} = comm×≃ a b
c+ : ∀ {n} {a b : ADT n} → Iso (a ⊔ b) (b ⊔ a)
c+ {n} {a} {b} = comm⊔≃ a b
i+l : ∀ {n} {a : ADT n} → Iso (𝟎 ⊔ a) a
i+l = ~~ (id⊔≃ _)
i+r : ∀ {n} {a : ADT n} → Iso (a ⊔ 𝟎) a
i+r = c+ =!~ id⊔≃ _
i×l : ∀ {n} {a : ADT n} → Iso (𝟏 × a) a
i×l {n} {a} = ~~ (id×≃ a)
i×r : ∀ {n} {a : ADT n} → Iso (a × 𝟏) a
i×r {n} {a} = c× =!~ id×≃ a
-- distributivity and annihilation
dl : ∀ {n} {a b c : ADT n} → Iso (a × (b ⊔ c)) (a × b ⊔ a × c)
dl {n} {a} {b} {c} = distrL≃
dr : ∀ {n} {a b c : ADT n} → Iso((a ⊔ b) × c)  (a × c ⊔ b × c)
dr {n} {a} {b} {c} = distrR≃
ar : ∀ {n} {a : ADT n} → Iso (a × 𝟎) 𝟎
ar {n} {a} = annih×≃ a
al : ∀ {n} {a : ADT n} → Iso (𝟎 × a) 𝟎
al {n} {a} = c× =!= (annih×≃ a)

a×= : ∀ {n} {a b c d : ADT n} → Iso (a × (b × c)) d → Iso ((a × b) × c) d
a×= {n} {a} {b} {c} {d} i = assoc×≃ a b c ~!= i
a+= : ∀ {n} {a b c d : ADT n} → Iso (a ⊔ (b ⊔ c)) d → Iso ((a ⊔ b) ⊔ c) d
a+= {n} {a} {b} {c} {d} i = assoc⊔≃ a b c ~!= i
c×= : ∀ {n} {a b c : ADT n} → Iso (b × a) c → Iso (a × b) c
c×= {n} {a} {b} {c} i = comm×≃ b a ~!= i
c+= : ∀ {n} {a b c : ADT n} → Iso (b ⊔ a) c → Iso (a ⊔ b) c
c+= {n} {a} {b} {c} i = comm⊔≃ b a ~!= i
i+l= : ∀ {n} {a b : ADT n} → Iso a b → Iso (𝟎 ⊔ a) b
i+l= {n} {a} {b} i = i+l =!= i
i+r= : ∀ {n} {a b : ADT n} → Iso a b → Iso (a ⊔ 𝟎) b
i+r= {n} {a} {b} i = i+r =!= i
i×l= : ∀ {n} {a b : ADT n} → Iso a b → Iso (𝟏 × a) b
i×l= {n} {a} {b} i = i×l =!= i
i×r= : ∀ {n} {a b : ADT n} → Iso a b → Iso (a × 𝟏) b
i×r= {n} {a} {b} i = i×r =!= i

dl= : ∀ {n} {a b c d : ADT n} → Iso (a × b ⊔ a × c) d → Iso (a × (b ⊔ c)) d
dl= {n} {a} {b} {c} {d} i = distrL≃ =!= i
dr= : ∀ {n} {a b c d : ADT n} → Iso (a × c ⊔ b × c) d → Iso ((a ⊔ b) × c) d
dr= {n} {a} {b} {c} {d} i = distrR≃ =!= i
ar= : ∀ {n} {a b : ADT n} → Iso 𝟎 b → Iso (a × 𝟎) b
ar= {n} {a} {b} i = annih×≃ a =!= i
al= : ∀ {n} {a b : ADT n} → Iso 𝟎 b → Iso (𝟎 × a) b
al= {n} {a} {b} i = c×= (annih×≃ a =!= i)
