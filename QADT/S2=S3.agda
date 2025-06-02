open import Logic

module QADT.S2=S3 where

data S2 : Set where
  ε2 : S2
  a : S2 → S2
  b : S2 → S2

data S3 : Set where
  ε3 : S3
  x : S3 → S3
  y : S3 → S3
  z : S3 → S3

S2→2S3 : S2 → S3 ⊔ S3
S2→2S3 ε2 = in1 ε3
S2→2S3 (a ε2) = in2 ε3
S2→2S3 (a (a s)) with S2→2S3 s
... | in1 t = in1 (x t)
... | in2 t = in1 (y t)
S2→2S3 (a (b s)) with S2→2S3 s
... | in1 t = in1 (z t)
... | in2 t = in2 (x t)
S2→2S3 (b ε2) = in2 (z ε3)
S2→2S3 (b (a s)) with S2→2S3 s
... | in1 t = in2 (y t)
... | in2 t = in2 (z (x t) )
S2→2S3 (b (b s)) with S2→2S3 s
... | in1 t = in2 (z (y t) )
... | in2 t = in2 (z (z t) )

2S3→S2 : S3 ⊔ S3 → S2
2S3→S2 (in1 ε3) = ε2
2S3→S2 (in1 (x s)) = a (a (2S3→S2 (in1 s)))
2S3→S2 (in1 (y s)) = a (a (2S3→S2 (in2 s)))
2S3→S2 (in1 (z s)) = a (b (2S3→S2 (in1 s)))
2S3→S2 (in2 ε3) = a ε2
2S3→S2 (in2 (x s)) = a (b (2S3→S2 (in2 s)))
2S3→S2 (in2 (y s)) = b (a (2S3→S2 (in1 s) ) )
2S3→S2 (in2 (z ε3)) = b ε2
2S3→S2 (in2 (z (x s))) = b (a (2S3→S2 (in2 s)) )
2S3→S2 (in2 (z (y s))) = b (b (2S3→S2 (in1 s)) )
2S3→S2 (in2 (z (z s))) = b (b (2S3→S2 (in2 s)) )

S2→2S3→S2 : ∀ x → 2S3→S2 (S2→2S3 x) ≡ x
S2→2S3→S2 ε2 = refl
S2→2S3→S2 (a ε2) = refl
S2→2S3→S2 (a (a s)) with S2→2S3 s
... | t = {!   !}
S2→2S3→S2 (a (b s)) = {!   !}
S2→2S3→S2 (b s) = {!   !}
