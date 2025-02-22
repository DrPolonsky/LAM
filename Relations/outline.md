The main theme is to generalize ARS from Terese to provide an "entry point"
into more advanced things.

So we spent some time figuring out the fundamentals --- Well-foundedness (termination)
properties, confluence properties, etc. --- with the view to isolating
the minimal decidability requirements for constructive abstract rewriting theory.

In particular, this led us to think about different notions of well-foundedness.

The constructive approach also suggested a few new ARS-theoretic properties that lead to slightly more general formulations of classical results.
We illustrate them in the formalization of Newman's lemma and an
abstract termination criterion given in [Terese,Thm.1.2.3(ii)?].
(Attributed there to [???].)
Points to consider.
* We may as well organize the paper and the "talk" simultaneously.
* What would we like to communicate?
  - Formalizing ARS theory
  - Include (counter)examples from infinitary rewriting ---
    decidability fails, termination fails, confluence.... also fails.
  - Figure out relationships between well-foundedness; construct
    counterexamples; outline proofs of (constructive) non-provability of (classical) implications.
* decMin is to dec (isNF) as dec is to wdec.
* FB, $dec(R)$ implies $\lnot\lnot \exists y. R x y \to \exists y. R x y$
  (Otherwise, you need a MP for the carrier.)
* Answer to Wellfounded preamble question no.5:
  - In the formula of being R-phi-minimal, namely:           
    ```is_-_-minimal_ φ x = x ∈ φ × (∀ y → y ∈ φ → R y x → ⊥)```  
we should proceed to replace ⊥ with (C x), where C : A -> Set is a predicate
on the carrier.  This would give rise to the concept of being (R,phi,C)-minimal,
asserting that the given input x is in phi, and every one-step R-reduct of x
still in phi is also included in C.

### Zoom Meeting on Jan 17
Outstanding questions
- SR and RP implies CR without decidability? (No.)
- SN and UN implies CR (or WCR?) without decidability? (No.)
- isWFacc implies isWFmin0 requires to either decide P or deal with a branching set of paths to R-minimal elements
- isWFacc implies isWFmin1 with no additional assumptions?
- isWFmin, isWFmin0, isWFmin1 --- relations to isWFacc and isWFseq

### February 1 notes
- DNS for lists established (``finitary demorgan'')
- As a corollary, isWFmin0- implies isWFacc- for finitely branching relations
- The simplest instance of isWFmin is KT, the constantly true predicate.
  isWFacc to isWFmin is therefore saying that SN implies WN
  But this can only be true with decMin
  Therefore, this is a valid assumption to try to prove the converse
- isWFmin0 to isWFseq requires Markov's principle for equality
  (for finding an element in the sequence equal to a given one)
  This will need decidability of equality
- (Actually, it's probably equivalent to it, because you can define a sequence
that is almost constant in order to determine whether the two elements are equal)

### Feb 3
- Abstract due next Monday
- Paper due two weeks from now
- need to add discussion of 1.2.3 to the report

### Feb 8
- CoInd and minimality
- FB and CoInd
- CoInd and q5

### Feb 9
- The difference between sequential and general minimality principles is that
the former implies there is no countable (actually, omega-indexed) counterexample,
the latter implies no counterexample to accessibility can exist.

### Feb 11
- Include proof sketch of the impossibility of WFseq -> WFacc
- Decide between "recurrent", "minimal", "terminal", "normal", etc.
- WFseq- implies WFacc- requires coind for accessibility

### Feb 14

{- 2024.06.28.
  Questions to investigate.
  1. Does ¬¬ R-accessible x → R-accessible x ?
     (This appears not to be the case.
      However, the implication should be valid for all ``definable'' P.)
  2. Does ¬¬WFacc R → WFacc R ?
  3. Does WFacc- R → ¬¬WFacc R ?
    (This is DNS for accessibility.)
  4. What's the role of ¬¬-closedness in the implication WFmin→WFind ?
  5. How should the "minimality" concept be changed to be useful?
  6. Does WFseq → WFmin- ?
  -}
  {- 2024.07.25.
    ¬¬-closure of well-foundedness properties should be provable for an
    inductively defined collection of predicates -}
