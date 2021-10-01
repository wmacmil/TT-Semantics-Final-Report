\begin{code}[hide]
module MS
          (e : Set) where
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; ∃; Σ-syntax; ∃-syntax)
-- example from
-- https://pdfs.semanticscholar.org/f94b/268c1c91dd1de22cf978a7ea03f8860cbe9d.pdf
\end{code}

We assign Agda types to the categories, knowing that entites are postulated as a
type.

\begin{code}
t = Set
S = t
NP = (e → t) → t
VP = NP → t
V = NP → NP → t
Det = (e → t) → (e → t) → t
N = e → t
\end{code}

Agda's equality symbol can be seen as the semantic interpretation,
$\llbracket\_\rrbracket$, of our grammar's categories, whereby we are here
working with a shallow embedding. One could instead elect to define both the GF
embedding as a record and Montague's intentional type theory as an inductive
dataype, whereby the semantics could then be given explictly. This degree of
formality is not necessary for our simple examples, but doing so would allow one
to prove metaproperties about the GF embedding, and should certainly be
investigated.
The two GF functions for forming sentences and verb phrases can
then be given the following Agda interpreations.

\begin{code}
sentence : NP → VP → S
sentence S V = V S

verbp : V → NP → VP
verbp V O S = V S O
\end{code}

\begin{code}[hide]
nounp : Det → N → NP
nounp D N = D N
\end{code}

We axiomatically include primitive lexical items of \term{love}, an entity
\term{j} for John, and \term{man} and \term{woman} as nouns, so that we can
articulate logically interesting facts about them. As our encoding of noun
phrases takes an arguement, we can define the syntactic notion \term{John} by
applying an arguement function to \term{j}.

\begin{code}
postulate
  love : e → e → t
  j : e
  man : N
  woman : N
  johnMan : man j

John : NP
John P = P j
\end{code}

We define our quantifiers using the Agda's dependent $\Pi$ and $\Sigma$ which
make up the core of any dependently typed language.

\begin{code}
Every : Det
Every P Q = (x : e) → P x → Q x

A : Det
A cn vp = Σ[ x ∈ e ] (cn x × vp x)
\end{code}

We also notice that we may define the dintransative verb loves two ways, which
are obtained commuting the NP arguements.

\begin{code}
loves loves' : V
loves O S = O (λ x → S λ y → love x y)    -- (i)
loves' O S = S (λ x → O λ y → love x y)   -- (ii)
\end{code}

We can then observe two different semantic interpretations of the phrase ``every
man loves a woman".

\begin{code}
everyManLovesAWoman = sentence (Every man) (verbp loves (A woman))   -- (i)
everyManLovesAWoman' = sentence (Every man) (verbp loves' (A woman)) -- (ii)
\end{code}

The two interpretations of ``loves" which differ as to where the respective
arguements are applied in the program, manifest in the semantic unambiguity of
whether there is one or possibly many women are in the context of consideration.
With Agda's help in normalizing these two types, we can see this ambiguity is
reflected in whether the outermost quantifier is universal or existential. Note
he product has been desugared to a non-dependent Σ-type.

\begin{code}
(i)  = (x : e) → man x → Σ e (λ x₁ → Σ (woman x₁) (λ x₂ → love x x₁))
(ii) = Σ e (λ x → Σ (woman x) (λ x₁ → (x₂ : e) → man x₂ → love x x₂))
\end{code}
\begin{code}[hide]
someManLovesAWoman = sentence (A man) (verbp loves (A woman))
someManLovesAWoman' = sentence (A man) (verbp loves' (A woman))
johnLovesAWoman = sentence John (verbp loves (A woman))
johnLovesAWoman' = sentence John (verbp loves' (A woman))
\end{code}

%\paragraph{Agda Fracas Example}

Let's articulate natural language inference to a hypothetical mathematician.

\textbf{Theorem}:
  If every man loves a woman, then John loves a woman.

\textbf{Proof}:
Assume that John is a person who is human. Knowing that every man
  loves a woman, we can apply this knowledge to John, who is a man, and identity a
woman that John loves. Specifically, this woman John loves is a person, evidence
that person is a woman, and evidence that John loves that person.

We also show this argument in Agda, noting that we comment out the more verbose
but informative information that goes into who a woman John loves really is. We
explicitly include the data of the proof so as to see how the overly elaborate
natural language arguement manifests in code. 

\begin{code}
-- (i)
jlaw : everyManLovesAWoman → johnLovesAWoman
jlaw emlaw = womanJonLoves -- thePerson ,  thePersonIsWoman  , jonLovesThePerson
  where
    womanJonLoves : Σ e (λ z → Σ (woman z) (λ _ → love j z))
    womanJonLoves = emlaw j johnMan
    -- thePerson : e
    -- thePerson = proj₁ womanJonLoves
    -- thePersonIsWoman : woman (thePerson)
    -- thePersonIsWoman = proj₁ (proj₂ womanJonLoves)
    -- jonLovesThePerson : love j thePerson
    -- jonLovesThePerson = proj₂ (proj₂ womanJonLoves)
\end{code}

We note this is the first interpretation of love. In the alternative
presentation we see that if there is a woman every man loves, that our semantic
theory interprets her as a person, the evidence that person is a woman, and the
evidence that every man loves that person. Since every man loves that person,
John certainly does as well.

\begin{code}
-- (ii)
jlaw' : everyManLovesAWoman' → johnLovesAWoman'
jlaw' (person , personIsWoman , everyManLovesPerson ) =
  person , personIsWoman , everyManLovesPerson j johnMan
\end{code}

Finally, we can know that some man loves a woman by virtue of the fact that John
loves a woman and John is a man. We note that the proofs just articulate the
data in different order.

\begin{code}
smlw : johnLovesAWoman → someManLovesAWoman
smlw (w , wWoman , jlovesw ) = j , johnMan , w , wWoman , jlovesw
smlw' : johnLovesAWoman' → someManLovesAWoman'
smlw' (w , wWoman , jlovesw ) = w , wWoman , j , johnMan , jlovesw
\end{code}

While the Montagovian approach is historically interesting and still incredibly
significant in linguistic semantics, the interpretation of various parts of
speech and their means of syntactic combination doesn't always seem to be intuitively reflected in the types. Dependent type theories, or MTTs, which have a more expressive type system, gives us a means of more intuitively encoding the meanings.

This use of a ``fancier" type theory for NL semantics can be viewed as analagous
to a preference of inductively defined numbers over Von Neumman or Chruch
encodings. While the latter constructions are interesting and important
historically, they aren't easy to work with and don't match our intuition.
Nonetheless, the different encodings of numbers in different foundations can be
proven sound and complete with respect to each other, so that one can rest
assured that the intuitive notion of number is captured by all of them.

Unlike in formal mathematics, however, to capturing semantics in different
foundational theories suggests no way of proving soundness or completeness with
respect to the interpretation of different phrases, as the set of semantically
fluent utterances are not inductively defined. One may instead take a pragmatic
approach and see the difficulties arising when doing inference with respect to
different type theories.
