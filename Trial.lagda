\begin{code}[hide]
{-# OPTIONS --type-in-type #-}

module Trial where

open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; ∃; Σ-syntax; ∃-syntax)
open import Data.Nat using (ℕ)
open import Data.Unit
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans; sym; cong; cong-app; subst)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; _∎)
\end{code}

In this example, we follow the dependently typed approach initiated by Ranta to
do inference on actual FraCas examples.

Initially, one takes the common nouns as types literally, by saying that the
type of common nouns is actually just a universe, which simply gives the
universe an alias of \term{CN} in Agda, $\llbracket CN \rrbracket := Set$. A man
is common noun, so semantically we just say $\llbracket Man \rrbracket\; {:}\;
\llbracket CN \rrbracket$. And if there is a man John, we simply assert
$\llbracket John \rrbracket\; {:}\; \llbracket Man \rrbracket$.

\begin{code}
CN = Set

postulate
  man : CN
  john : man
\end{code}

In Agda, there is only one sort of predicative universe, \term{Set}. In Coq
there are both impredicative and predicative universes, \term{Prop} and
\term{Set} respectively, of which \term{Type} is a superclass. While one defines
\term{CN := Set} in Coq, the type of impredicative propositions are included in
both \cite{fracoq} and \cite{luoCoq} which is not possible in Agda. It should be
possible to make everything predicative in Coq, but the authors' reasons for
using impredicativity were not explicated in their work. Agda's \term{Prop} are
by default proof irrelevant, whereas one must choose to make Coq's propositions
proof irrelevant. We don't explore more about the implications of foundations
here.

Once one has a the universe of common nouns, each of which may have many
inhabitants, we can ask how they are modified. Intransative Verbs (IVs) like
``walk", can be seen as a type restricted by the collection of things which have
the ability to walk, such as animals. We can see such verbs as functions taking a
specific type of common noun to an arbitrary type : $\llbracket IV \rrbracket\;
{:}\; (\llbracket x \rrbracket\; {:}\; \llbracket CN \rrbracket) \rightarrow
Set$

\begin{code}[hide]
postulate
  animal : Set
\end{code}
\begin{code}
postulate
  walk : animal -> Set
\end{code}
\begin{code}[hide]
postulate
  delegate survey object surgeon human : CN
\end{code}

We can then encode the quantiers, noting that they also return just types the
dependent type \term{P} below is propositional in Coq. These are more arguably
more syntactically pleasing than our Mongtagovian semantics, because they only
bind a noun and a property about that noun, rather than rigidly requiring a verb
phrase and a noun phrase as arguments.

\begin{code}
some : (A : CN) → (P : A → Set) → Set
some A P = Σ[ x ∈ A ] P x

all : (A : CN) → (P : A → Set) → Set
all A P = (x : A) → P x
\end{code}

Wanting to do inference with these examples, we hope to show that if John is a
man and every man walks, then John walks. The difficulty is that walk is a type
over animals, not men, and the relation between men and animals are not yet
covered by our type theory. The theory of coercive subtyping rectifies this and
gives a mechanism of implicity coercing the type of men to the type of animals,
as indeed all men are animals. One can form an order from the subtypes, with
possible infima and suprema, that may transform some abstract ontological model
of the domain into specific ways of using the information to prove inferences.

The coercions in coercive type theory can be approximated by the use of
Agda's instance arguements, which are indicated with \codeword{{{_}}} below.
Nonetheless, Agda doesn't support coercive subtyping as developed by Luo, and
therefore has weaknesses relative to Coq when it comes to eliminating ``coercion
bureaucracy". A coercion is a record type parameterized by two types $x$ and $y$
with one field \term{coe} which is merely a mapping from $x$ to $y$. We can then
compose and apply functions with arguements for which there exists an coercion.

\begin{code}
record Coercion {a} (x y : Set a) : Set a where
  constructor ⌞_⌟
  field coe : x → y
\end{code}
\begin{code}[hide]
open Coercion
\end{code}
\begin{code}
_⊚_ : ∀ {a} {A B C : Set a} → Coercion A B → Coercion B C → Coercion A C
_⊚_ c d = ⌞ (λ x → coe d (coe c x)) ⌟

_$_ : ∀ {a b} {A A′ : Set a} {B : Set b} → (A → B) →
      {{c : Coercion A′ A }} → A′ → B
_$_ f {{c}} a = f (coe c a)

postulate
  ha : human → animal
  mh : man → human
\end{code}

The instance arguements, similar to Haskell's type-classes, allow one to
introduce the coercion information into a context so that one may compute with
these hidden typing relations.

\begin{code}
instance
  hac = ⌞ ha ⌟
  mhc = ⌞ mh ⌟
  mac = mhc ⊚ hac
\end{code}

Once one has defined instances, Agda can infer that \term{walk} is a property of
men, which should be subtypes of animals. We must explictly explicitly declare
this in Agda, unfortunately. A type theory with native support for coercive
subtyping would save significant hassle, although someone with significant
experience using Agda's instance arguements might find a superior way to do this
rather than generating all the instances and coercion applications, possibly
without resorting to metaprogramming. However, once we have the infastracture in
place, we can not only infer basic facts about men, but also about animals and
their relation to men.

\begin{code}[hide]
manwalk : man → Set
manwalk m = walk $ m
\end{code}
\begin{code}
johnwalk = manwalk john
allmanwalk = all man manwalk
somemanwalk = some man manwalk

thm1 : allmanwalk → johnwalk
thm1 ∀mWalk[m] = ∀mWalk[m] john

thm2 : johnwalk → somemanwalk
thm2 jw = john , jw

thm3 : somemanwalk → some animal walk
thm3 (m , walk[m]) = ha (mh m) , walk[m]
\end{code}

To the best of our knowledge, there is no way of coercing types directly, as in,
one cannot simply force the type-checker in \term{thm3} to accept the man
arguement without explicitly requiring the programmer to insert the coercions,
\term{ha (mh m)}. Another issue is that \term{manwalk} and \term{walk} are
explicitly different types, despite the instances allowing Agda to coerce the
fact that a man walks, \codeword{walk[m]}, to an animal walking. We may
reconcile this with more instance arguements, whereby we create a parameterized
record \term{Walks} with a single data point for the walking capacity. One can
then overload walks with all the different entities which can walk, and thereby
not have the ugly \term{manwalks} in the type signature of \term{thm3'}.

\begin{code}
record Walks {a} (A : Set a) : Set a where
  field
    walks : A → Set

open Walks {{...}} public

postulate
  animalsWalk : Walks animal

instance
  animalwalks : Walks animal
  animalwalks = animalsWalk

  humanwalks : Walks human
  humanwalks = record { walks = λ h → Walks.walks animalsWalk $ h}

  manwalks : Walks man
  manwalks = record { walks = λ m → Walks.walks animalsWalk $ m}

thm3' : some man walks  → some human walks
thm3' (m , walk[m]) = mh m , walk[m]
\end{code}

\subsection{Irish Delegate Example}

We finish with the following FraCas example, which includes the ditransative
verb ``finished", the adjective ``Irish", and adverb ``on time", and the
determiner ``the". We include a common noun for \term{object}, of which
\term{survey} and \term{animal} should be subtypes.

\begin{verbatim}
Premise  : Some Irish delegates finished the survey on time.
Question : Did any delegates finish the survey on time?
Answer   : Yes.
\end{verbatim}

\begin{code}[hide]
postulate
  ao : animal → object
  dh : delegate → human
  so : survey → object
instance
  aoc = ⌞ ao ⌟
  dhc = ⌞ dh ⌟
  soc = ⌞ so ⌟
  dac = dhc ⊚ hac --added
  hoc = hac ⊚ aoc
  doc = (dhc ⊚ hac) ⊚ aoc
\end{code}

Semantically, Ditransitive Verbs (DVs) are similair to IVs, they are just binary
functions instead of unary.

$$\llbracket DV \rrbracket\; {:}\; (\llbracket x \rrbracket\; {:}\; \llbracket
CN \rrbracket) \rightarrow (\llbracket y \rrbracket\; {:}\; \llbracket CN
\rrbracket) \rightarrow Set$$

The quality of being on time, which modifies a verb, is intpreted as a function
which takes a common noun $cn$, a type indexed by $cn$ (the verb), and returns a
type which is itself dependent on $cn$. The intuition that one can continue to
modify a verb phrase with more adverbs is immediately obvious based of the type
signature, because it returns the same type as a verb after taking a verb as an
arguement.

$$\llbracket ADV \rrbracket\; {:}\; (\Pi \; x \; {:}\;
\llbracket CN \rrbracket) \rightarrow (\llbracket x \rrbracket\; \rightarrow
Set) \rightarrow (\llbracket x \rrbracket\; \rightarrow Set)$$

The determiner ``the" is simply a way of extracting a member from a given CN.

$$\llbracket the \rrbracket\; {:}\; (\Pi \; x \; {:}\; \llbracket CN \rrbracket) \rightarrow x)$$

Finally, the MTT interpretation of adjectives is definitionally equal to IVs,
$\llbracket ADJ \rrbracket\; {:}\; (\llbracket x \rrbracket\; {:}\; \llbracket
CN \rrbracket) \rightarrow Set$. This does not mean they are semantically at all
similar. Verbs describe what an individual does, whereas adjectives describe
some property of the individual. To apply an adjective $a$ to a member $n$ of
some CN gives a sentence whose meaning is ``$a$ is $n$", whereby the syntactic
``is" is implicit in the semantics.

\begin{code}
postulate
  finish : object → human → Set
  ontime : (A : CN) → (A → Set) → (A → Set)
  the : (A : CN) →  A
  irish : object → Set
\end{code}

Adjectives are generally not meant to return sentences, but other common
nouns. Therefore, we can leverage the dependent product type or records more
generally to describe modified common nouns, whereby the first element $c$ is a
member of some CN and the second member is a proof that $c$ has the property the
adjective expresses. We can therefore see the example of \term{irishdelegate} as
such in Agda:

\begin{code}[hide]
dobj : delegate → object
dobj del = ao (ha (dh del))
\end{code}
\begin{code}
record irishdelegate : CN where
  constructor
    mkIrishdelegate
  field
    c : delegate
    ic : irish $ c
\end{code}

We can follow the same methodology as before, coercing Irish delegates to
delegates axiomatically, and then applying the semantic interpretations of the
words such that the types align correctly - where one sees this actually follows
from an intuitive syntactic presentation.

\begin{code}[hide]
postulate
  idd : irishdelegate → delegate

instance
  iddc = ⌞ idd ⌟
  idh = iddc ⊚ dhc
\end{code}
\begin{code}[hide]
finishTheSurvey : human → Set
finishTheSurvey = finish $ (the survey)

finishedTheSurveyOnTime : delegate → Set
finishedTheSurveyOnTime x = ontime human finishTheSurvey $ x

someDelegateFinishedTheSurveyOnTime : Set
someDelegateFinishedTheSurveyOnTime = some delegate finishedTheSurveyOnTime
\end{code}

Once one builds a parallel infastructure for \term{irishdelegate}, one can then
proceed with the inference. We note that the work has to be doubled because
\term{finishedTheSurveyOnTime} and \term{someDelegateFinishedTheSurveyOnTime}
need to be refactored, renaming \term{delegate} to \term{irishdelegate}. Again,
this inference is just the identity function modulo an explicit \term{idd}
coercion, and implicit coercions allowing \codeword{finishedOnTime} to be cast to
its most general formulation where it is parameterized \term{human}.

\begin{code}[hide]
finishedTheSurveyOnTime' : irishdelegate → Set
finishedTheSurveyOnTime' x = ontime human finishTheSurvey $ x

someIrishDelegateFinishedTheSurveyOnTime : Set
someIrishDelegateFinishedTheSurveyOnTime = some irishdelegate finishedTheSurveyOnTime'
\end{code}
\begin{code}
fc55 :
  someIrishDelegateFinishedTheSurveyOnTime → someDelegateFinishedTheSurveyOnTime
fc55 (irishDelegate , finishedOnTime) = (idd irishDelegate) , finishedOnTime
\end{code}

We note that one could have instead included an extensionality clause for
adjectives and adverbs, wherby one gives additional information so that the
arguement and return types, dependent on some CN $A$, behave coherently with
respect to arbitrary arguements of $A$. One can then derive the adverb by
forgetting the extensionality clause. The inference works out the same.

\begin{code}
postulate
  ADV : (A : CN) (v : A → Set) → Σ[ p ∈ (A → Set) ] ((x : A) → p x → v x)

on_time : (A : CN) (v : A → Set) → A → Set
on_time A v = proj₁ (ADV A v)
\end{code}
\begin{code}[hide]
2finishedTheSurveyOnTime : delegate → Set
2finishedTheSurveyOnTime x = on_time human finishTheSurvey $ x

2finishedTheSurveyOnTime' : irishdelegate → Set
2finishedTheSurveyOnTime' x = on_time human finishTheSurvey $ x

2someIrishDelegateFinishedTheSurveyOnTime : Set
2someIrishDelegateFinishedTheSurveyOnTime = some irishdelegate 2finishedTheSurveyOnTime'

2someDelegateFinishedTheSurveyOnTime : Set
2someDelegateFinishedTheSurveyOnTime = some delegate 2finishedTheSurveyOnTime
\end{code}
\begin{code}
fc55' :
  2someIrishDelegateFinishedTheSurveyOnTime → 2someDelegateFinishedTheSurveyOnTime
fc55' (irishDelegate , finishedOnTime) = (idd irishDelegate) , finishedOnTime
\end{code}

We now investigate the possiblity of gereralizing Irish, as well as integrating
the adjectival work with our previous work generating instance arguements for
``walks".

Unlike walking, which was assumed to apply to all animals, being Irish is a
restriction on the set of objects of some given domain. Therefore we can't just
define the record parametrically for all common nouns, but rather must include
an instance arguement for the coercion. Note this would break the semantic model
if we were to include the type of common noun ``Swede" with a coercion to
humans, because one would be able to make an Irish Swede.

\begin{code}
record irishThing (A : CN) {{c : Coercion A object}} : CN where
  constructor
    mkIrish
  field
    thing : A
    isIrish : irish $ thing
\end{code}
\begin{code}[hide]
open irishThing {{...}} public
\end{code}

Once can now delcare Irish entities using the record for humans, delegates, and
animals, where one can include the coercion arguements explicitly, even though
they are inferrable. Thereafter, we can overload walks even more. Although it is
clear that a lot of this code is boilerplate, the instance declarations must be
nullary, and basic code generation techniques would be needed to scale this to a
larger corpus. The point is, once we know that animals walk, anything subsumed
under that category is straightforward to make ``walkable".

\begin{code}
IrishDelegate = irishThing delegate {{doc}}
IrishHuman = irishThing human {{hoc}}
IrishAnimal = irishThing animal {{aoc}}

instance
  irishAnimalWalks : Walks IrishAnimal
  irishAnimalWalks = record { walks = helper }
    where
      helper : irishThing animal → Set
      helper (mkIrish a isIrish₁) = Walks.walks animalsWalk a

  irishHumanWalks : Walks IrishHuman
  irishHumanWalks = record { walks = helper }
    where
      helper : irishThing human → Set
      helper (mkIrish a isIrish₁) = Walks.walks animalsWalk $ a
\end{code}
\begin{code}[hide]
  irishDelegateWalks : Walks IrishDelegate
  irishDelegateWalks = record { walks = helper }
    where
      helper : irishThing delegate → Set
      helper (mkIrish d isIrish₁) = Walks.walks animalsWalk $ d

thm? : some IrishDelegate walks  → some IrishHuman walks
thm? (mkIrish del isIrish[del] , snd) = (mkIrish (dh del) isIrish[del]) , snd

id : {A : Set} → A → A
id x = x
\end{code}

We can now prove analagous theorems to what we showed earlier, with the
adjectival modification showing as extra data in both the input and output. One
can always forsake the Irish detail and prove a weaker conclusion, as in
\term{thm5}.

\begin{code}
thm4 : some IrishHuman walks → some IrishAnimal walks
thm4 (mkIrish hum isIrish[hum] , snd) = (mkIrish (ha hum) isIrish[hum]) , snd

thm5 : some IrishHuman walks → some animal walks
thm5 (mkIrish hum isIrish[hum] , snd) = (ha hum) , snd
\end{code}

If we now decide to now assume some anonymous \term{irishHuman} exists, and we
prove that human is an animal in \term{irishAnimal}, we can see the fruits of
our labor insofar as the identity funtion works in \term{thm6} despite the
property of our specimin walking being of different types. In \term{thm7}, we
can also then use our anonymous human as a witness for the existential claim
that ``some Irish animal walks".

\begin{code}
postulate
  irishHuman : irishThing human {{hoc}}

instance
  irishAnimal : irishThing animal
  irishAnimal = mkIrish (ha (irishThing.thing irishHuman)) (irishThing.isIrish irishHuman)

thm6 : walks irishAnimal → walks irishHuman
thm6 = id

thm7 : walks irishHuman → some IrishAnimal walks
thm7 x =
  mkIrish (ha (irishThing.thing irishHuman)) ((irishThing.isIrish irishHuman)) , x
\end{code}

One might try to prove something even sillier, like that an Irish animal is an
Irish thing object. Problematically, for the instance checker to be happy, we need to reflexivly coerce an object due to the constraint that a coercion to an object must exist to build and \term{irishThing}. This then makes it so that if we want to 

\begin{code}
postulate
  oo : object → object
instance
  ooc = ⌞ oo ⌟

postulate
  irishHumanisIrishThing : irishThing animal → irishThing object
\end{code}

If one tries to prove this though, it's impossible to complete the program.

\begin{verbatim}
irishHumanisIrishThing (mkIrish thing isIrish) = mkIrish ((ao (thing))) {!!}
\end{verbatim}

Agda computes with the reflexive coercion instance, and therefore we come to the unredeemable goal :

\begin{verbatim}
Goal: irish $ ao thing
Have: irish $ thing
\end{verbatim}

One might think to just add an extra instance to appease Agda :

\begin{code}
instance
  aooc = ⌞ ao ⌟ ⊚ ooc
\end{code}

However, if we were to add an additional instance allowing an animal to be
coerced to an object, this would break the necessary uniqueness of instance
arguements, consistent with the uniqueness of coercions property in type
theories supporting coercive subtyping. This example highlights the limitations
of working with a make-believe subtyping mechanism. While instances give the
Agda programmer the benefits of ad-hoc polymorphism, they are is still not a substitute for a type theory with coercive subtyping built in, especially when it comes to MTT semantics.

\subsection{Addendum on Inductive Types}

\begin{code}
data Men : CN where
  Steve : Men
  Dave : Men

data Human : CN where
  MenHuman : Men → Human

SteveHuman : Human
SteveHuman = MenHuman Steve

-- what if we map this to actual evidence
Walk : Human → Set
Walk (MenHuman Steve) = ⊤
Walk (MenHuman Dave) = ⊤

allmenWalk : all Men λ x → Walk (MenHuman x)
allmenWalk Steve = tt
allmenWalk Dave = tt

data ⊥ : Set where

Walk' : Human → Set
Walk' (MenHuman Steve) = ⊤
Walk' (MenHuman Dave) = ⊥

someManWalks' : some Men λ x → Walk' (MenHuman x)
proj₁ someManWalks' = Steve
proj₂ someManWalks' = tt

-- allmenDontWalk : all Men λ x → Walk' (MenHuman x)
-- allmenDontWalk Steve = tt
-- allmenDontWalk Dave = {!!}

steveWalks : Walk (MenHuman Steve) -- : all Men λ x → Walk (MenHuman x)
steveWalks = tt

someManWalks : some Men λ x → Walk (MenHuman x)
proj₁ someManWalks = Steve
proj₂ someManWalks = tt
\end{code}
