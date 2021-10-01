\begin{code}[hide]
{-# OPTIONS --type-in-type #-}

module Mont
          (e : Set) where

open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂; ∃; Σ-syntax; ∃-syntax)

data Falsity : Set where
\end{code}

The common nouns as tyes maxim is interpreted into Agda by saying there is a 

\begin{code}[hide]
t = Set
\end{code}

\begin{code}[hide]
VP = e -> t
NP = VP -> t  --- (e -> t) -> t
CN = e -> t

properNoun : e -> NP
properNoun x vp = vp x

-- Definition VP:= forall (subjectClass : CN), object -> Prop. (* subject *)
-- Definition all:= fun A:CN=> fun P:A->Prop=> forall x:A, P(x).

every : CN -> VP -> t -- uttery useless as a proposition (this useful as a PROGRAM)
every cn vp = (x : e) -> cn x -> vp x

some : CN -> VP -> t
some cn vp = Σ[ x ∈ e ] (cn x × vp x)

-- a : CN -> VP -> t

module Example
         (walk : VP)
         (man : CN)
         (JOHN : e)
         (johnMan : man JOHN)
         (p : every man walk)
       where

  john : NP
  john = λ vp → vp JOHN

  johnWalksProof : john walk
  johnWalksProof = p JOHN johnMan -- p JOHN johnMan

  someManWalks : some man walk -- some man walk
  -- someManWalks = JOHN , johnMan , p JOHN johnMan
  someManWalks = JOHN , johnMan , johnWalksProof

----irish delegate

-- Definition IntersectiveA := object -> Prop.
-- Parameter irish_A : IntersectiveA .
-- Definition N:= object->Prop.
-- Parameter on_time_Adv : VeridicalAdv .
-- Definition VeridicalAdv :=
-- { adv : (object -> Prop) -> (object -> Prop)
-- & prod (forall (x : object) (v : object -> Prop), (adv v) x -> v x)
-- (forall (v w : object -> Prop), (forall x, v x -> w x) -> forall (x : object), adv v x -> adv w x)
-- }.jqj

-- intersectiveA = object → Set

  -- N = object → Set
-- V2 = object → object → Set

-- veridicalAdv : Set
-- veridicalAdv = Σ[ adv ∈ ((object → Set) → (object → Set)) ]
--   (( x : object) (v : object → Set) → (adv v) x → v x) ×
--   ((v w : object → Set) → (∀ x → v x → w x) → ∀ (x : object) → adv v x → adv w x)

-- postulate
--   survey_N : N
--   delegate_N : N
--   irishA : intersectiveA
--   on_time_Adv : veridicalAdv
--   finish_V2 : V2
--   environment : (object -> Set) -> object

-- asdf = λ (y : object) → finish_V2 (environment survey_N) y × survey_N (environment survey_N)

-- helper1 = Σ[ x ∈ object ] ((irishA x) × delegate_N x) ×  {!asdf !}

-- H : exists x : object,
-- (irish_A x /\ delegate_N x) /\
-- (let (a, _) := on_time_Adv in a)
-- (fun y : object =>
-- finish_V2 (environment survey_N) y /\
-- survey_N (environment survey_N)) x


-- veridicalAdv : {!!}
-- veridicalAdv = Σ {!!} {!!}

-- Σ[ adv ∈ (object → Set) → (object → Set)]
-- intersectiveA = object → Set

\end{code}

