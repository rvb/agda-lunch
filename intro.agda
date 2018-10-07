-- An introduction to Agda

-- What is Agda?

-- - A functional language
--   - Total
--   - Dependently-typed

-- What is Agda for?
--   - Programs & proofs in the same language
--   - Arbitrary expressions in types

-- Today
--   - Truth, falsehood and constructive logic
--   - Totality and consistency
--   - Natural numbers and lists
--   - Vectors: Length-indexed lists
--   - Operations on vectors
--   - Equality in Agda
--   - Functors, applicatives and monads
--   - Vectors as a monad

-- What is a 'proof' in Agda?
-- In Agda, we exploit the Curry-Howard correspondence, so:

-- An expression of type A is a proof of the proposition that A represents

-- The interpretation of a type as a proposition is not encoded in Agda, it exists in our heads.

-- Encoding truth and falsehood.

-- The proposition that is always true does not need proving.
-- Its proofs contain no data, so there is exactly one.
-- In Agda, this can be encoded as a record with no fields.

record True : Set where --Agda records have a type declaration. Set is the type of types*
  constructor <> --Record constructors may be given explicitly.

--We can show that the proposition True is True by giving a value of type True.

trueHolds : True
trueHolds = <> --This is a 'hole', a part of the program that is not yet finished.

-- If truth is a proposition that is always true and requires no data to prove it, what is falsehood?
-- A false proposition should have no proofs, as, after all, it is not true.
-- This means that it must be encoded as a type with no values.
-- We encode this as a data type with no constructors.

data False : Set where
  -- Normally, we would list constructors here. False has none, as it has no values.

--It is impossible to create a proof of False

falseHolds : False
falseHolds = {!!} --This hole cannot be filled in.

--A proof of "A and B" is a pair of proofs, one for A and one for B

--We define pairs as a record type.
record _×_ (A B : Set) : Set where -- In _×_, the underscores indicate where arguments go.
  constructor _,_ --The same here, ',' is an infix binary operator
  field
    fst : A
    snd : B

--For instance, we can prove "B and A" from "A and B".
--This implication is encoded as a function type.

andCommutes : ∀ {A B} → A × B → B × A --Arguments in { .. } are implicit. Using ∀, we ask Agda to infer their types
andCommutes (a , b) = b , a

--A proof of "A or B" is either a proof of A, or a proof of B.
--This is a union type:
data Or (A B : Set) : Set where
  --We define a data type by stating its constructors and their types:
  inl : A → Or A B
  inr : B → Or A B 

--A and (B or C) implies (A and B) or (A and C):
andOrDistribute : ∀ {A B C} → A × (Or B C) → Or (A × B) (A × C)
andOrDistribute (a , inl b) = inl (a , b)
andOrDistribute (a , inr c) = inr (a , c)

--Now that we can encode and and or, how do we know we can't prove nonsense?
--Proving nonsense would mean being able to give a value in type False.
--We can show that having a value of this type means we can prove absolutely anything:
falseImpliesEverything : ∀ (A : Set) → False → A
falseImpliesEverything toShow ()

--We are used to thinking of an expression of type A
--as something that, as long as it finishes, will give us an A.
--What happens if an expression goes into an infinite loop?
-- meaningless : False
-- meaningless = meaningless

--Agda is a total language, which rejects your program if it cannot show it will terminate.
--In particular, meaningless is rejected.
--Therefore, in Agda, an expression of type A is guaranteed to give you an A.
--There are no expressions of type False, so you cannot derive a contradiction in Agda, it is consistent as a logic.

--In addition to a logic, Agda is also a functional programming language.
--A common data type is the natural numbers, defined inductively below.
data Nat : Set where
  Z : Nat
  S : Nat → Nat

--We can define addition of natural numbers:
_+_ : Nat → Nat → Nat
Z + y = y
S x + y = S (x + y)


--Lists have a similar structure to natural numbers, but contain elements:
data List (A : Set) : Set where
  [] : List A
  _::_ : A → List A → List A

--We can append lists:
_++_ : ∀ {A} → List A → List A → List A
[] ++ ys = ys
(x :: xs) ++ ys = x :: (xs ++ ys)

--We can also apply a function to every element:

lmap : ∀ {A B} → (A → B) → List A → List B
lmap f [] = []
lmap f (x :: xs) = f x :: lmap f xs

--Unfortunately, the list type is not particularly informative.
--In fact, both ++ and lmap could always return empty lists and would typecheck just fine.
--What can we do to fix this?
--In F#, we'd write unit tests and hope we've covered every case.
--In Agda, we can instead make our types stronger, so they provide better guarantees.

--By including the length of a list in its type, we can guarantee that map preserves lengths,
--and append returns a vector of the right length.
data Vec (A : Set) : Nat → Set where
  [] : Vec A Z
  _::_ : ∀ {n} → A → Vec A n → Vec A (S n)

--Append for vectors:
--The return type encodes that the length of the result is the sum of the input lengths.
--We can use any expression in a type, there is nothing special about +.
_++V_ : ∀ {m n A} → Vec A m → Vec A n → Vec A (m + n)
[] ++V ys = ys
(x :: xs) ++V ys = x :: (xs ++V ys)

--Map for vectors:
--We encode that map preserves the length of the input vector.
map : ∀ {n} {A B : Set} → (A → B) → Vec A n → Vec B n
map f [] = []
map f (x :: xs) = f x :: map f xs

--In addition to preserving lengths, map has some other properties:
--For any vector x:
-- map id x = x
-- map (f << g) x = map f (map g x)

--The proposition that two values x and y are equal is written in Agda as
--x ≡ y.
--Its only constructor is refl, which constructs proofs of type x ≡ x.

open import Agda.Builtin.Equality

--As an example of working with ≡, we can prove that it is transitive:
≡trans : {A : Set} → {x y z : A} → x ≡ y → y ≡ z → x ≡ z
≡trans refl y≡z = y≡z

--Identity function.
id : {A : Set} → A → A
id x = x

--A slightly harder example:
--Proving the functor laws for vector map.
mapId : ∀ {A n} → (x : Vec A n) → map id x ≡ x
mapId [] = refl
mapId (x :: xs) rewrite mapId xs = refl

_>>_ : {A B C : Set} → (A → B) → (B → C) → (A → C)
(f >> g) x = g (f x)

_<<_ : {A B C : Set} → (B → C) → (A → B) → (A → C)
(g << f) x = g (f x)

mapCmp : ∀ {A B C n} → (f : A → B) → (g : B → C) → (x : Vec A n) → map g (map f x) ≡ map (f >> g) x
mapCmp f g [] = refl
mapCmp f g (x :: xs) rewrite mapCmp f g xs = refl

--Vectors as an applicative:
--We require pure and apply:
pure : ∀{n A} → A → Vec A n
pure {Z} x = []
pure {S n} x = x :: pure x

_<*>_ : ∀{n A B} → Vec (A → B) n → Vec A n → Vec B n
[] <*> [] = []
(f :: fs) <*> (x :: xs) = f x :: (fs <*> xs)

--Identity
identityApp : ∀ {n A} → (x : Vec A n) → pure id <*> x ≡ x
identityApp [] = refl
identityApp (x :: xs) rewrite identityApp xs = refl

--Homomorphism
homomorphismApp : ∀ {n A B} → (x : A) → (f : A → B) → pure {n = n} f <*> pure x ≡ pure (f x)
homomorphismApp {Z} x f = refl
homomorphismApp {S n} x f rewrite homomorphismApp {n} x f = refl

interchangeApp : ∀ {n A B} → (u : Vec (A → B) n) → (y : A) → u <*> pure y ≡ pure (λ f → f y) <*> u
interchangeApp [] y = refl
interchangeApp (u :: us) y rewrite interchangeApp us y = refl

compositionApp : ∀ {n A B C} → (u : Vec (B → C) n) → (v : Vec (A → B) n) → (w : Vec A n) →  (((pure _<<_ <*> u) <*> v) <*> w) ≡ u <*> (v <*> w) 
compositionApp [] [] [] = refl
compositionApp (u :: us) (v :: vs) (w :: ws) rewrite compositionApp us vs ws = refl

--We require tail to define join:
tail : ∀{n A} → Vec A (S n) → Vec A n
tail (x :: xs) = xs

--Finally, we require join to make Vec a monad:
join : ∀ {n A} → Vec (Vec A n) n → Vec A n
join [] = []
join ((x :: xs) :: xss) = x :: join (map tail xss)

--Lemma required to prove the monad laws below.
mapTailHelper : ∀ {n A} (x : A) (xs : Vec A n) (m : Nat) → map tail (pure {m} (x :: xs)) ≡ pure xs
mapTailHelper _ _ Z = refl
mapTailHelper x xs (S m) rewrite mapTailHelper x xs m = refl

joinPureId : ∀{n A} → (xs : Vec A n) → join (pure xs) ≡ xs
joinPureId {Z} [] = refl
joinPureId {(S n)} (x :: xs) rewrite mapTailHelper x xs n | joinPureId xs = refl

joinMapPureId : ∀{n A} → (xs : Vec A n) → join (map pure xs) ≡ xs
joinMapPureId [] = refl
joinMapPureId {S n} (x :: xs) rewrite mapCmp pure (tail {n}) xs | joinMapPureId xs = refl

tailNaturality : ∀ {n} {A B : Set} → (f : A → B) → (xs : Vec A (S n)) → map f (tail xs) ≡ tail (map f xs)
tailNaturality f (x :: xs) = refl

postulate extensionality : {A B : Set} → {f g : A → B} → ((x : A) → f x ≡ g x) → f ≡ g

joinNaturality : ∀ {n A B} → (f : A → B) → (xs : Vec (Vec A n) n) → map f (join xs) ≡ join (map (map f) xs)
joinNaturality f [] = refl
joinNaturality {S n} f ((x :: xs) :: xss)
  rewrite mapCmp (map f) tail xss
    | joinNaturality f (map tail xss)
    | mapCmp tail (map f) xss
    | extensionality (tailNaturality {n} f) = refl

joinTail : ∀ {n A} → (xss : Vec (Vec A (S n)) (S n)) → tail (join xss) ≡ join (map tail (tail xss))
joinTail ((x :: xs) :: xss) = refl

joinJoinLaw : ∀ {n A} → (xs : Vec (Vec (Vec A n) n) n) → join (join xs) ≡ join (map join xs)
joinJoinLaw [] = refl
joinJoinLaw {S n} {A} (((x :: xs) :: xss) :: xsss)
  rewrite mapCmp join tail xsss
    | joinNaturality tail (map tail xsss)
    | mapCmp tail (map tail) xsss
    | joinJoinLaw (map (tail >> map tail) xsss)
    | mapCmp (tail >> map tail) join xsss
    | extensionality (λ x → joinTail {n} {A} x) = refl
