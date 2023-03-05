-- | A suitable foundation for following the book.
--
-- This module will be imported on top of every other.
module Add.Foundation where

open import Agda.Primitive public using (Level;lzero;lsuc)

-- | Equational reasoning.
import Relation.Binary.PropositionalEquality as Eq
open Eq public using (_≡_;refl;sym;trans;cong)
open Eq.≡-Reasoning public using (begin_; _≡⟨⟩_; step-≡;_∎)

-- | Functions.
open import Function public using (id;flip;_∘_;_$_)

-- | Booleans.
open import Data.Bool public using (Bool;true;false;if_then_else_)

-- | Natural numbers.
open import Data.Nat public using (ℕ;zero;suc;_+_;_*_;⌊_/2⌋;⌈_/2⌉)
open import Data.Nat.Properties public using (+-comm;*-comm)

_^_ : ∀ {a} {A : Set a} → (A → A) → ℕ → A → A
_ ^ zero = id
f ^ suc n = f ∘ (f ^ n)

n/2 : ∀ {n : ℕ} → ⌊ n /2⌋ + ⌈ n /2⌉ ≡ n
n/2 {zero} = refl
n/2 {suc zero} = refl
n/2 {suc (suc n)} =
  begin
    ⌊ suc (suc n) /2⌋ + ⌈ suc (suc n) /2⌉
  ≡⟨⟩
    suc ⌊ n /2⌋ + ⌈ suc (suc n) /2⌉
  ≡⟨⟩
    suc ⌊ n /2⌋ + ⌊ suc (suc (suc n)) /2⌋
  ≡⟨⟩
    suc ⌊ n /2⌋ + suc ⌊ suc n /2⌋
  ≡⟨⟩
    suc ⌊ n /2⌋ + suc ⌈ n /2⌉
  ≡⟨⟩
    suc (⌊ n /2⌋ + suc ⌈ n /2⌉)
  ≡⟨ cong suc (+-comm ⌊ n /2⌋ (suc ⌈ n /2⌉)) ⟩
     suc (suc ⌈ n /2⌉ + ⌊ n /2⌋)
  ≡⟨⟩
    suc (suc (⌈ n /2⌉ + ⌊ n /2⌋))
  ≡⟨ cong (suc ∘ suc) (+-comm ⌈ n /2⌉  ⌊ n /2⌋) ⟩
     suc (suc (⌊ n /2⌋ + ⌈ n /2⌉))
  ≡⟨⟩
    suc (suc (⌊ n /2⌋ + ⌈ n /2⌉))
  ≡⟨ cong (suc ∘ suc) n/2 ⟩
     suc (suc n)
  ∎

-- | Float numbers.
open import Data.Float public using (Float;_<ᵇ_)

clamp : Float → Float → Float → Float
clamp a b f =
  if f <ᵇ a then a
  else if b <ᵇ f then b
  else f

-- | Length-indexed vectors.
open import Data.Vec public using (Vec;[];_∷_;_++_;_⊛_;map;zipWith;head;tail;reverse;replicate)

-- Common Haskell-like type classes.
record Monoid {a} (A : Set a) : Set a where
  infixr 6 _<>_
  field
    mempty : A
    _<>_ : A → A → A

open Monoid {{...}} public

record Functor {a} (F : Set a → Set a) : Set (lsuc a) where
  field
    fmap : ∀ {A B : Set a} → (A → B) → F A → F B

open Functor {{...}} public

record Applicative {a} (F : Set a → Set a) : Set (lsuc a) where
  infixl 4 _<∗>_
  field
    pure : ∀ {A : Set a} → A → F A
    _<∗>_ : ∀ {A B : Set a} → F (A → B) → F A → F B

open Applicative {{...}} public
