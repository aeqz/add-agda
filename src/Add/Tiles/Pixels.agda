module Add.Tiles.Pixels where

open import Add.Foundation

Pixels : ∀ {a} → ℕ → ℕ → Set a → Set a
Pixels w h = flip Vec h ∘ flip Vec w

transpose : ∀ {a} {A : Set a} {w h : ℕ} → Pixels w h A → Pixels h w A
transpose {w = zero} {h = zero} _ = []
transpose {w = zero} {h = suc _} _ = []
transpose {w = suc _} {h = zero} _ = replicate []
transpose {w = suc w} {h = suc h} vvs = map head vvs ∷ transpose (map tail vvs)

instance
  functorPixels : ∀ {a} {w h : ℕ} → Functor {a} (Pixels w h)
  fmap {{functorPixels}} = map ∘ map

instance
  applicativePixels : ∀ {a} {w h : ℕ} → Applicative {a} (Pixels w h)
  pure {{applicativePixels}} = replicate ∘ replicate
  _<∗>_ {{applicativePixels}} = zipWith (_⊛_)
