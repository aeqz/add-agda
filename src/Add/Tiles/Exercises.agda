open import Add.Foundation
open import Add.Tiles.Pixels

-- | Exercises over the library specification.
--
-- It assumes that an implementation and some example terminals are given via module parameters.
module Add.Tiles.Exercises
  {Tile : Set → Set}
  {Color}
  {monoidColor : Monoid Color}
  {rgba : Float → Float → Float → Float → Color}
  {rasterize : ∀ {A} (w h : ℕ) → Tile A → Pixels w h A} where
  open import Add.Tiles.Spec {Tile} {Color} {monoidColor} {rgba} {rasterize}
  module WithImpl {Impl : Spec} {haskell church : Tile Color} where
    open Spec Impl

    --| Exercise: derive the following property from the laws.
    _ : ∀ {A} (t : Tile A) → ccw t ≡ₒ cw (cw (cw t))

    -- Solution:
    _ = λ t →
      beginₒ
        ccw t
      ≡⟨ congₒ ccw (symₒ cw/cw/cw/cw) ⟩ₒ
        ccw (cw (cw (cw (cw t))))
      ≡⟨ ccw/cw ⟩ₒ
        cw (cw (cw t))
      ∎ₒ

    --| Exercise: derive the following property from the laws.
    _ : ∀ {A} (n : ℕ) (t : Tile A) → (flipH ∘ (cw ^ (2 * n)) ∘ flipH) t ≡ₒ (cw ^ (2 * n)) t

    -- Solution:
    _ = induction
      where
        lemma = λ n t →
          begin
            (cw ^ (2 * suc n)) t
          ≡⟨ cong (λ n → (cw ^ n) t) (*-comm 2 (suc n)) ⟩
            (cw ^ (suc n * 2)) t
          ≡⟨⟩
            (cw ^ (suc (suc (n * 2)))) t
          ≡⟨⟩
            cw (cw ((cw ^ (n * 2)) t))
          ≡⟨ cong (λ n → cw (cw ((cw ^ n) t))) (*-comm n 2) ⟩
             cw (cw ((cw ^ (2 * n)) t))
          ∎

        induction = λ where
          zero _ → flipH/flipH
          (suc n) t →
            beginₒ
              flipH ((cw ^ (2 * (suc n))) (flipH t))
            ≡⟨ eq/obs (cong flipH (lemma n (flipH t))) ⟩ₒ
              flipH (cw (cw ((cw ^ (2 * n)) (flipH t))))
            ≡⟨ congₒ (flipH ∘ cw ∘ cw) (symₒ flipH/flipH) ⟩ₒ
              flipH (cw (cw (flipH (flipH ((cw ^ (2 * n)) (flipH t))))))
            ≡⟨ flipH/cw/cw/flipH ⟩ₒ
              cw (cw (flipH ((cw ^ (2 * n)) (flipH t))))
            ≡⟨ congₒ (cw ∘ cw) (induction n t) ⟩ₒ
              cw (cw ((cw ^ (2 * n)) t))
            ≡⟨ eq/obs (sym (lemma n t)) ⟩ₒ
              (cw ^ (2 * (suc n))) t
            ∎ₒ

    -- | Exercise: recreate a tile avoiding to use flipV.
    _ : Tile Color

    -- Solution:
    _ = (ccw ∘ flipH ∘ cw) haskell

    -- | Exercise: derive the following law from the others.
    _ : ∀ {A} (t : Tile A) → flipV (flipV t) ≡ₒ t

    -- Solution:
    _ = λ t →
      beginₒ
        flipV (flipV t)
      ≡⟨ ccw/flipH/cw ⟩ₒ
        ccw (flipH (cw (flipV t)))
      ≡⟨ congₒ (ccw ∘ flipH ∘ cw) ccw/flipH/cw ⟩ₒ
        ccw (flipH (cw (ccw (flipH (cw t)))))
      ≡⟨ congₒ (ccw ∘ flipH) cw/ccw ⟩ₒ
        ccw (flipH (flipH (cw t)))
      ≡⟨ congₒ ccw flipH/flipH ⟩ₒ
        ccw (cw t)
      ≡⟨ ccw/cw ⟩ₒ
        t
      ∎ₒ

    -- | Exercise: derive the following property from the laws.
    _ : ∀ {A} (t : Tile A) → flipV (flipH t) ≡ₒ cw (cw t)

    -- Solution:
    _ = λ t →
      beginₒ
        flipV (flipH t)
      ≡⟨ ccw/flipH/cw ⟩ₒ
        ccw (flipH (cw (flipH t)))
      ≡⟨ symₒ x-symmetry ⟩ₒ
        flipH (cw (cw (flipH t)))
      ≡⟨ flipH/cw/cw/flipH ⟩ₒ
        cw (cw t)
      ∎ₒ

    -- | Exercise: derive the following property from the laws in two different ways.
    _ : ∀ {A} (t1 t2 : Tile A) -> flipH (flipH (beside t1 t2)) ≡ₒ beside t1 t2

    -- Solution:
    _ = λ t1 t2 ->
      beginₒ
        flipH (flipH (beside t1 t2))
      ≡⟨ flipH/flipH ⟩ₒ
        beside t1 t2
      ∎ₒ

    _ : ∀ {A} (t1 t2 : Tile A) -> flipH (flipH (beside t1 t2)) ≡ₒ beside t1 t2
    _ = λ t1 t2 ->
      beginₒ
        flipH (flipH (beside t1 t2))
      ≡⟨ congₒ flipH flipH/beside ⟩ₒ
        flipH (beside (flipH t1) (flipH t2))
      ≡⟨ flipH/beside ⟩ₒ
        beside (flipH (flipH t1)) (flipH (flipH t2))
      ≡⟨ congₒ (λ t -> beside t (flipH (flipH t2))) flipH/flipH ⟩ₒ
        beside t1 (flipH (flipH t2))
      ≡⟨ congₒ (beside t1) flipH/flipH ⟩ₒ
        beside t1 t2
      ∎ₒ

    -- | Exercise: recreate a tile avoiding to use above.
    _ : Tile Color

    -- Solution:
    _ = cw (beside (ccw church) (ccw haskell))
