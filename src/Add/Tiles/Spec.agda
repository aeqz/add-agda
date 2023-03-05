open import Add.Foundation
open import Add.Tiles.Pixels

-- | Specification of a library for generating images.
--
-- An implementation must provide every required term constructor and law proof.
module Add.Tiles.Spec
  {Tile : Set → Set}
  {Color : Set}
  {monoidColor : Monoid Color}
  {rgba : Float → Float → Float → Float → Color}
  {rasterize : ∀ {A} (w h : ℕ) → Tile A → Pixels w h A}
  where

-- | Equality for tiles is defined by observation from the provided rasterize function.
data _≡ₒ_ {A} (t1 t2 : Tile A) : Set where
  obs/eq : (∀ {w h : ℕ} → rasterize w h t1 ≡ rasterize w h t2) → t1 ≡ₒ t2

-- | Tiles that are definitionally equal are also observably equal.
eq/obs : ∀ {A} {t1 t2 : Tile A} → t1 ≡ t2 → t1 ≡ₒ t2
eq/obs pr = obs/eq λ {w} {h} → cong (rasterize w h) pr

-- | Equality properties can be derived from the observational equality definition, but that is not
-- the case for congruence.
reflₒ : ∀ {A} {t : Tile A} → t ≡ₒ t
reflₒ = obs/eq refl

symₒ : ∀ {A} {t1 t2 : Tile A} → t1 ≡ₒ t2 → t2 ≡ₒ t1
symₒ (obs/eq pr) = obs/eq (sym pr)

transₒ : ∀ {A} {t1 t2 t3 : Tile A} → t1 ≡ₒ t2 → t2 ≡ₒ t3 → t1 ≡ₒ t3
transₒ (obs/eq pr1) (obs/eq pr2) = obs/eq (trans pr1 pr2)

-- | The following definitions will help when writing observational equality proofs.
infix 1 beginₒ_
infixr 2 _≡⟨⟩ₒ_ _≡⟨_⟩ₒ_
infix 3 _∎ₒ

beginₒ_ : ∀ {A} {t1 t2 : Tile A} → t1 ≡ₒ t2 → t1 ≡ₒ t2
beginₒ pr = pr

_≡⟨⟩ₒ_ : ∀ {A} (t1 : Tile A) {t2 : Tile A} → t1 ≡ₒ t2 → t1 ≡ₒ t2
_ ≡⟨⟩ₒ pr = pr

_≡⟨_⟩ₒ_ : ∀ {A} (t1 : Tile A) {t2 t3 : Tile A} → t1 ≡ₒ t2 → t2 ≡ₒ t3 → t1 ≡ₒ t3
_ ≡⟨ pr1 ⟩ₒ pr2 = transₒ pr1 pr2

_∎ₒ : ∀ {A} (t : Tile A) → t ≡ₒ t
_ ∎ₒ = reflₒ

-- | The library specification that must be implemented.
record Spec : Set₁ where
  field

    -- | Terminals.
    empty : Tile Color
    color : Float → Float → Float → Float → Tile Color
    empty/color : ∀ {r g b : Float} → color r g b 0.0 ≡ₒ empty
    clamp-channels : ∀ {r g b a : Float} →
      color r g b a ≡ₒ
        color (clamp 0.0 1.0 r) (clamp 0.0 1.0 g) (clamp 0.0 1.0 b) (clamp 0.0 1.0 a)

    -- | Clockwise rotation by 90 degrees.
    cw : ∀ {A} → Tile A → Tile A
    cw/cw/cw/cw : ∀ {A} {t : Tile A} → cw (cw (cw (cw t))) ≡ₒ t
    cw/color : ∀ {r g b a : Float} →
      cw (color r g b a) ≡ₒ (color r g b a)

    -- | Counterclockwise rotation by 90 degrees.
    ccw : ∀ {A} → Tile A → Tile A
    ccw/cw : ∀ {A} {t : Tile A} → ccw (cw t) ≡ₒ t
    cw/ccw : ∀ {A} {t : Tile A} → cw (ccw t) ≡ₒ t

    -- | Mirror horizontally.
    flipH : ∀ {A} → Tile A → Tile A
    flipH/flipH : ∀ {A} {t : Tile A} → flipH (flipH t) ≡ₒ t
    flipH/cw/cw/flipH : ∀ {A} {t : Tile A} → flipH (cw (cw (flipH t))) ≡ₒ cw (cw t)
    x-symmetry : ∀ {A} {t : Tile A} → flipH (cw t) ≡ₒ ccw (flipH t)
    flipH/color : ∀ {r g b a : Float} →
      flipH (color r g b a) ≡ₒ (color r g b a)

    -- | Mirror vertically.
    flipV : ∀ {A} → Tile A → Tile A
    flipV/flipV : ∀ {A} {t : Tile A} → flipV (flipV t) ≡ₒ t
    ccw/flipH/cw : ∀ {A} {t : Tile A} → flipV t ≡ₒ ccw (flipH (cw t))
    flipV/flipH : ∀ {A} {t : Tile A} → flipV (flipH t) ≡ₒ cw (cw t)

    -- | Stick one tile besides another by subdividing the space.
    beside : ∀ {A} → Tile A → Tile A → Tile A
    flipH/beside : ∀ {A} {t1 t2 : Tile A} →
      flipH (beside t1 t2) ≡ₒ beside (flipH t1) (flipH t2)

    -- | Stick one tile above another by subdividing the space.
    above : ∀ {A} → Tile A → Tile A → Tile A
    above/beside/ccw : ∀ {A} {t1 t2 : Tile A} →
      above t1 t2 ≡ₒ cw (beside (ccw t1) (ccw t2))

    above/beside : ∀ {A} {a b c d : Tile A} →
      above (beside a b) (beside c d) ≡ₒ beside (above a c) (above b d)

    -- | Put four tiles together by subdividing the space.
    quad : ∀ {A} → Tile A → Tile A → Tile A → Tile A → Tile A
    above/beside/quad : ∀ {A} {a b c d : Tile A} →
      above (beside a b) (beside c d) ≡ₒ quad a b c d

    -- | Rotate a Tile through a quad.
    swirl : ∀ {A} → Tile A → Tile A
    quad/swirl : ∀ {A} {t : Tile A} →
      quad t (cw t) (ccw t) ((cw ∘ cw) t) ≡ₒ swirl t

    -- | Layer one tile on top of another.
    behind : Tile Color → Tile Color → Tile Color
    opaque : ∀ {t : Tile Color} {r g b : Float} →
      behind t (color r g b 1.0) ≡ₒ color r g b 1.0

    transparent : ∀ {t : Tile Color} {r g b : Float} →
      behind t (color r g b 0.0) ≡ₒ t

    -- | Observational equality congruence.
    congₒ : ∀ {A} (f : Tile A → Tile A) {t1 t2 : Tile A} → t1 ≡ₒ t2 → f t1 ≡ₒ f t2

    -- | Observation.
    --
    -- The previous laws that deal with space (i.e. polymorphic on the Tile type parameter) coud be
    -- trivially satisfied by a unit Tile type, so the following ones add stronger requirements by
    -- relating the algebra with its spatial observation.
    --
    -- We use length-indexed vectors instead of regular linked lists for the ease of working with
    -- the rasterized result in Agda. This also provides the guarantee that the image size is
    -- respected: the following laws could also be trivially satisfied if the rasterize
    -- implementation just ignored its size parameters.
    rasterize/flipV : ∀ {A} {t : Tile A} {w h : ℕ} →
      rasterize w h (flipV t) ≡ reverse (rasterize w h t)

    rasterize/flipH : ∀ {A} {t : Tile A} {w h : ℕ} →
      rasterize w h (flipH t) ≡ map reverse (rasterize w h t)

    rasterize/above : ∀ {A} {t1 t2 : Tile A} {w h : ℕ} →
      rasterize w (⌊ h /2⌋ + ⌈ h /2⌉) (above t1 t2) ≡
        (rasterize w ⌊ h /2⌋ t1) ++
          (rasterize w ⌈ h /2⌉ t2)

    rasterize/beside : ∀ {A} {t1 t2 : Tile A} {w h : ℕ} →
      rasterize (⌊ w /2⌋ + ⌈ w /2⌉) h (beside t1 t2) ≡
        transpose (
          transpose (rasterize ⌊ w /2⌋ h t1) ++
            transpose (rasterize ⌈ w /2⌉ h t2)
        )

    rasterize/cw : ∀ {A} {t : Tile A} {w h : ℕ} →
      rasterize w h (cw t) ≡
        map reverse (transpose (rasterize h w t))

    rasterize/color : ∀ {r g b a : Float} {w h : ℕ} →
      rasterize w h (color r g b a) ≡
        replicate (replicate (rgba r g b a))

    -- | Color-related specification is stated by requiring an applicative instance that matches
    -- the observational counterpart together with the color monoid instance.
    functorTile : Functor Tile
    rasterize/map : ∀ {A B} {f : A → B} {t : Tile A} {w h : ℕ} →
      rasterize w h (fmap {{functorTile}} f t) ≡
        fmap f (rasterize w h t)

    applicativeTile : Applicative Tile
    rasterize/ap : ∀ {A B} {tf : Tile (A → B)} {t : Tile A} {w h : ℕ} →
      rasterize w h (_<∗>_ {{applicativeTile}} tf t) ≡
        (rasterize w h tf <∗> rasterize w h t)

    empty/mempty : empty ≡ₒ
      pure {{applicativeTile}} (mempty {{monoidColor}})

    behind/<> : ∀ {t1 t2 : Tile Color} →
      behind t1 t2 ≡ₒ
        (_<∗>_) {{applicativeTile}} (fmap {{functorTile}} (_<>_ {{monoidColor}}) t1) t2
